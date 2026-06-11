//! General-purpose VOLE-in-the-head proof.
//!
//! Much of the documentation refers to notation in "the paper"; this is referencing
//! Baum et al.[^vole].
//!
//! [^vole]: Carsten Baum, Lennart Braun, Cyprien Delpech de Saint Guilhem, Michael Klooß,
//! Emmanuela Orsini, Lawrence Roy, and Peter Scholl. [Publicly Verifiable Zero-Knowledge and
//! Post-Quantum Signatures from VOLE-in-the-head](https://eprint.iacr.org/2023/996). 2023.
//!
use mac_n_cheese_sieve_parser::WireId;
use merlin::Transcript;
use rand::{CryptoRng, RngCore};
use rayon::iter::*;
use std::{iter::zip, marker::PhantomData};
use swanky_error::{ErrorKind, Result, bail};
use swanky_field::{FiniteField, FiniteRing, IsSubFieldOf};
use swanky_field_binary::{F2, F8b, F128b};
use swanky_sieve_ir_api::{CircuitExecuter, HigherDegreeCircuitExecuter};

use crate::{circuit::Circuit, vole::DecommitmentSerde};
use crate::{
    commitment_polynomial::CommitmentPolynomial,
    parameters::{REPETITION_PARAM, SECURITY_PARAM, VOLE_SIZE_PARAM},
    proof::{
        prover_preparer::ProverPreparer, prover_traverser::ProverTraverser,
        transcript::ChiGenerator,
    },
    vole::{AsSecretBytes, RandomVoleP, RandomVoleV},
};

/// Number of base VOLE correlations composed into one full-field VOLE over [`F128b`].
const MASK_VOLE_SIZE: usize = REPETITION_PARAM * VOLE_SIZE_PARAM;

use self::verifier_traverser::VerifierTraverser;

mod prover_preparer;
mod prover_traverser;
mod transcript;
mod verifier_traverser;

/// Zero-knowledge proof of knowledge of a circuit.
#[derive(Debug, Clone)]
pub struct Proof<Vole: RandomVoleP, VoleV: RandomVoleV> {
    /// Commitment to the extended witness ($`d`$ in the paper).
    witness_commitment: Vec<F2>,
    /// Aggregated commitment to the degree-1 term coefficients for each gate in the circuit
    /// ($`\tilde a`$ in the paper).
    degree_1_commitment: F128b,
    /// Aggregated commitment to the assert_zero gates.
    assert_zero_commitment: F128b,
    /// Coefficients of the masked higher degree constraint polynomial ($`\pi(t)`$ in Fig. 3 of
    /// the better-conversions paper).
    ///
    /// If the circuit has higher degree constraints whose maximum degree is $`d`$, this contains
    /// the $`d`$ coefficients $`[\pi_0, ..., \pi_{d-1}]`$ (the degree-$`d`$ coefficient is zero
    /// for an honest prover and omitted). It is empty if the circuit has no higher degree
    /// constraints.
    higher_degree_commitment: Vec<F128b>,
    /// Challenge generated to decommit to the VOLEs after committing to the degree coefficients.
    decommitment_challenge: [u8; SECURITY_PARAM / 8],
    /// Partial decommitment of the VOLEs.
    partial_decommitment: VoleV::Decommitment,

    // This ties the proof to the VOLE implementation used to create it.
    vole: PhantomData<Vole>,
}

impl<VoleP, VoleV> Proof<VoleP, VoleV>
where
    VoleP: RandomVoleP,
    VoleV: RandomVoleV<Decommitment = VoleP::Decommitment>,
{
    /// TODO: docstring
    pub fn proof_size_estimate(&self) -> usize {
        // This is only a part of the proof size, it does not include the partial decommitment part because this is abstracted with traits.
        let witness_commitment_bytes = self.witness_commitment.len() / 8;
        let degree_1_commitment_bytes = 16;
        let higher_degree_commitment_bytes = self.higher_degree_commitment.len() * 16;
        let decommitment_challenge_bytes = SECURITY_PARAM / 8;

        let partial_decommitment_size = self.partial_decommitment.proof_size_estimate();

        witness_commitment_bytes
            + degree_1_commitment_bytes
            + higher_degree_commitment_bytes
            + decommitment_challenge_bytes
            + partial_decommitment_size
    }

    /// Create a proof of knowledge of a witness that satisfies the given circuit.
    pub fn prove_with_circuit<R>(
        circuit: &Circuit,
        transcript: &mut Transcript,
        rng: &mut R,
    ) -> Result<Self>
    where
        R: CryptoRng + RngCore,
    {
        let (gates, private_input, max_wire_id) = circuit.to_interpreter();
        Self::prove(gates, private_input, max_wire_id, transcript, rng)
    }

    /// Create a proof of knowledge of a witness that satisfies the given circuit.
    pub fn prove<R, C>(
        circuit: C,
        private_input: &[F2],
        max_wire_id: WireId,
        transcript: &mut Transcript,
        rng: &mut R,
    ) -> Result<Self>
    // TODO: Get rid of max_wire_id
    where
        R: CryptoRng + RngCore,
        C: HigherDegreeCircuitExecuter<F2, F128b>, // Can't do higher order trait bounds... See https://github.com/rust-lang/rust/issues/108185#issuecomment-2819123578
    {
        let t = std::time::Instant::now();
        let mut transcript = transcript::Transcript::from(transcript);
        log::info!("0: load transcript: {:?}", t.elapsed());

        // Evaluate the circuit in the clear to get the full witness and all wire values
        let t = std::time::Instant::now();
        let mut circuit_preparer = ProverPreparer::new(private_input, max_wire_id)?;
        circuit.execute(&mut circuit_preparer)?;

        // Batching higher degree constraints of maximum degree d requires d - 1 full-field mask
        // VOLEs (sigma_j in Fig. 3 of the better-conversions paper), each composed from
        // `MASK_VOLE_SIZE` base VOLEs. These are provisioned after the witness VOLEs.
        let mask_vole_count =
            circuit_preparer.max_higher_degree().saturating_sub(1) * MASK_VOLE_SIZE;

        let (witness, _challenge_count) = circuit_preparer.into_parts();
        log::info!("1: circuit preparer: {:?}", t.elapsed());

        let t = std::time::Instant::now();
        // Update transcript with general public information
        transcript.append_public_values();

        // Get a set of (l + mask count + SECURITY_PARAM) random VOLEs
        let (voles, _vole_challenge) = VoleP::create(
            witness.len() + mask_vole_count,
            transcript.as_mut(),
            &witness,
            rng,
        );
        log::info!("2: VoleP::create: {:?}", t.elapsed());

        let t = std::time::Instant::now();
        // Commit to extended witness (`d` in the paper)
        let witness_commitment: Vec<F2> = voles
            .witness_mask()
            .iter()
            .zip(witness.iter())
            .map(|(u, w)| w - u)
            .collect();
        log::info!("3: witness_commitment: {:?}", t.elapsed());

        let t = std::time::Instant::now();
        // TODO:
        // The hashing of u~ and hV is done in the Vole generation. In order to do it here we have to change the interface of VoleP to expose these fields.
        // Add u~ from the proof into the transcript here instead of in the vole part.
        // Add hV (from VOLE) to the transcript here instead of in the vole part.

        // Add witness commitment to the transcript and generate a challenge for each polynomial
        transcript.append_witness_commitment(witness_commitment.as_slice());
        let chi_challenge = transcript.extract_challenge();

        // Traverse circuit to compute the coefficients for the degree 0 and 1 terms for each
        // gate / polynomial (`A_i0` and `A_i1` in the paper) and start to aggregate these with
        // the challenges.
        let mut circuit_traverser = ProverTraverser::new(witness, chi_challenge, voles)?;
        circuit.execute(&mut circuit_traverser)?;
        let (
            degree_0_aggregation,
            degree_1_aggregation,
            assert_zero_commitment,
            higher_degree_aggregate,
            voles,
        ) = circuit_traverser.into_parts()?;

        log::info!("4: circuit_traverser.into_parts: {:?}", t.elapsed());

        let t = std::time::Instant::now();
        // Compute masks for the aggregated coefficients (`v*`, `u*` in the paper)
        let degree_0_mask = combine(voles.aggregate_commitment_masks());
        let degree_1_mask = combine(voles.aggregate_commitment_values());

        // Finish computing aggregated responses (`a~`, `b~` in the paper)
        let degree_0_commitment = degree_0_aggregation + degree_0_mask;
        let degree_1_commitment = degree_1_aggregation + degree_1_mask;

        // Mask the higher degree aggregate with the reserved mask VOLEs to form pi(t). The mask
        // VOLEs start right after the witness VOLEs (there is one witness commitment per witness
        // VOLE).
        let higher_degree_commitment = mask_higher_degree_aggregate(
            &higher_degree_aggregate,
            &voles,
            witness_commitment.len(),
        )?;

        // Add aggregated responses to transcript
        transcript.append_polynomial_commitments(
            &degree_0_commitment,
            &degree_1_commitment,
            &assert_zero_commitment,
        );
        transcript.append_higher_degree_commitment(&higher_degree_commitment);
        let decommitment_challenge = transcript.extract_decommitment_challenge();

        // Decommit the VOLEs
        let partial_decommitment = voles.decommit(&decommitment_challenge);

        log::info!("5: decommit: {:?}", t.elapsed());
        // Form the proof
        Ok(Self {
            witness_commitment,
            degree_1_commitment,
            assert_zero_commitment,
            higher_degree_commitment,
            decommitment_challenge,
            partial_decommitment,
            vole: PhantomData,
        })
    }

    /// This makes sure the proof is correctly formed e.g. everything is the right length.
    fn validate_proof(&self, voles: &VoleV) -> Result<()> {
        // There should be one witness commitment for every element in the extended witness, plus
        // `MASK_VOLE_SIZE` VOLEs for each higher degree mask polynomial (the higher degree
        // commitment has max-degree-many coefficients, which require one fewer masks).
        // The proof and the decommitted VOLEs should agree on what this size is.
        let mask_vole_count =
            self.higher_degree_commitment.len().saturating_sub(1) * MASK_VOLE_SIZE;
        if self.witness_commitment.len() + mask_vole_count != voles.extended_witness_length() {
            bail!(
                ErrorKind::OtherError,
                "Invalid proof: Did not commit to the same number of witnesses {} (plus {} higher degree mask VOLEs) as there are VOLEs {}",
                self.witness_commitment.len(),
                mask_vole_count,
                voles.extended_witness_length()
            )
        }

        Ok(())
    }

    /// Verify the proof for the given Circuit.
    ///
    pub fn verify_with_circuit(
        &self,
        circuit: &Circuit,
        transcript: &mut Transcript,
    ) -> Result<()> {
        let (gates, _private_input, _max_wire_id) = circuit.to_interpreter();
        self.verify(gates, transcript)
    }

    /// Verify the proof.
    ///
    pub fn verify<C>(&self, circuit: C, transcript: &mut Transcript) -> Result<()>
    where
        C: CircuitExecuter<F2>, // Can't do higher order trait bounds... See https://github.com/rust-lang/rust/issues/108185#issuecomment-2819123578
    {
        let mut transcript = transcript::Transcript::from(transcript);
        transcript.append_public_values();

        let t = std::time::Instant::now();
        // Reconstruct VOLEs and update transcript with any necessary components.
        let reconstructed_voles = VoleV::reconstruct(
            &self.partial_decommitment,
            &self.decommitment_challenge,
            transcript.as_mut(),
        );
        self.validate_proof(&reconstructed_voles)?;
        log::info!("1: VoleV::reconstruct: {:?}", t.elapsed());

        // Add `d` to transcript and generate challenges for each polynomial
        let t = std::time::Instant::now();
        transcript.append_witness_commitment(self.witness_commitment.as_slice());
        log::info!("2: append_witness_commitment {:?}", t.elapsed());

        let t = std::time::Instant::now();
        // TODO:
        // The hashing of u~ and hV is done in the Vole generation. In order to do it here we have to change the interface of VoleP to expose these fields.
        // Add u~ from the proof into the transcript here instead of in the vole part.
        // Add hV (from VOLE) to the transcript here instead of in the vole part.

        // TODO: Should we be doing something with these challenges?
        let chi_challenge = transcript.extract_challenge();
        log::info!("3: extract_challenges {:?}", t.elapsed());

        // Compute masked witnesses Q' = Q[..l] + d * Delta
        let t = std::time::Instant::now();
        let verifier_key = reconstructed_voles.verifier_key_array();
        let d_delta = self
            .witness_commitment
            .par_iter()
            .map(|e| {
                let witness_com = F8b::from(*e);
                verifier_key.map(|key| witness_com * key)
            })
            .collect::<Vec<_>>();

        let witness_voles = reconstructed_voles.witness_voles();
        let masked_witnesses: Vec<F128b> = witness_voles
            .par_iter()
            .zip(d_delta.par_iter())
            .map(|(qs, dds)| {
                let masked_witness: [F8b; 16] = zip(qs, dds)
                    .map(|(q, dd)| q + dd)
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                F8b::form_superfield(&masked_witness.into())
            })
            .collect();
        log::info!("4: reconstructed voles with masks {:?}", t.elapsed());

        let t = std::time::Instant::now();
        // Combine mask VOLEs to get q*
        let validation_mask = combine(reconstructed_voles.mask_voles());

        // Run circuit traversal and get the aggregate value (part of c~)
        let mut verifier_traverser = VerifierTraverser::new(
            chi_challenge,
            reconstructed_voles.verifier_key(),
            masked_witnesses,
        )?;
        circuit.execute(&mut verifier_traverser)?;
        let (validation_aggregate, aggregate_assert_zero) = verifier_traverser.into_parts()?;
        log::info!("5: circuit traverser {:?}", t.elapsed());

        let t = std::time::Instant::now();
        // Finally, compute c~ = aggregate + q*
        let validation = validation_aggregate + validation_mask;
        let degree_0_commitment =
            validation - self.degree_1_commitment * reconstructed_voles.verifier_key();

        // Add aggregated responses to the transcript
        transcript.append_polynomial_commitments(
            &degree_0_commitment,
            &self.degree_1_commitment,
            &self.assert_zero_commitment,
        );
        // TODO: Actually check the higher degree commitment (pi(Delta) = q in Fig. 3 of the
        // better-conversions paper). This requires a `HigherDegreeBackend` implementation for
        // `VerifierTraverser`; until then, circuits with higher degree constraints cannot be
        // verified, but the prover's transcript must still be mirrored here.
        transcript.append_higher_degree_commitment(&self.higher_degree_commitment);

        // Get the VOLE decommitment challenge and make sure it's valid
        let decommitment_challenge = transcript.extract_decommitment_challenge();
        if self.decommitment_challenge != decommitment_challenge {
            bail!(
                ErrorKind::OtherError,
                "Verification failed: VOLE challenge did not match expected value"
            );
        }

        // Assert zero check
        if self.assert_zero_commitment != aggregate_assert_zero {
            bail!(
                ErrorKind::OtherError,
                "Verification failed: Assert zero check failed"
            );
        }

        log::info!("6: last check {:?}", t.elapsed());

        Ok(())
    }
}

/// Mask the higher degree aggregate to form the coefficients of $`\pi(t)`$ (Fig. 3 in the
/// better-conversions paper).
///
/// Computes $$`\pi(t) = \text{aggregate}(t) + \sum_{j=1}^{d-1} t^{j-1} \cdot \sigma_j(t)`$$,
/// where each mask $`\sigma_j(t) = w_j + s_j \cdot t`$ is a full-field VOLE composed from the
/// `MASK_VOLE_SIZE` base VOLE correlations starting at index `witness_len + (j - 1) *
/// MASK_VOLE_SIZE`.
///
/// Returns the $`d`$ coefficients $`[\pi_0, ..., \pi_{d-1}]`$. The degree-$`d`$ coefficient of
/// the aggregate is the (zero) committed value and is omitted, so $`\pi(t)`$ has degree at most
/// $`d - 1`$. The result is empty if there were no higher degree constraints.
fn mask_higher_degree_aggregate<VoleP: RandomVoleP>(
    aggregate: &CommitmentPolynomial<F2, F128b>,
    voles: &VoleP,
    witness_len: usize,
) -> Result<Vec<F128b>> {
    debug_assert_eq!(aggregate.highest_degree(), F2::ZERO);
    let mut pi = aggregate.lower_coefficients().to_vec();

    for j in 0..aggregate.degree().saturating_sub(1) {
        // Compose the mask sigma_j(t) = w_j + s_j * t from base VOLE correlations, the same way
        // the degree 0 and 1 commitment masks are composed in `prove()`.
        let base = witness_len + j * MASK_VOLE_SIZE;
        let mut values = [F128b::ZERO; MASK_VOLE_SIZE];
        let mut masks = [F128b::ZERO; MASK_VOLE_SIZE];
        for k in 0..MASK_VOLE_SIZE {
            values[k] = voles.witness_mask()[base + k].into();
            masks[k] = voles.vole_mask(base + k)?;
        }
        let s_j = combine(values);
        let w_j = combine(masks);

        // Add t^(j-1) * sigma_j(t); `j` here is 0-based while the paper's is 1-based.
        pi[j] += w_j;
        pi[j + 1] += s_j;
    }

    Ok(pi)
}

/// Convert a list of field elements into a single 128-bit value.
///
/// Specifically, we compute
/// $` \sum_{i = 0}^{128} v_i X^i`$,
/// where $`X`$ is [`F128b::GENERATOR`], the generator for the field.
fn combine(values: [F128b; 128]) -> F128b {
    // Start with `X^0 = 1`
    let mut power = F128b::ONE;
    let mut acc = F128b::ZERO;

    for vi in values {
        acc += vi * power;
        power *= F128b::GENERATOR;
    }
    acc
}

/// The secret material for the prover is the extended witness.
impl AsSecretBytes for Vec<F2> {
    fn as_bytes(&self) -> Vec<u8> {
        self.iter().map(|b| (*b).into()).collect()
    }
}

#[cfg(test)]
mod tests {
    use merlin::Transcript;
    use rand::thread_rng;
    use std::io::Write;
    use std::{fs::File, io::Cursor};
    use swanky_error::{ErrorKind, Result, WrapErr};
    use swanky_field::FiniteRing;
    use swanky_field_binary::{F2, F128b};
    use swanky_sieve_ir_api::{CircuitResult, HigherDegreeBackend, HigherDegreeCircuitExecuter};
    use tempfile::tempdir;

    use crate::{
        circuit::load_circuit_prover,
        vole::insecure::{InsecureCommitments, InsecureVole},
    };

    use super::{Circuit, Proof};

    // Get a fresh transcript
    fn transcript() -> Transcript {
        Transcript::new(b"basic happy test transcript")
    }

    // Create a proof for the given circuit and input.
    fn create_proof(
        circuit_bytes: &'static str,
        private_input_bytes: &'static str,
    ) -> Result<(Result<Proof<InsecureVole, InsecureCommitments>>, Circuit)> {
        let mut circuit_cursor = Cursor::new(circuit_bytes.as_bytes());

        let dir = tempdir().unwrap();
        let private_input_path = dir.path().join("schmivitz_private_inputs");
        let mut private_input = File::create(private_input_path.clone()).unwrap();
        writeln!(private_input, "{private_input_bytes}").unwrap();

        let circuit = load_circuit_prover(&mut circuit_cursor, &private_input_path)?;
        let rng = &mut thread_rng();

        let proof = Proof::<InsecureVole, InsecureCommitments>::prove_with_circuit::<_>(
            &circuit,
            &mut transcript(),
            rng,
        );
        Ok((proof, circuit))
    }

    #[test]
    fn prove_doesnt_explode() -> Result<()> {
        let mini_circuit_bytes = "version 2.0.0;
            circuit;
            @type field 2;
            @begin
              $0 <- @private(0);
              $1 <- @mul(0: $0, $0);
              $2 <- @add(0: $0, $0);
            @end ";
        let private_input_bytes = "version 2.0.0;
            private_input;
            @type field 2;
            @begin
                < 1 >;
            @end";

        let (proof, mini_circuit) = create_proof(mini_circuit_bytes, private_input_bytes)?;
        assert!(
            proof?
                .verify_with_circuit(&mini_circuit, &mut transcript())
                .is_ok()
        );

        Ok(())
    }

    const SMALL_CIRCUIT: &str = "version 2.0.0;
        circuit;
        @type field 2;
        @begin
          $0 ... $4 <- @private(0);
          $5 <- @add(0: $0, $0);
          $6 <- @add(0: $0, $1);
          $7 <- @add(0: $0, $2);
          $8 <- @add(0: $0, $3);
          $9 <- @add(0: $0, $4);
          $10 <- @mul(0: $0, $5);
          $11 <- @mul(0: $0, $6);
          $12 <- @mul(0: $0, $7);
          $13 <- @mul(0: $0, $8);
          $14 <- @mul(0: $0, $9);
        @end ";

    #[test]
    fn prove_works_on_slightly_larger_circuit() -> Result<()> {
        let private_input_bytes = "version 2.0.0;
            private_input;
            @type field 2;
            @begin
                < 1 >;
                < 1 >;
                < 1 >;
                < 0 >;
                < 0 >;
            @end ";

        let (proof, small_circuit) = create_proof(SMALL_CIRCUIT, private_input_bytes)?;
        assert!(
            proof?
                .verify_with_circuit(&small_circuit, &mut transcript())
                .is_ok()
        );

        Ok(())
    }

    #[test]
    fn prover_and_verifier_must_input_the_same_transcript() -> Result<()> {
        let private_input_bytes = "version 2.0.0;
        private_input;
        @type field 2;
        @begin
            < 1 >;
            < 0 >;
            < 1 >;
            < 0 >;
            < 1 >;
        @end ";

        // This uses the output of `transcript()` as-is to prove. This should work
        let (proof, small_circuit) = create_proof(SMALL_CIRCUIT, private_input_bytes)?;
        assert!(proof.is_ok());

        // If we use a different transcript to verify, it'll fail
        let transcript = &mut transcript();
        transcript.append_message(b"I am but a simple verifier", b"trying to be secure");
        assert!(
            proof?
                .verify_with_circuit(&small_circuit, transcript)
                .is_err()
        );

        Ok(())
    }

    /// A hand-written circuit with a degree-4 constraint x0 * x1 * x2 * x3 == 0.
    struct HigherDegreeCircuit;

    impl HigherDegreeCircuitExecuter<F2, F128b> for HigherDegreeCircuit {
        fn execute<B: HigherDegreeBackend<F2, F128b>>(&self, backend: &mut B) -> CircuitResult<()> {
            let inputs = backend.inputs_private::<4>()?;
            backend.assert_zero_higher_degree(&inputs, |x| {
                let x01 = B::h_mul(&x[0], &x[1]).unwrap();
                let x23 = B::h_mul(&x[2], &x[3]).unwrap();
                B::h_mul(&x01, &x23).unwrap()
            });
            Ok(())
        }
    }

    #[test]
    fn prove_handles_higher_degree_constraints() -> Result<()> {
        // Witness satisfying x0 * x1 * x2 * x3 == 0.
        let private_input = [F2::ONE, F2::ONE, F2::ZERO, F2::ONE];
        let rng = &mut thread_rng();

        let proof = Proof::<InsecureVole, InsecureCommitments>::prove(
            HigherDegreeCircuit,
            &private_input,
            4,
            &mut transcript(),
            rng,
        )?;

        // The maximum constraint degree is 4, so pi(t) has degree at most 3 and is sent as 4
        // coefficients.
        assert_eq!(proof.higher_degree_commitment.len(), 4);

        Ok(())
    }

    #[test]
    fn proof_requires_exact_number_of_challenges() -> Result<()> {
        // Create a valid proof
        let small_circuit_bytes = "version 2.0.0;
            circuit;
            @type field 2;
            @begin
              $0 ... $4 <- @private(0);
              $5 <- @add(0: $0, $0);
              $6 <- @add(0: $0, $1);
              $7 <- @add(0: $0, $2);
              $8 <- @add(0: $0, $3);
              $9 <- @add(0: $0, $4);
              $10 <- @mul(0: $0, $5);
              $11 <- @mul(0: $0, $6);
              $12 <- @mul(0: $0, $7);
              $13 <- @mul(0: $0, $8);
              $14 <- @mul(0: $0, $9);
            @end ";
        let small_circuit_text = &mut Cursor::new(small_circuit_bytes.as_bytes());

        let dir = tempdir().wrap_err(
            ErrorKind::FilesystemError,
            "Failed to create a temporary directory.",
        )?;
        let private_input_path = dir.path().join("basic_happy_small_test_path");
        let mut private_input = File::create(private_input_path.clone()).wrap_err(
            ErrorKind::FilesystemError,
            "Failed to create private input file.",
        )?;
        let private_input_bytes = "version 2.0.0;
            private_input;
            @type field 2;
            @begin
                < 1 >;
                < 0 >;
                < 1 >;
                < 0 >;
                < 1 >;
            @end ";
        writeln!(private_input, "{private_input_bytes}").wrap_err(
            ErrorKind::FilesystemError,
            "Failed to write private input bytes to file.",
        )?;

        let small_circuit = load_circuit_prover(small_circuit_text, &private_input_path)?;
        let rng = &mut thread_rng();

        let proof = Proof::<InsecureVole, InsecureCommitments>::prove_with_circuit::<_>(
            &small_circuit,
            &mut transcript(),
            rng,
        )?;

        assert!(
            proof
                .verify_with_circuit(&small_circuit, &mut transcript())
                .is_ok()
        );

        Ok(())
    }
}
