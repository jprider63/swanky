use swanky_error::{ErrorKind, Result, bail};
use swanky_field::FiniteRing;
use swanky_field_binary::F2;
use swanky_field_binary::F128b;
use swanky_sieve_ir_api::{CircuitResult, FieldBackend, HigherDegreeBackend};

use crate::polynomial_constraint::power;
use crate::proof::ChiGenerator;

/// A [`VerifierTraverser`] allows the verifier to execute the gate-by-gate evaluation portion of
/// the VOLE-in-the-head verification protocol.
///
/// The primary steps in circuit traversal are assigning masked witnesses to each
/// wire (either using provided witnesses from the proof or evaluating expected witnesses for
/// linear gates) and computing the aggregate value used to verify the proof.
pub(crate) struct VerifierTraverser {
    /// Fiat-Shamir challenges as powers of chi. There should be one for each polynomial (e.g. non-linear gate) and assert zero.
    chi_challenge: ChiGenerator,

    /// Verifier's chosen random VOLE key ($`\Delta`$ in the paper).
    verifier_key: F128b,

    /// The masked witness commitments ($`\bf q'`$ in the paper).
    ///
    /// There should be one of these for each extended witness.
    /// Note that these are a function of the random VOLEs correlated with the witness, the
    /// commitment to the witness itself, and the verifier's VOLE key.
    masked_witnesses: Vec<F128b>,

    /// Count of how many of the provided masked witnesses have been assigned.
    assigned_witness_count: usize,

    /// Partial aggregation of the value $`\tilde c`$ from the protocol.
    ///
    /// After traversal, this should have the value
    /// $`\sum_{i \in [t]} \chi_i \cdot c_i(\Delta)`$.
    aggregate: F128b,

    /// Partial aggregation of the assert zero check.
    /// TODO: Add this to the specification and reference it.
    aggregate_assert_zero: F128b,

    /// Challenge-weighted sums of the higher degree constraint evaluations, grouped by
    /// constraint degree.
    ///
    /// After traversal, index $`d_i`$ holds $$`\sum_{i : \deg = d_i} \chi_i \cdot \gamma_i`$$
    /// where $`\gamma_i = \rho_i(\Delta)`$ is the verifier's homomorphic evaluation of the
    /// $`i`$th higher degree constraint (Fig. 3 in the better-conversions paper). The vector has
    /// one entry per degree up to the maximum constraint degree (and is empty if the circuit has
    /// no higher degree constraints); the degree alignment $`\Delta^{d - d_i}`$ is applied in
    /// [`Proof::verify()`](crate::proof::Proof::verify) once the maximum degree $`d`$ is known.
    higher_degree_aggregates: Vec<F128b>,
}

impl VerifierTraverser {
    pub(crate) fn new(
        chi_challenge: ChiGenerator,
        verifier_key: F128b,
        masked_witnesses: Vec<F128b>,
    ) -> Result<Self> {
        // TODO: Add additional asserts here?
        Ok(Self {
            chi_challenge,
            verifier_key,
            masked_witnesses,
            assigned_witness_count: 0,
            aggregate: F128b::ZERO,
            aggregate_assert_zero: F128b::ZERO,
            higher_degree_aggregates: Vec::new(),
        })
    }

    /// Assign a wire ID to the next unused masked witness and get the corresponding challenge.
    ///
    /// This should be called with the destination [`WireId`] for each non-linear gate.
    /// It should _not_ be used with linear gates! Use [`Self::save_computed_masked_witness()`] to
    /// assign a specific witness value to a linear gate.
    ///
    /// Fails if there aren't enough unused witnesses or if the [`WireId`] is already assigned to
    /// a masked witness.
    fn next_masked_witness(&mut self) -> Result<F128b> {
        let next_index = self.assigned_witness_count;
        self.assigned_witness_count += 1;

        // These two checks should be equivalent because we checked at construction that the
        // challenge list is exactly the extended witness length.
        if next_index >= self.masked_witnesses.len() {
            bail!(
                ErrorKind::OtherError,
                "Bad input: needed at least {} masked witnesses, but only got {}",
                self.assigned_witness_count,
                self.masked_witnesses.len()
            )
        }

        Ok(self.masked_witnesses[next_index])
    }

    /// Decomposes into the aggregate components (a partial construction of `c~` and the higher
    /// degree aggregates) that were built during full circuit traversal.
    ///
    /// This will fail if there were unused challenges or masked witnesses.
    pub(crate) fn into_parts(self) -> Result<(F128b, F128b, Vec<F128b>)> {
        if self.assigned_witness_count != self.masked_witnesses.len() {
            bail!(
                ErrorKind::OtherError,
                "Proof contained more masked witnesses than it needed! Had {}, used {}",
                self.masked_witnesses.len(),
                self.assigned_witness_count
            );
        }
        Ok((
            self.aggregate,
            self.aggregate_assert_zero,
            self.higher_degree_aggregates,
        ))
    }
}

impl FieldBackend<F2> for VerifierTraverser {
    type Wire = F128b;

    fn input_public(&mut self) -> CircuitResult<Self::Wire> {
        todo!();
    }
    fn input_private(&mut self) -> CircuitResult<Self::Wire> {
        // Assign a fresh masked witness to the wire
        let res = self.next_masked_witness()?;

        // Private input gates don't define a polynomial that would contribute to the aggregate
        // being computed, so we ignore the challenge
        Ok(res)
    }

    fn add(&mut self, left: &Self::Wire, right: &Self::Wire) -> CircuitResult<Self::Wire> {
        // Compute the correct masked witness for the output wire
        Ok(left + right)

        // Linear gates don't contribute to the aggregate being computed
    }
    fn addc(&mut self, left: &Self::Wire, right: F2) -> CircuitResult<Self::Wire> {
        // Compute the correct masked witness for the output wire
        let t = if right == F2::ZERO {
            F128b::ZERO
        } else {
            F128b::ONE
        };
        Ok(left - t * self.verifier_key)

        // Linear gates don't contribute to the aggregate being computed
    }
    fn mul(&mut self, left: &Self::Wire, right: &Self::Wire) -> CircuitResult<Self::Wire> {
        // Assign the next masked witness to the destination wire
        let res = self.next_masked_witness()?;
        let challenge = self.chi_challenge.next();

        // Compute the contibution to the aggregate: ci​(Δ) = q_left * ​q_right ​− q_dst * ​Δ
        let eval = left * right - (res * self.verifier_key);

        self.aggregate += challenge * eval;

        Ok(res)
    }
    fn mulc(&mut self, _lhs: &Self::Wire, _rhs: F2) -> CircuitResult<Self::Wire> {
        todo!();
    }
    fn assert_zero(&mut self, arg: &Self::Wire) -> CircuitResult<()> {
        let challenge = self.chi_challenge.next();

        self.aggregate_assert_zero += challenge * arg;
        Ok(())
    }
}

impl HigherDegreeBackend<F2, F128b> for VerifierTraverser {
    /// The verifier's evaluation $`\rho(\Delta)`$ of the constraint commitment polynomial, along
    /// with the polynomial's degree.
    ///
    /// The degree is needed because the gate operations must mirror the degree alignment that
    /// [`CommitmentPolynomial`](crate::commitment_polynomial::CommitmentPolynomial) applies on
    /// the prover's side.
    type HigherDegreeWire = (F128b, usize);

    /// Mirrors [`CommitmentPolynomial::add`](crate::commitment_polynomial::CommitmentPolynomial::add):
    /// with $`d = \max(d_1, d_2)`$, the sum is $`t^{d - d_1} \rho_1(t) + t^{d - d_2} \rho_2(t)`$.
    fn h_add(
        &self,
        lhs: &Self::HigherDegreeWire,
        rhs: &Self::HigherDegreeWire,
    ) -> CircuitResult<Self::HigherDegreeWire> {
        let (eval_1, degree_1) = *lhs;
        let (eval_2, degree_2) = *rhs;
        let degree = degree_1.max(degree_2);

        let eval = power(self.verifier_key, degree - degree_1) * eval_1
            + power(self.verifier_key, degree - degree_2) * eval_2;
        Ok((eval, degree))
    }

    /// Mirrors [`CommitmentPolynomial::addc`](crate::commitment_polynomial::CommitmentPolynomial::addc),
    /// which adds $`c \cdot t^d`$.
    fn h_addc(
        &self,
        lhs: &Self::HigherDegreeWire,
        rhs: F2,
    ) -> CircuitResult<Self::HigherDegreeWire> {
        let (eval, degree) = *lhs;
        Ok((eval + rhs * power(self.verifier_key, degree), degree))
    }

    fn h_mul(
        &self,
        lhs: &Self::HigherDegreeWire,
        rhs: &Self::HigherDegreeWire,
    ) -> CircuitResult<Self::HigherDegreeWire> {
        let (eval_1, degree_1) = *lhs;
        let (eval_2, degree_2) = *rhs;
        Ok((eval_1 * eval_2, degree_1 + degree_2))
    }

    fn h_mulc(
        &self,
        lhs: &Self::HigherDegreeWire,
        rhs: F2,
    ) -> CircuitResult<Self::HigherDegreeWire> {
        let (eval, degree) = *lhs;
        Ok((rhs * eval, degree))
    }

    fn assert_zero_higher_degree<const INPUT_LEN: usize>(
        &mut self,
        inputs: &[Self::Wire; INPUT_LEN],
        f: impl Fn(&Self, [Self::HigherDegreeWire; INPUT_LEN]) -> Self::HigherDegreeWire,
    ) {
        // Each masked witness is the evaluation at Delta of the prover's degree-1 commitment
        // polynomial for that wire.
        let (gamma, degree) = f(self, std::array::from_fn(|i| (inputs[i], 1)));

        // Group the challenge-weighted evaluations by degree; the Delta^(d - d_i) alignment is
        // applied once the maximum degree d is known, after traversal.
        let challenge = self.chi_challenge.next();
        if degree >= self.higher_degree_aggregates.len() {
            self.higher_degree_aggregates.resize(degree + 1, F128b::ZERO);
        }
        self.higher_degree_aggregates[degree] += challenge * gamma;
    }
}
