use mac_n_cheese_sieve_parser::WireId;
use swanky_error::{ErrorKind, Result, bail, swanky_error};
use swanky_field::FiniteRing;
use swanky_field_binary::{F2, F128b};
use swanky_sieve_ir_api::{CircuitResult, FieldBackend, HigherDegreeBackend};

use crate::commitment_polynomial::CommitmentPolynomial;
use crate::proof::ChiGenerator;
use crate::vole::RandomVoleP;

/// A [`ProverTraverser`] allows the prover to execute the gate-by-gate evaluation portion of the
/// VOLE-in-the-head protocol.
///
/// The primary steps in circuit traversal include assigning VOLEs to each wire and
/// computing the two aggregated values used in the proof.
pub(crate) struct ProverTraverser<Vole> {
    /// Current position for a fresh extended witness value.
    wire_values_pos: WireId,

    /// Map containing the wire values for the extended witness (private inputs and multiplication gates in the circuit).
    extended_witness: Vec<F2>,
    /// Fiat-Shamir challenges as powers of chi. There should be one for each polynomial (e.g. non-linear gate) and assert zero.
    chi_challenge: ChiGenerator,

    /// Random VOLE values. There should be one for each extended witness value.
    voles: Vole,
    /// Count of how many of the custom VOLEs have been assigned.
    vole_assignment_count: usize,

    /// Partial aggregation of the value $`\tilde a`$ from the protocol.
    ///
    /// After traversal, this should have the value $$`\sum_{i \in [t]} \chi_i \cdot A_{i,1}`$$.
    aggregate_degree_0: F128b,
    /// Partial aggregation of the value $`\tilde b`$ from the protocol.
    ///
    /// After traversal, this should have the value $$`\sum_{i \in [t]} \chi_i \cdot A_{i,0}`$$.
    aggregate_degree_1: F128b,

    /// Partial aggregation of the assert zero check.
    /// TODO: Add this to the specification and reference it.
    aggregate_assert_zero: F128b,

    /// Commitment polynomials collected from higher degree constraints during traversal.
    ///
    /// Unlike the degree-2 aggregates above, these are batched after traversal with their own
    /// challenge (see [`crate::polynomial_constraint::batch_prove`]), so they don't consume chi
    /// challenges or fresh VOLEs.
    higher_degree_constraints: Vec<CommitmentPolynomial<F2, F128b>>,
}

impl<Vole: RandomVoleP> ProverTraverser<Vole> {
    /// Create a new circuit traverser.
    ///
    /// Requirements on inputs:
    /// - The `extended_witness` must contain a corresponding value for the input and output wires on
    ///   every non-linear gate;
    /// - The challenges must correspond to the number of polynomials. In this setting, that must
    ///   be no greater than the length of the extended witness (as defined by the [`RandomVole`]);
    /// - The [`RandomVole::extended_witness_length()`] must be large enough to have a VOLE
    ///   corresponding to every gate in the extended witness.
    pub(crate) fn new(
        extended_witness: Vec<F2>,
        chi_challenge: ChiGenerator,
        voles: Vole,
    ) -> Result<Self> {
        // TODO: debug_assert!(extended_witness.len() == voles.extended_witness_length())
        Ok(Self {
            wire_values_pos: 0,
            extended_witness,
            chi_challenge,

            voles,
            vole_assignment_count: 0,

            aggregate_degree_0: F128b::ZERO,
            aggregate_degree_1: F128b::ZERO,

            aggregate_assert_zero: F128b::ZERO,

            higher_degree_constraints: Vec::new(),
        })
    }

    fn next_vole(&mut self) -> Result<F128b> {
        let next_index = self.vole_assignment_count;
        self.vole_assignment_count += 1;

        // These two checks should be equivalent because we checked at construction that the
        // challenge list is exactly the extended witness length.
        if next_index >= self.voles.extended_witness_length() {
            bail!(
                ErrorKind::OtherError,
                "Bad input: needed at least {} VOLEs, but only got {}",
                self.vole_assignment_count,
                self.voles.extended_witness_length()
            )
        }

        self.voles.vole_mask(next_index)
    }

    /// Decomposes into the aggregate components that we constructed during the
    /// full circuit traversal.
    ///
    /// The components that were passed to [`Self::new()`] are returned unchanged.
    ///
    /// This will fail if there were unused challenges or VOLEs.
    pub(crate) fn into_parts(self) -> Result<(F128b, F128b, F128b, Vole)> {
        if self.vole_assignment_count != self.voles.extended_witness_length() {
            bail!(
                ErrorKind::OtherError,
                "Traversal contained more VOLEs than it needed! Had {}, used {}",
                self.voles.extended_witness_length(),
                self.vole_assignment_count
            );
        }
        Ok((
            self.aggregate_degree_0,
            self.aggregate_degree_1,
            self.aggregate_assert_zero,
            self.voles,
        ))
    }

    /// Get the next extended witness value.
    pub(crate) fn next_witness_value(&mut self) -> Result<F2> {
        let wid = self.wire_values_pos;
        self.wire_values_pos += 1;

        self.extended_witness
            .get::<usize>(
                wid.try_into()
                    .map_err(|e| swanky_error!(ErrorKind::OtherError, "Conversion error: {e}"))?,
            )
            .ok_or_else(|| {
                swanky_error!(
                    ErrorKind::OtherError,
                    "Internal invariant failed: expected a witness value for wire ID {}",
                    wid
                )
            })
            .copied()
    }

    /// Get the commitment polynomials collected from higher degree constraints during traversal.
    ///
    /// These should be batched and proven with
    /// [`crate::polynomial_constraint::batch_prove`] after traversal.
    #[allow(dead_code)] // TODO: Remove once higher degree constraints are wired into the proof.
    pub(crate) fn higher_degree_constraints(&self) -> &[CommitmentPolynomial<F2, F128b>] {
        &self.higher_degree_constraints
    }
}

// TODO: Generalize this for large primes.
impl<VOLE: RandomVoleP> FieldBackend<F2> for ProverTraverser<VOLE> {
    type Wire = (F2, F128b);
    fn input_public(&mut self) -> CircuitResult<Self::Wire> {
        todo!()
    }
    fn input_private(&mut self) -> CircuitResult<Self::Wire> {
        let f = self.next_witness_value()?;
        let vole = self.next_vole()?;

        // Private input gates don't define a polynomial that would contribute to the aggregated
        // coefficients being computed
        Ok((f, vole))
    }
    fn add(&mut self, left: &Self::Wire, right: &Self::Wire) -> CircuitResult<Self::Wire> {
        let res = left.0 + right.0;

        // Compute the correct VOLE for the output wire
        let sum_vole = left.1 + right.1;

        // Linear gates don't contribute to the aggregated values being computed
        Ok((res, sum_vole))
    }
    fn addc(&mut self, left: &Self::Wire, right: F2) -> CircuitResult<Self::Wire> {
        let res = left.0 + right;

        // Compute the correct VOLE for the output wire
        let sum_vole = left.1;

        // Linear gates don't contribute to the aggregated values being computed
        Ok((res, sum_vole))
    }
    fn mul(&mut self, left: &Self::Wire, right: &Self::Wire) -> CircuitResult<Self::Wire> {
        let f = self.next_witness_value()?;

        // Assign a fresh VOLE to the output wire and get the corresponding challenge
        let vole = self.next_vole()?;
        let challenge = self.chi_challenge.next();

        // Compute coefficient values `A_i1` and `A_i0` (respectively). These are derived from the
        // `c_i(X)` polynomial defined in the paper -- see Fig 7 and page 32-33 for details.
        let degree_0_coeff = left.1 * right.1;
        let degree_1_coeff = right.0 * left.1 + left.0 * right.1 - vole;

        self.aggregate_degree_0 += challenge * degree_0_coeff;
        self.aggregate_degree_1 += challenge * degree_1_coeff;

        Ok((f, vole))
    }
    fn mulc(&mut self, _: &Self::Wire, _: F2) -> CircuitResult<Self::Wire> {
        todo!()
    }
    fn assert_zero(&mut self, wire: &Self::Wire) -> CircuitResult<()> {
        let challenge = self.chi_challenge.next();
        self.aggregate_assert_zero += challenge * wire.1;

        Ok(())
    }
}

impl<VOLE: RandomVoleP> HigherDegreeBackend<F2, F128b> for ProverTraverser<VOLE> {
    type HigherDegreeWire = CommitmentPolynomial<F2, F128b>;

    fn h_add(
        lhs: &Self::HigherDegreeWire,
        rhs: &Self::HigherDegreeWire,
    ) -> CircuitResult<Self::HigherDegreeWire> {
        Ok(lhs.add(rhs))
    }

    fn h_addc(lhs: &Self::HigherDegreeWire, rhs: F2) -> CircuitResult<Self::HigherDegreeWire> {
        Ok(lhs.addc(rhs))
    }

    fn h_mul(
        lhs: &Self::HigherDegreeWire,
        rhs: &Self::HigherDegreeWire,
    ) -> CircuitResult<Self::HigherDegreeWire> {
        Ok(lhs.mul(rhs))
    }

    fn h_mulc(lhs: &Self::HigherDegreeWire, rhs: F2) -> CircuitResult<Self::HigherDegreeWire> {
        Ok(lhs.mulc(rhs))
    }

    fn assert_zero_higher_degree<const INPUT_LEN: usize>(
        &mut self,
        inputs: &[Self::Wire; INPUT_LEN],
        f: impl Fn([Self::HigherDegreeWire; INPUT_LEN]) -> Self::HigherDegreeWire,
    ) {
        // Lift each input wire (value, VOLE mask) into its degree-1 commitment polynomial
        // ρ(t) = w + x·t and evaluate the constraint over the polynomials.
        let constraint = f(std::array::from_fn(|i| {
            CommitmentPolynomial::from_base_vole(inputs[i].0, inputs[i].1)
        }));

        // The highest-degree coefficient is the constraint evaluated on the witness values, so an
        // honest prover always commits to zero here.
        debug_assert_eq!(constraint.highest_degree(), F2::ZERO);

        self.higher_degree_constraints.push(constraint);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use merlin::Transcript;
    use rand::thread_rng;

    use crate::vole::insecure::InsecureVole;

    type Traverser = ProverTraverser<InsecureVole>;

    fn test_traverser() -> Traverser {
        let rng = &mut thread_rng();
        let transcript = &mut Transcript::new(b"higher degree tests");
        let secret: Vec<F2> = Vec::new();
        let (voles, _challenge) = InsecureVole::create(0, transcript, &secret, rng);

        ProverTraverser::new(Vec::new(), ChiGenerator::new(F128b::random(rng)), voles).unwrap()
    }

    /// The collected constraint polynomial must commit to zero and be consistent with the
    /// verifier's view: evaluating it at any point Δ must match the constraint computed
    /// homomorphically over the wire tags q_i = w_i + x_i·Δ.
    #[test]
    fn higher_degree_constraints_match_homomorphic_evaluation() {
        let rng = &mut thread_rng();
        let mut traverser = test_traverser();

        // Witness satisfying x0 * x1 * x2 * x3 == 0.
        let product_values = [F2::ONE, F2::ONE, F2::ZERO, F2::ONE];
        let product_wires: [(F2, F128b); 4] =
            std::array::from_fn(|i| (product_values[i], F128b::random(rng)));
        traverser.assert_zero_higher_degree(&product_wires, |x| {
            let x01 = Traverser::h_mul(&x[0], &x[1]).unwrap();
            let x23 = Traverser::h_mul(&x[2], &x[3]).unwrap();
            Traverser::h_mul(&x01, &x23).unwrap()
        });

        // Witness satisfying x0 * x1 + x2 * x3 == 0.
        let sum_values = [F2::ONE; 4];
        let sum_wires: [(F2, F128b); 4] =
            std::array::from_fn(|i| (sum_values[i], F128b::random(rng)));
        traverser.assert_zero_higher_degree(&sum_wires, |x| {
            let x01 = Traverser::h_mul(&x[0], &x[1]).unwrap();
            let x23 = Traverser::h_mul(&x[2], &x[3]).unwrap();
            Traverser::h_add(&x01, &x23).unwrap()
        });

        let constraints = traverser.higher_degree_constraints();
        assert_eq!(constraints.len(), 2);
        assert_eq!(constraints[0].degree(), 4);
        assert_eq!(constraints[1].degree(), 2);

        let delta = F128b::random(rng);
        let tag = |(x, w): (F2, F128b)| w + x * delta;

        let expected_product = product_wires.map(tag).iter().fold(F128b::ONE, |a, q| a * q);
        assert_eq!(constraints[0].highest_degree(), F2::ZERO);
        assert_eq!(constraints[0].evaluate_at_point(delta), expected_product);

        let sum_tags = sum_wires.map(tag);
        let expected_sum = sum_tags[0] * sum_tags[1] + sum_tags[2] * sum_tags[3];
        assert_eq!(constraints[1].highest_degree(), F2::ZERO);
        assert_eq!(constraints[1].evaluate_at_point(delta), expected_sum);
    }

    /// Constant operations apply the constant to the committed value.
    #[test]
    fn constant_operations_apply_to_the_committed_value() {
        let rng = &mut thread_rng();
        let poly = CommitmentPolynomial::from_base_vole(F2::ONE, F128b::random(rng));

        let sum = Traverser::h_addc(&poly, F2::ONE).unwrap();
        assert_eq!(sum.highest_degree(), F2::ZERO);
        let scaled = Traverser::h_mulc(&poly, F2::ZERO).unwrap();
        assert_eq!(scaled.highest_degree(), F2::ZERO);
    }
}
