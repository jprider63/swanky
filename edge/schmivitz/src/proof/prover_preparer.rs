use mac_n_cheese_sieve_parser::WireId;
use swanky_error::{ErrorKind, bail};
use swanky_field_binary::{F2, F128b};
use swanky_sieve_ir_api::{CircuitResult, FieldBackend, HigherDegreeBackend};

/// A [`ProverPreparer`] allows the prover to prepare for VOLE-in-the-head by evaluating the
/// circuit in the clear and determining the full extended witness.
///
/// The total extended witness includes two types of values:
/// - Private inputs to the circuit (this is the "non-extended" witness)
/// - Outputs of non-linear (multiplication) gates (this is the "extended" part)
///
/// ## Failure modes
/// This type is only designed to be used with a VOLE-in-the-head circuit. Its methods will fail
/// if it visits a circuit where:
/// - there are gates other than `private-input`, `add`, `addc`, or `mul`
/// - there is more than one type ID used for any gate
/// - any private input to the circuit is not in $`F2`$
#[derive(Debug)]
pub(crate) struct ProverPreparer<'a> {
    /// Private circuit inputs.
    private_input: &'a [F2],

    /// Current position for the next witness value.
    priv_input_pos: u64,

    /// Set of wire values that correspond to elements in the extended witness.
    witness: Vec<F2>,

    /// Number of polynomials that will need challenges.
    challenge_count: usize,

    /// Maximum degree among the higher degree constraint polynomials in the circuit.
    max_higher_degree: usize,
}

impl<'a> ProverPreparer<'a> {
    pub(crate) fn new(private_input: &'a [F2], max_wire_id: WireId) -> swanky_error::Result<Self> {
        Ok(Self {
            private_input,
            priv_input_pos: 0,
            witness: Vec::with_capacity(max_wire_id as usize),
            challenge_count: 0,
            max_higher_degree: 0,
        })
    }

    #[cfg(test)]
    pub(crate) fn count(&self) -> usize {
        self.witness.len()
    }

    /// Get the maximum degree among the higher degree constraint polynomials seen during
    /// traversal (0 if there were none).
    pub(crate) fn max_higher_degree(&self) -> usize {
        self.max_higher_degree
    }

    /// Get the witness and number of challenges required.
    ///
    /// These values will be empty if the circuit has not yet been traversed.
    pub(crate) fn into_parts(self) -> (Vec<F2>, usize) {
        (self.witness, self.challenge_count)
    }
}

// TODO: Generalize this for large primes.
impl<'a> FieldBackend<F2> for ProverPreparer<'a> {
    type Wire = F2;

    fn input_public(&mut self) -> CircuitResult<Self::Wire> {
        bail!(
            ErrorKind::OtherError,
            "Invalid input: VOLE-in-the-head does not support gate public inputs"
        );
    }
    fn input_private(&mut self) -> CircuitResult<Self::Wire> {
        let f2 = self.private_input[self.priv_input_pos as usize];
        self.priv_input_pos += 1;

        // TODO: Can we push all of the input witnesses up front?
        self.witness.push(f2);

        Ok(f2)
    }
    fn add(&mut self, left: &Self::Wire, right: &Self::Wire) -> CircuitResult<Self::Wire> {
        let sum = left + right;

        Ok(sum)
    }
    fn addc(&mut self, left: &Self::Wire, right: F2) -> CircuitResult<Self::Wire> {
        let sum = left + right;

        Ok(sum)
    }
    fn mul(&mut self, left: &Self::Wire, right: &Self::Wire) -> CircuitResult<Self::Wire> {
        self.challenge_count += 1;

        let product = left * right;

        // Save product to the witness.
        self.witness.push(product);
        Ok(product)
    }
    fn mulc(&mut self, _: &Self::Wire, _: F2) -> CircuitResult<Self::Wire> {
        bail!(
            ErrorKind::OtherError,
            "Invalid input: VOLE-in-the-head does not support gate mulc"
        );
    }
    fn assert_zero(&mut self, _: &Self::Wire) -> CircuitResult<()> {
        self.challenge_count += 1;
        Ok(())
    }
}

impl<'a> HigherDegreeBackend<F2, F128b> for ProverPreparer<'a> {
    /// The degree of the commitment polynomial that the
    /// [`ProverTraverser`](crate::proof::prover_traverser::ProverTraverser) will build for the
    /// wire.
    ///
    /// The degree rules mirror [`crate::commitment_polynomial::CommitmentPolynomial`]: input
    /// wires have degree 1, addition aligns to the larger degree, and multiplication sums the
    /// degrees.
    type HigherDegreeWire = usize;

    fn h_add(
        &self,
        lhs: &Self::HigherDegreeWire,
        rhs: &Self::HigherDegreeWire,
    ) -> CircuitResult<Self::HigherDegreeWire> {
        Ok(*lhs.max(rhs))
    }

    fn h_addc(
        &self,
        lhs: &Self::HigherDegreeWire,
        _: F2,
    ) -> CircuitResult<Self::HigherDegreeWire> {
        Ok(*lhs)
    }

    fn h_mul(
        &self,
        lhs: &Self::HigherDegreeWire,
        rhs: &Self::HigherDegreeWire,
    ) -> CircuitResult<Self::HigherDegreeWire> {
        Ok(lhs + rhs)
    }

    fn h_mulc(
        &self,
        lhs: &Self::HigherDegreeWire,
        _: F2,
    ) -> CircuitResult<Self::HigherDegreeWire> {
        Ok(*lhs)
    }

    fn assert_zero_higher_degree<const INPUT_LEN: usize>(
        &mut self,
        _: &[Self::Wire; INPUT_LEN],
        f: impl Fn(&Self, [Self::HigherDegreeWire; INPUT_LEN]) -> Self::HigherDegreeWire,
    ) {
        self.challenge_count += 1;

        // Each input wire lifts to a degree-1 commitment polynomial during traversal.
        let degree = f(self, [1; INPUT_LEN]);
        self.max_higher_degree = self.max_higher_degree.max(degree);
    }
}

#[cfg(test)]
mod tests {
    use rand::thread_rng;
    use std::io::Cursor;

    use mac_n_cheese_sieve_parser::text_parser::RelationReader;
    use swanky_field::FiniteRing;
    use swanky_field_binary::F2;
    use swanky_sieve_ir_api::{CircuitExecuter, HigherDegreeBackend};

    use crate::circuit::CircuitIngestor;
    use crate::proof::{Circuit, prover_preparer::ProverPreparer};

    /// Take a string description of a circuit and parse it.
    fn load_circuit(circuit: &str) -> swanky_error::Result<Circuit> {
        let rng = &mut thread_rng();
        // Generate a private input vector with 100 random inputs
        let random_private_inputs: Vec<F2> = (0..100).map(|_| F2::random(rng)).collect();

        let cursor = &mut Cursor::new(circuit.as_bytes());
        let reader = RelationReader::new(cursor)?;
        let mut circ = CircuitIngestor::new_prover(random_private_inputs)?;
        reader.read(&mut circ)?;

        let circuit_loaded = circ.into_circuit();
        Ok(circuit_loaded)
    }

    fn prepare_circuit<'a>(
        circuit_loaded: &'a Circuit,
    ) -> swanky_error::Result<ProverPreparer<'a>> {
        let (circuit, private_input, max_wire_id) = circuit_loaded.to_interpreter();

        let mut counter: ProverPreparer = ProverPreparer::new(private_input, max_wire_id)?;
        circuit.execute(&mut counter)?;
        Ok(counter)
    }

    #[test]
    fn private_inputs_count_correctly() -> swanky_error::Result<()> {
        let private_input_only = "version 2.0.0;
            circuit;
            @type field 2;
            @begin
              $0 <- @private(0);
              $1 <- @private(0);
              $2 <- @private(0);
            @end ";
        let circuit = load_circuit(private_input_only)?;
        let counter = prepare_circuit(&circuit)?;
        assert_eq!(counter.count(), 3);

        let private_input_range = "version 2.0.0;
            circuit;
            @type field 2;
            @begin
              $0 ... $3 <- @private(0);
            @end";
        let circuit = load_circuit(private_input_range)?;
        let counter = prepare_circuit(&circuit)?;
        assert_eq!(counter.count(), 4);
        Ok(())
    }

    #[test]
    fn multiplication_gates_count_correctly() -> swanky_error::Result<()> {
        let one_mul = "version 2.0.0;
            circuit;
            @type field 2;
            @begin
              $0 <- @private(0);
              $1 <- @mul(0: $0, $0);
            @end ";
        let circuit = load_circuit(one_mul)?;
        let counter = prepare_circuit(&circuit)?;
        assert_eq!(counter.count(), 2);

        let many_mul = "version 2.0.0;
            circuit;
            @type field 2;
            @begin
              $0 <- @private(0);
              $1 <- @mul(0: $0, $0);
              $2 <- @mul(0: $0, $1);
              $3 <- @mul(0: $0, $2);
              $4 <- @mul(0: $0, $3);
              $5 <- @mul(0: $0, $4);
              $6 <- @mul(0: $0, $5);
            @end ";
        let circuit = load_circuit(many_mul)?;
        let counter = prepare_circuit(&circuit)?;
        assert_eq!(counter.count(), 7);
        Ok(())
    }

    #[test]
    fn add_gates_are_not_counted_in_extended_witness() -> swanky_error::Result<()> {
        // These are the same circuits as in `multiplication_gates_count_correctly`, but with an
        // extra `@add` thrown in.
        let one_mul = "version 2.0.0;
            circuit;
            @type field 2;
            @begin
              $0 <- @private(0);
              $1 <- @mul(0: $0, $0);
              $2 <- @add(0: $0, $0);
            @end ";
        let circuit = load_circuit(one_mul)?;
        let counter = prepare_circuit(&circuit)?;
        assert_eq!(counter.count(), 2);

        let many_mul = "version 2.0.0;
            circuit;
            @type field 2;
            @begin
              $0 <- @private(0);
              $1 <- @mul(0: $0, $0);
              $2 <- @mul(0: $0, $1);
              $3 <- @mul(0: $0, $2);
              $7 <- @add(0: $0, $2);
              $4 <- @mul(0: $0, $3);
              $5 <- @mul(0: $0, $4);
              $6 <- @mul(0: $0, $5);
            @end ";
        let circuit = load_circuit(many_mul)?;
        let counter = prepare_circuit(&circuit)?;
        assert_eq!(counter.count(), 7);
        Ok(())
    }

    #[test]
    fn higher_degree_operations_compute_correct_degrees() {
        let private_input: Vec<F2> = Vec::new();
        let preparer = ProverPreparer::new(&private_input, 0).unwrap();
        let x = 3;
        let y = 2;

        // Addition aligns to the larger degree, multiplication sums the degrees, and constant
        // operations leave the degree unchanged.
        assert_eq!(preparer.h_add(&x, &y).unwrap(), 3);
        assert_eq!(preparer.h_mul(&x, &y).unwrap(), 5);
        assert_eq!(preparer.h_addc(&y, F2::ONE).unwrap(), 2);
        assert_eq!(preparer.h_mulc(&y, F2::ZERO).unwrap(), 2);
    }

    #[test]
    fn higher_degree_constraints_track_max_degree() -> swanky_error::Result<()> {
        let private_input: Vec<F2> = Vec::new();
        let mut preparer = ProverPreparer::new(&private_input, 0)?;
        assert_eq!(preparer.max_higher_degree(), 0);

        // x0 * x1 * x2 * x3, a degree-4 constraint.
        let wires = [F2::ONE, F2::ONE, F2::ZERO, F2::ONE];
        preparer.assert_zero_higher_degree(&wires, |b, x| {
            let x01 = b.h_mul(&x[0], &x[1]).unwrap();
            let x23 = b.h_mul(&x[2], &x[3]).unwrap();
            b.h_mul(&x01, &x23).unwrap()
        });
        assert_eq!(preparer.max_higher_degree(), 4);

        // A subsequent lower-degree constraint (x0 * x1 + x2 * x3, degree 2) doesn't lower the
        // maximum.
        preparer.assert_zero_higher_degree(&wires, |b, x| {
            let x01 = b.h_mul(&x[0], &x[1]).unwrap();
            let x23 = b.h_mul(&x[2], &x[3]).unwrap();
            b.h_add(&x01, &x23).unwrap()
        });
        assert_eq!(preparer.max_higher_degree(), 4);

        // Higher degree constraints don't add witness values, but each needs a challenge.
        let (witness, challenge_count) = preparer.into_parts();
        assert!(witness.is_empty());
        assert_eq!(challenge_count, 2);

        Ok(())
    }

    #[test]
    fn mul_gates_eval_correctly() -> swanky_error::Result<()> {
        let one_mul = "version 2.0.0;
            circuit;
            @type field 2;
            @begin
              $0 <- @private(0);
              $1 <- @private(0);
              $2 <- @mul(0: $0, $1);
            @end ";

        // This evaluates on a random input; over time we'll check them all
        let circuit = load_circuit(one_mul)?;
        let counter = prepare_circuit(&circuit)?;
        assert_eq!(
            counter.witness.first().unwrap() * counter.witness.get(1).unwrap(),
            *counter.witness.get(2).unwrap()
        );

        Ok(())
    }
}
