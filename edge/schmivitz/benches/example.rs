use swanky_field_binary::{F2, F128b};
use swanky_sieve_ir_api::{
    CircuitExecuter, CircuitResult, FieldBackend, HigherDegreeBackend, HigherDegreeCircuitExecuter,
};

pub struct ExampleCircuit<const N: usize>;

// This circuit has no higher degree constraints, so executing it on a `HigherDegreeBackend` only
// exercises the `FieldBackend` gates.
impl<const N: usize> HigherDegreeCircuitExecuter<F2, F128b> for ExampleCircuit<N> {
    fn execute<B: HigherDegreeBackend<F2, F128b>>(&self, backend: &mut B) -> CircuitResult<()> {
        <Self as CircuitExecuter<F2>>::execute(self, backend)
    }
}

impl<const N: usize> CircuitExecuter<F2> for ExampleCircuit<N> {
    fn execute<B: FieldBackend<F2>>(&self, backend: &mut B) -> CircuitResult<()> {
        let mut v = backend.input_private()?;

        // N additions
        for _ in 0..N {
            v = backend.add(&v, &v)?;
        }

        // N multiplications
        for _ in 0..N {
            v = backend.mul(&v, &v)?;
        }

        // backend.assert_zero(&v2)?;

        Ok(())
    }
}
