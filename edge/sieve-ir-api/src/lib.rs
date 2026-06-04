//! A Rust based API for writing zero-knowledge circuits in a style compatible with
//! [SIEVE IR](https://github.com/sieve-zk/ir). This provides a programmatic way to write circuits,
//! which should be faster than parsing a circuit dynamically.
//!
//! Here's a simple example that demonstrates how to write a boolean circuit programmatically.
//! ```
//! use swanky_field_binary::F2;
//! use swanky_sieve_ir_api::*;
//!
//! fn example1<B>(backend: &mut B) -> CircuitResult<()>
//! where
//!     B: FieldBackend<F2>,
//! {
//!     let v0 = backend.input_private()?;
//!     let v1 = backend.mul(&v0, &v0)?;
//!     let v2 = backend.add(&v1, &v1)?;
//!
//!     backend.assert_zero(&v2)?;
//!
//!     Ok(())
//! }
//! ```
//!
//! Here's another example that defines a circuit with multiple fields.
//! ```
//! use swanky_field_binary::F2;
//! use swanky_field_ff_primes::F128p;
//! use swanky_sieve_ir_api::*;
//!
//! fn helper_circuit<B>(
//!     backend: &mut B,
//!     arg1: &B::Wire,
//!     arg2: &B::Wire,
//!     arg3: &B::Wire,
//! ) -> CircuitResult<(B::Wire, B::Wire)>
//! where
//!     B: FieldBackend<F2>,
//! {
//!     let v1 = backend.add(arg1, arg2)?;
//!     let v2 = backend.add(arg3, &v1)?;
//!
//!     Ok((v1, v2))
//! }
//!
//! fn example2<B>(backend: &mut B) -> CircuitResult<()>
//! where
//!     B: FieldBackend<F2>,
//!     B: FieldBackend<F128p>,
//! {
//!     let v0 = <B as FieldBackend<F2>>::input_private(backend)?;
//!     let v1 = <B as FieldBackend<F2>>::mul(backend, &v0, &v0)?;
//!     let v2 = <B as FieldBackend<F2>>::add(backend, &v1, &v1)?;
//!
//!     <B as FieldBackend<F2>>::assert_zero(backend, &v2)?;
//!
//!     let p0 = <B as FieldBackend<F128p>>::input_private(backend)?;
//!     let p1 = <B as FieldBackend<F128p>>::input_private(backend)?;
//!     let p2 = <B as FieldBackend<F128p>>::add(backend, &p0, &p1)?;
//!     <B as FieldBackend<F128p>>::assert_zero(backend, &p2)?;
//!
//!     let (v3, v4) = helper_circuit(backend, &v0, &v1, &v2)?;
//!     <B as FieldBackend<F2>>::assert_zero(backend, &v3)?;
//!     <B as FieldBackend<F2>>::assert_zero(backend, &v4)?;
//!
//!     Ok(())
//! }
//! ```
//!
//! ```
//! use swanky_field_binary::F2;
//! use swanky_sieve_ir_api::*;
//!
//! fn example3<B>(backend: &mut B) -> CircuitResult<()>
//! where
//!     B: PolyBackend<F2>,
//! {
//!     let v0 = backend.input_private()?;
//!     let v1 = backend.mul(&v0, &v0)?;
//!     let v2 = backend.add(&v1, &v1)?;
//!
//!     backend.assert_zero(&v2)?;
//!
//!     let inps = backend.inputs_private::<16>()?;
//!     backend.poly_gate(&inps, |x: [F2; 16]| x[0] * x[1] * x[2] * x[3]);
//!     Ok(())
//! }
//! ```

#![deny(missing_docs)]

pub mod commitment_polynomial;

use std::array;
use std::fmt::Debug;
use std::ops::{Add, Mul, Sub};
use swanky_error::{ErrorKind, swanky_error};

/// Error types for a SIEVE IR circuit.
pub type CircuitResult<T> = swanky_error::Result<T>;

/// API for field backends that conform to SIEVE IR.
pub trait FieldBackend<F> {
    /// Backend's repesentation for wire values.
    type Wire: Debug + Default + Clone + Copy;

    /// Read a public instance value.
    fn input_public(&mut self) -> CircuitResult<Self::Wire>;

    /// Read multiple public instance values.
    fn inputs_public<const LEN: usize>(&mut self) -> CircuitResult<[Self::Wire; LEN]> {
        // TODO: Use `std::array::try_from_fn` when it's stable.
        let v = (0..LEN)
            .map(|_| self.input_public())
            .collect::<CircuitResult<Vec<Self::Wire>>>()?;
        v.try_into()
            .map_err(|e| swanky_error!(ErrorKind::OtherError, "Conversion error: {e:?}"))
    }

    /// Read a private witness value.
    fn input_private(&mut self) -> CircuitResult<Self::Wire>;

    /// Read multiple private witness values.
    fn inputs_private<const LEN: usize>(&mut self) -> CircuitResult<[Self::Wire; LEN]> {
        // TODO: Use `std::array::try_from_fn` when it's stable.
        let v = (0..LEN)
            .map(|_| self.input_private())
            .collect::<CircuitResult<Vec<Self::Wire>>>()?;
        v.try_into()
            .map_err(|e| swanky_error!(ErrorKind::OtherError, "Conversion error: {e:?}"))
    }

    /// Field addition.
    fn add(&mut self, lhs: &Self::Wire, rhs: &Self::Wire) -> CircuitResult<Self::Wire>;

    /// Field addition with a constant.
    fn addc(&mut self, lhs: &Self::Wire, rhs: F) -> CircuitResult<Self::Wire>;

    /// Field multiplication.
    fn mul(&mut self, lhs: &Self::Wire, rhs: &Self::Wire) -> CircuitResult<Self::Wire>;

    /// Field multiplication with a constant.
    fn mulc(&mut self, lhs: &Self::Wire, rhs: F) -> CircuitResult<Self::Wire>;

    /// An assertion that the argument is zero.
    fn assert_zero(&mut self, arg: &Self::Wire) -> CircuitResult<()>;
}

/// `CircuitExecuter` abstracts over backends to execute a circuit over a single field type.
/// Note that this is necessary since Rust currently does not support higher order trait bounds. See <https://github.com/rust-lang/rust/issues/108185#issuecomment-2819123578>
pub trait CircuitExecuter<F> {
    /// The body of the circuit to execute, given a backend.
    fn execute<B: FieldBackend<F>>(&self, backend: &mut B) -> CircuitResult<()>;
}

/// Gello
/* pub trait PolyBackend<F>: FieldBackend<F> {
    /// Gello4
    type Polynomial;

    /// Gello2
    fn poly_gate<const INPUT_LEN: usize>(
        &mut self,
        inputs: &[Self::Wire; INPUT_LEN],
        f: impl Fn([Self::Polynomial; INPUT_LEN]) -> Self::Polynomial,
    ) -> CircuitResult<Self::Wire>;
} */

/// A trait abstracting over backends that support higher degree constraints.
pub trait HigherDegreeBackend<F>: FieldBackend<F> {
    // TODO:
    // type Polynomial;

    /// Assert that a higher degree constraint equals 0.
    fn assert_zero_higher_degree<const INPUT_LEN: usize, T: Add + Sub + Mul>(
        &mut self,
        inputs: &[Self::Wire; INPUT_LEN],
        f: impl Fn([T; INPUT_LEN]) -> T,
    );
    /*
    /// Helper function to return the wire value returned by a higher degree gate.
    /// By default, this will witness a new private input and assert that it equals the output of
    /// the higher degree constraint.
    fn higher_degree_gate<const INPUT_LEN: usize, T: Add + Sub + Mul>(
        &mut self,
        inputs: &[Self::Wire; INPUT_LEN],
        f: impl Fn([T; INPUT_LEN]) -> T,
    ) -> CircuitResult<Self::Wire> {
        // Witness a new witness value.
        let output_wire = self.input_private()?;

        // Append `output` to inputs.
        let inputs: [Self::Wire; INPUT_LEN+1] = array::from_fn(|i|
            if i < INPUT_LEN { inputs[i] } else { output_wire }
        );

        self.assert_zero_higher_degree(inputs, |inputs| {
            let f_inputs: &[T; INPUT_LEN] = &inputs[0..INPUT_LEN];
            let x = f(f_inputs);

            let output = inputs[INPUT_LEN];
            x - output
        });

        output_wire
    }*/
}
