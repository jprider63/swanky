//! Polynomial commitment type for VOLE-based zero-knowledge protocols.
//!
//! A [`CommitmentPolynomial`] represents the polynomial ρ_x(t) = ρ_0 + ρ_1·t + ··· + ρ_d·t^d
//! where ρ_d = x is the committed value and ρ_0, ..., ρ_{d-1} are random masking coefficients
//! drawn from the extension field.
//!
//! Gate operations allow building commitment polynomials bottom-up through a circuit:
//! - [`CommitmentPolynomial::addc`]: add a constant
//! - [`CommitmentPolynomial::add`]: add two commitments (aligning degrees)
//! - [`CommitmentPolynomial::mulc`]: multiply by a constant
//! - [`CommitmentPolynomial::mul`]: multiply two commitments

use swanky_field::FiniteField;

/// A polynomial commitment over an extension field `FE`.
///
/// Stores the coefficients `[ρ_0, ρ_1, ..., ρ_d]` of the polynomial
/// ρ(t) = ρ_0 + ρ_1·t + ··· + ρ_d·t^d, where ρ_d is the committed value.
#[derive(Clone, Debug)]
pub struct CommitmentPolynomial<FE: FiniteField> {
    coefficients: Vec<FE>,
}

impl<FE: FiniteField> CommitmentPolynomial<FE> {
    /// Create a commitment polynomial from a base VOLE.
    ///
    /// Given a value `x` and a VOLE mask `w`, constructs ρ(t) = w + x·t (degree 1).
    pub fn from_base_vole(value: FE, mask: FE) -> Self {
        Self {
            coefficients: vec![mask, value],
        }
    }

    /// Create a commitment polynomial directly from coefficients.
    ///
    /// The last coefficient is the committed value.
    pub fn from_coefficients(coefficients: Vec<FE>) -> Self {
        assert!(!coefficients.is_empty(), "polynomial must have at least one coefficient");
        Self { coefficients }
    }

    /// Return the degree of the polynomial.
    pub fn degree(&self) -> usize {
        self.coefficients.len() - 1
    }

    /// Return a reference to the coefficients [ρ_0, ..., ρ_d].
    pub fn coefficients(&self) -> &[FE] {
        &self.coefficients
    }

    /// Evaluate the polynomial at a given point using Horner's method.
    ///
    /// This is useful for the verifier to evaluate at Δ (the global VOLE key).
    pub fn evaluate_at_point(&self, point: FE) -> FE {
        let mut result = FE::ZERO;
        for c in self.coefficients.iter().rev() {
            result = result * point + *c;
        }
        result
    }

    /// Add a constant: ρ(t) = ρ_x(t) + c·t^d
    ///
    /// The constant is added to the highest-degree coefficient (the committed value).
    pub fn addc(&self, c: FE) -> Self {
        let mut coeffs = self.coefficients.clone();
        let d = self.degree();
        coeffs[d] = coeffs[d] + c;
        Self {
            coefficients: coeffs,
        }
    }

    /// Add two commitment polynomials, aligning to the maximum degree.
    ///
    /// Given ρ_x of degree d_1 and ρ_y of degree d_2, with d = max(d_1, d_2):
    /// ρ(t) = t^(d - d_1)·ρ_x(t) + t^(d - d_2)·ρ_y(t)
    pub fn add(&self, other: &Self) -> Self {
        let d1 = self.degree();
        let d2 = other.degree();
        let d = d1.max(d2);

        let shift1 = d - d1;
        let shift2 = d - d2;
        let new_len = d + 1;

        let mut coeffs = vec![FE::ZERO; new_len];

        for (i, c) in self.coefficients.iter().enumerate() {
            coeffs[i + shift1] = coeffs[i + shift1] + *c;
        }
        for (i, c) in other.coefficients.iter().enumerate() {
            coeffs[i + shift2] = coeffs[i + shift2] + *c;
        }

        Self {
            coefficients: coeffs,
        }
    }

    /// Multiply by a constant: ρ(t) = c·ρ_x(t)
    pub fn mulc(&self, c: FE) -> Self {
        let coeffs = self.coefficients.iter().map(|x| *x * c).collect();
        Self {
            coefficients: coeffs,
        }
    }

    /// Multiply two commitment polynomials: ρ(t) = ρ_x(t)·ρ_y(t)
    pub fn mul(&self, other: &Self) -> Self {
        let d1 = self.degree();
        let d2 = other.degree();
        let new_degree = d1 + d2;
        let mut coeffs = vec![FE::ZERO; new_degree + 1];

        for (i, a) in self.coefficients.iter().enumerate() {
            for (j, b) in other.coefficients.iter().enumerate() {
                coeffs[i + j] = coeffs[i + j] + *a * *b;
            }
        }

        Self {
            coefficients: coeffs,
        }
    }

    /// Multiply the polynomial by t^shift (shift all coefficients up).
    pub fn shift(&self, shift: usize) -> Self {
        if shift == 0 {
            return self.clone();
        }
        let mut coeffs = vec![FE::ZERO; self.coefficients.len() + shift];
        for (i, c) in self.coefficients.iter().enumerate() {
            coeffs[i + shift] = *c;
        }
        Self {
            coefficients: coeffs,
        }
    }

    /// Multiply the polynomial by a scalar and accumulate into self.
    pub fn add_scaled(&mut self, other: &Self, scalar: FE) {
        if other.coefficients.len() > self.coefficients.len() {
            self.coefficients.resize(other.coefficients.len(), FE::ZERO);
        }
        for (i, c) in other.coefficients.iter().enumerate() {
            self.coefficients[i] = self.coefficients[i] + *c * scalar;
        }
    }
}
