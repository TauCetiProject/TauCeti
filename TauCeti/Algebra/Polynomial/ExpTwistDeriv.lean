/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative

/-!
# The exponentially twisted derivative of a polynomial

Over a commutative semiring `R`, for `c : R` and `m : ℕ`, the linear map
`Polynomial.expTwistDeriv c m = (d/dX + c) ^ m` on `R[X]` records how differentiation acts on an
exponential polynomial `P(X) e^{cX}`: formally, `d/dX (P e^{cX}) = (P' + c P) e^{cX}`, so the `m`-th
derivative of `P e^{cX}` is `expTwistDeriv c m P · e^{cX}`. The power-series form of this identity
is `PowerSeries.iterate_derivative_coe_mul_rescale_exp`.

Since `d/dX` commutes with multiplication by the constant `c`, the binomial theorem expands the
operator as `∑_{j ≤ m} C(m, j) c^{m - j} P^{(j)}` (`Polynomial.expTwistDeriv_eq_sum`). In
particular `expTwistDeriv c m` never raises the degree (`Polynomial.natDegree_expTwistDeriv_le`),
and it is the `m`-th iterate of `q ↦ q' + c q` (`Polynomial.expTwistDeriv_eq_iterate`), whose
degree and kernel are described by `Polynomial.natDegree_iterate_derivative_add_C_mul` and
`Polynomial.iterate_derivative_add_C_mul_eq_zero_iff` when `c ≠ 0`.

Auxiliary functions in the method of linear forms in logarithms are sums of terms
`P(X) e^{ψ X}`; their derivatives of every order are again of this shape, with the polynomial
factors transformed by `expTwistDeriv ψ m`.

## Main definitions

* `Polynomial.expTwistDeriv c m`: the linear map `(d/dX + c) ^ m` on `R[X]`.

## Main results

* `Polynomial.expTwistDeriv_zero`, `Polynomial.expTwistDeriv_succ`: the recursion
  `E_{c, 0} P = P` and `E_{c, m + 1} P = (E_{c, m} P)' + c E_{c, m} P`.
* `Polynomial.expTwistDeriv_eq_iterate`: `expTwistDeriv c m` is the `m`-th iterate of
  `q ↦ q' + c q`.
* `Polynomial.expTwistDeriv_eq_sum`: the binomial form `∑_{j ≤ m} C(m, j) c^{m - j} P^{(j)}`.
* `Polynomial.expTwistDeriv_C`, `Polynomial.expTwistDeriv_one`: on constants,
  `E_{c, m} (C a) = C (c ^ m * a)`; in particular `E_{c, m} 1 = C (c ^ m)`.
* `Polynomial.natDegree_expTwistDeriv_le`: `expTwistDeriv c m` does not raise the degree.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press (1975), Chapter 2.
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- The **exponentially twisted derivative** `(d/dX + c) ^ m` on `R[X]`. It describes the `m`-th
derivative of an exponential polynomial: `(P e^{cX})^{(m)} = (expTwistDeriv c m P) e^{cX}`. -/
noncomputable def expTwistDeriv (c : R) (m : ℕ) : R[X] →ₗ[R] R[X] :=
  (derivative + c • 1) ^ m

/-- The twisted derivative of order zero is the identity. -/
@[simp]
theorem expTwistDeriv_zero (c : R) (P : R[X]) : expTwistDeriv c 0 P = P := by
  simp [expTwistDeriv]

/-- The recursion for the twisted derivative: `E_{c, m + 1} P = (E_{c, m} P)' + c E_{c, m} P`. -/
theorem expTwistDeriv_succ (c : R) (m : ℕ) (P : R[X]) :
    expTwistDeriv c (m + 1) P = derivative (expTwistDeriv c m P) + c • expTwistDeriv c m P := by
  simp [expTwistDeriv, pow_succ']

/-- The twisted derivative of order `m` is the `m`-th iterate of `q ↦ q' + c q`. -/
theorem expTwistDeriv_eq_iterate (c : R) (m : ℕ) :
    ⇑(expTwistDeriv c m) = (fun q ↦ derivative q + C c * q)^[m] := by
  funext P
  induction m with
  | zero => simp
  | succ m ih => rw [expTwistDeriv_succ, Function.iterate_succ_apply', ← ih, smul_eq_C_mul]

/-- The binomial form of the twisted derivative,
`E_{c, m} P = ∑_{j ≤ m} C(m, j) c^{m - j} P^{(j)}`. -/
theorem expTwistDeriv_eq_sum (c : R) (m : ℕ) (P : R[X]) :
    expTwistDeriv c m P =
      ∑ j ∈ range (m + 1), ((m.choose j : R) * c ^ (m - j)) • derivative^[j] P := by
  have hcomm : Commute (derivative : Module.End R R[X]) (c • 1) :=
    (Commute.one_right _).smul_right c
  rw [expTwistDeriv, hcomm.add_pow, LinearMap.sum_apply]
  refine sum_congr rfl fun j _ ↦ ?_
  simp only [smul_pow, one_pow, mul_apply_eq_comp, natCast_apply_eq_smul, LinearMap.smul_apply,
    one_apply_eq_self, pow_apply_eq_iterate, map_smul, ← Nat.cast_smul_eq_nsmul R, smul_smul]

/-- On a constant polynomial, `E_{c, m} (C a) = C (c ^ m * a)`. -/
@[simp]
theorem expTwistDeriv_C (c : R) (m : ℕ) (a : R) : expTwistDeriv c m (C a) = C (c ^ m * a) := by
  induction m with
  | zero => simp
  | succ m ih => rw [expTwistDeriv_succ, ih, derivative_C, zero_add, smul_C, smul_eq_mul, pow_succ',
      mul_assoc]

/-- On the constant polynomial `1`, `E_{c, m} 1 = C (c ^ m)`. -/
@[simp]
theorem expTwistDeriv_one (c : R) (m : ℕ) : expTwistDeriv c m 1 = C (c ^ m) := by
  simpa using expTwistDeriv_C c m 1

/-- The twisted derivative does not raise the degree of a polynomial. -/
theorem natDegree_expTwistDeriv_le (c : R) (m : ℕ) (P : R[X]) :
    (expTwistDeriv c m P).natDegree ≤ P.natDegree := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [expTwistDeriv_succ]
    refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_smul_le _ _).trans ih))
    exact (natDegree_derivative_le _).trans (Nat.sub_le_of_le_add (ih.trans (Nat.le_add_right _ _)))

end Polynomial
