/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Iterated division by `X`

`Polynomial.divX p` drops the constant coefficient of `p` and lowers the remaining degrees by
one. Its `m`-th iterate `divX^[m] p` drops the `m` lowest coefficients and lowers the remaining
degrees by `m`, so that `(divX^[m] p).coeff n = p.coeff (n + m)`. This file records how the
iterate interacts with sums, scalars, multiplication by powers of `X` and reflection, and the
Horner recursion `divX^[m] p = divX^[m + 1] p * X + C (p.coeff m)`, whose values at a point are
the partial Horner sums of `p`. It also records that the iterates commute with coefficient maps,
and that `y * (divX p)(y) = p(y) - p(0)`, in particular for powers `p ^ a`, for which also
`X * divX (p ^ a) = p ^ a - p(0) ^ a`.

In terms of Laurent polynomials, `divX^[m] (Xᵐ * p)` is `p`, while the reflection
`reflect m q = Xᵐ q(X⁻¹)` of a polynomial `q` of degree at most `m` keeps only its constant
term `q(0)` under `divX^[m]`. These identities split a Laurent polynomial, written with
denominator `Xᵐ`, into its parts of positive and of nonpositive degree.
-/

public section

namespace Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- The `m`-th iterate of `divX` lowers the indices of the coefficients by `m`. -/
@[simp]
theorem coeff_iterate_divX (m : ℕ) (p : R[X]) (n : ℕ) :
    (divX^[m] p).coeff n = p.coeff (n + m) := by
  induction m generalizing n with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', coeff_divX, ih, add_right_comm, add_assoc]

/-- The iterates of `divX` are additive. -/
@[simp]
theorem iterate_divX_add (m : ℕ) (p q : R[X]) :
    divX^[m] (p + q) = divX^[m] p + divX^[m] q := by
  ext n
  simp

/-- The iterates of `divX` commute with scalar multiplication. -/
@[simp]
theorem iterate_divX_smul {S : Type*} [SMulZeroClass S R] (m : ℕ) (s : S) (p : R[X]) :
    divX^[m] (s • p) = s • divX^[m] p := by
  ext n
  simp

/-- After multiplication by `Xⁿ`, the `m`-th iterate of `divX` lowers the degrees by `m - n`, or
raises them by `n - m`. -/
theorem iterate_divX_X_pow_mul (m n : ℕ) (p : R[X]) :
    divX^[m] (X ^ n * p) = if m ≤ n then X ^ (n - m) * p else divX^[m - n] p := by
  ext k
  split_ifs with h
  · rw [coeff_iterate_divX, coeff_X_pow_mul', coeff_X_pow_mul']
    split_ifs <;> grind
  · rw [coeff_iterate_divX, coeff_iterate_divX, coeff_X_pow_mul']
    split_ifs <;> grind

/-- The `m`-th iterate of `divX` kills exactly the polynomials of degree less than `m`. -/
theorem iterate_divX_eq_zero_iff {m : ℕ} {p : R[X]} : divX^[m] p = 0 ↔ p.degree < m := by
  rw [degree_lt_iff_coeff_zero]
  refine ⟨fun h N hN ↦ ?_, fun h ↦ ?_⟩
  · rw [← Nat.sub_add_cancel hN, ← coeff_iterate_divX, h, coeff_zero]
  · ext n
    rw [coeff_iterate_divX, coeff_zero, h _ (by omega)]

/-- The `m`-th iterate of `divX` of `p` is the constant polynomial with value the coefficient
of `Xᵐ` exactly when `p` has degree at most `m`. -/
theorem iterate_divX_eq_C_iff {m : ℕ} {p : R[X]} :
    divX^[m] p = C (p.coeff m) ↔ p.natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  refine ⟨fun h N hN ↦ ?_, fun h ↦ ?_⟩
  · rw [← Nat.sub_add_cancel hN.le, ← coeff_iterate_divX, h, coeff_C_of_ne_zero (by omega)]
  · ext n
    rw [coeff_iterate_divX, coeff_C]
    split_ifs with hn
    · rw [hn, zero_add]
    · exact h _ (by omega)

/-- One Horner step for the iterates of `divX`: the `m`-th iterate is recovered from the next
one and the coefficient of `Xᵐ`. -/
theorem iterate_divX_succ_mul_X_add_C (m : ℕ) (p : R[X]) :
    divX^[m + 1] p * X + C (p.coeff m) = divX^[m] p := by
  have h := divX_mul_X_add (divX^[m] p)
  rwa [coeff_iterate_divX, zero_add, ← Function.iterate_succ_apply' divX] at h

/-- The `m`-th iterate of `divX` keeps only the constant coefficient of a polynomial of degree at
most `m` from its reflection `Xᵐ q(X⁻¹)`. -/
theorem iterate_divX_reflect {m : ℕ} {q : R[X]} (hq : q.natDegree ≤ m) :
    divX^[m] (reflect m q) = C (q.coeff 0) := by
  rw [iterate_divX_eq_C_iff.2 (natDegree_reflect_le.trans (max_le le_rfl hq)), coeff_reflect,
    revAt_le le_rfl, tsub_self]

/-- The iterates of `divX` commute with coefficient maps. -/
@[simp]
theorem iterate_divX_map {S : Type*} [Semiring S] (m : ℕ) (p : R[X]) (f : R →+* S) :
    divX^[m] (p.map f) = (divX^[m] p).map f := by
  ext n
  simp

/-- `divX` commutes with coefficient maps. -/
@[simp]
theorem divX_map {S : Type*} [Semiring S] (p : R[X]) (f : R →+* S) :
    divX (p.map f) = (divX p).map f :=
  iterate_divX_map 1 p f

end Semiring

/-- The iterates of `divX` commute with subtraction. -/
@[simp]
theorem iterate_divX_sub [Ring R] (m : ℕ) (p q : R[X]) :
    divX^[m] (p - q) = divX^[m] p - divX^[m] q := by
  ext n
  simp

/-- Multiplying `divX (p ^ a)` by `X` gives `p ^ a - p(0) ^ a`. -/
theorem X_mul_divX_pow [Ring R] (p : R[X]) (a : ℕ) :
    X * divX (p ^ a) = p ^ a - C (p.coeff 0 ^ a) := by
  rw [eq_sub_iff_add_eq, ← constantCoeff_apply, ← map_pow, constantCoeff_apply, X_mul_divX_add]

section Eval₂

variable [Semiring R] {S : Type*} [CommRing S]

/-- Multiplying the value of `divX p` at `y` by `y` recovers the value of `p` at `y` without its
constant term. -/
theorem mul_eval₂_divX (f : R →+* S) (p : R[X]) (y : S) :
    y * (divX p).eval₂ f y = p.eval₂ f y - f (p.coeff 0) := by
  rw [eq_sub_iff_add_eq, mul_comm, ← eval₂_mul_X, ← eval₂_C f y, ← eval₂_add, divX_mul_X_add]

/-- Multiplying the value of `divX (p ^ a)` at `y` by `y` gives `p(y) ^ a - p(0) ^ a`. -/
theorem mul_eval₂_divX_pow (f : R →+* S) (p : R[X]) (a : ℕ) (y : S) :
    y * (divX (p ^ a)).eval₂ f y = p.eval₂ f y ^ a - f (p.coeff 0) ^ a := by
  rw [mul_eval₂_divX, eval₂_pow, ← map_pow, ← constantCoeff_apply, map_pow, constantCoeff_apply]

end Eval₂

end Polynomial
