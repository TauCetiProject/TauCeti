/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangePolynomial.Basic
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Realizing exchange polynomials over semirings

The finite multiplicative coefficient data of an exchange polynomial give an ordinary
polynomial whenever the coefficients admit addition. Its coefficients agree with the stored
ones, and over a nontrivial semiring its degree is exactly the specified degree. Reversal,
dilation and scaling agree with polynomial reflection, substitution and constant multiplication.
Evaluation therefore uses Mathlib's polynomial evaluation, including its functoriality laws.

The specified degree survives arbitrary coefficient maps, including maps to the zero semiring;
the comparison with `natDegree` requires a nontrivial coefficient semiring.

The exchange coefficient conventions follow Nakanishi, *Structure of seeds in generalized
cluster algebras*, Definition 2.2 and (2.5)–(2.6).
-/

public section

namespace TauCeti.ExchangePolynomial

open Polynomial

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The ordinary polynomial whose finite coefficient vector is the exchange polynomial. -/
noncomputable def toPolynomial (H : ExchangePolynomial R) : R[X] := by
  classical
  exact ofFn (H.degree + 1) (fun i => H.coeff i)

/-- Polynomial realization preserves every coefficient, including the zero extension. -/
@[simp] theorem coeff_toPolynomial (H : ExchangePolynomial R) (i : ℕ) :
    H.toPolynomial.coeff i = H.coeff i := by
  classical
  by_cases hi : i < H.degree + 1
  · simp [toPolynomial, hi]
  · simp [toPolynomial, Nat.le_of_not_gt hi, H.coeff_eq_zero i (by omega)]

/-- The polynomial realization has degree bounded by the specified exchange degree. -/
theorem natDegree_toPolynomial_le (H : ExchangePolynomial R) :
    H.toPolynomial.natDegree ≤ H.degree := by
  exact natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
    simpa using H.coeff_eq_zero i hi

/-- Over a nontrivial semiring the unit highest coefficient prevents a degree drop. -/
@[simp] theorem natDegree_toPolynomial [Nontrivial R] (H : ExchangePolynomial R) :
    H.toPolynomial.natDegree = H.degree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_toPolynomial_le H)
  simpa using H.isUnit_last.ne_zero

/-- Exchange polynomial realization is faithful over nontrivial coefficient semirings. -/
theorem toPolynomial_injective [Nontrivial R] :
    Function.Injective (toPolynomial : ExchangePolynomial R → R[X]) := by
  intro H G h
  apply ext
  · simpa using congrArg Polynomial.natDegree h
  · intro i
    simpa using congrArg (fun p : R[X] => p.coeff i) h

/-- Regard a positive-degree polynomial with unit endpoints as exchange data. -/
def _root_.Polynomial.toExchangePolynomial (p : R[X]) (hpos : 0 < p.natDegree)
    (h0 : IsUnit (p.coeff 0)) (hr : IsUnit p.leadingCoeff) : ExchangePolynomial R where
  degree := p.natDegree
  degree_pos := hpos
  coeff := p.coeff
  coeff_eq_zero i hi := coeff_eq_zero_of_natDegree_lt hi
  isUnit_zero := h0
  isUnit_last := by simpa using hr

@[simp] theorem _root_.Polynomial.degree_toExchangePolynomial (p : R[X]) (hpos : 0 < p.natDegree)
    (h0 : IsUnit (p.coeff 0)) (hr : IsUnit p.leadingCoeff) :
    (p.toExchangePolynomial hpos h0 hr).degree = p.natDegree := (rfl)

@[simp] theorem _root_.Polynomial.coeff_toExchangePolynomial (p : R[X]) (hpos : 0 < p.natDegree)
    (h0 : IsUnit (p.coeff 0)) (hr : IsUnit p.leadingCoeff) (i : ℕ) :
    (p.toExchangePolynomial hpos h0 hr).coeff i = p.coeff i := (rfl)

@[simp] theorem _root_.Polynomial.toPolynomial_toExchangePolynomial (p : R[X])
    (hpos : 0 < p.natDegree)
    (h0 : IsUnit (p.coeff 0)) (hr : IsUnit p.leadingCoeff) :
    (p.toExchangePolynomial hpos h0 hr).toPolynomial = p := by
  ext i
  simp

/-- Recover exchange data from their realization with any proofs of the endpoint conditions. -/
@[simp] theorem toExchangePolynomial_toPolynomial [Nontrivial R] (H : ExchangePolynomial R)
    (hpos : 0 < H.toPolynomial.natDegree) (h0 : IsUnit (H.toPolynomial.coeff 0))
    (hr : IsUnit H.toPolynomial.leadingCoeff) :
    H.toPolynomial.toExchangePolynomial hpos h0 hr = H := by
  apply ext <;> simp

/-- Realization commutes with additive as well as multiplicative coefficient maps. -/
@[simp] theorem toPolynomial_map (H : ExchangePolynomial R) (f : R →+* S) :
    (H.map f.toMonoidWithZeroHom).toPolynomial = H.toPolynomial.map f := by
  ext i
  simp

/-- Reversal is reflection at the specified degree, even over the zero semiring. -/
@[simp] theorem toPolynomial_reverse (H : ExchangePolynomial R) :
    H.reverse.toPolynomial = H.toPolynomial.reflect H.degree := by
  ext i
  by_cases hi : i ≤ H.degree
  · simp [coeff_reflect, revAt_le hi, hi]
  · simp [coeff_reflect, revAt_eq_self_of_lt (by omega : H.degree < i), hi,
      H.coeff_eq_zero i (by omega)]

/-- In the nontrivial case reflection agrees with Mathlib's degree-based reversal. -/
theorem toPolynomial_reverse_eq_reverse [Nontrivial R] (H : ExchangePolynomial R) :
    H.reverse.toPolynomial = H.toPolynomial.reverse := by
  simp [Polynomial.reverse]

/-- Unit dilation realizes substitution `T ↦ κ T`. -/
@[simp] theorem toPolynomial_dilate (H : ExchangePolynomial R) (κ : Rˣ) :
    (H.dilate κ).toPolynomial = H.toPolynomial.comp (C (κ : R) * X) := by
  ext i
  simp only [comp_C_mul_X_coeff, coeff_toPolynomial, coeff_dilate]
  exact mul_comm _ _

/-- Unit scaling realizes multiplication by the corresponding constant polynomial. -/
@[simp] theorem toPolynomial_scale (H : ExchangePolynomial R) (e : Rˣ) :
    (H.scale e).toPolynomial = C (e : R) * H.toPolynomial := by
  ext i
  simp [coeff_C_mul]

@[simp] theorem toPolynomial_binary :
    (binary : ExchangePolynomial R).toPolynomial = 1 + X := by
  ext i
  obtain _ | _ | i := i <;> simp [Polynomial.coeff_one, coeff_X]

/-- Evaluation is the finite sum of the realized coefficients times the corresponding powers. -/
theorem eval₂_toPolynomial (H : ExchangePolynomial R) (f : R →+* S) (x : S) :
    H.toPolynomial.eval₂ f x = ∑ i : Fin (H.degree + 1), f (H.coeff i) * x ^ (i : ℕ) := by
  classical
  simp only [toPolynomial, ofFn_eq_sum_monomial, eval₂_finsetSum, eval₂_monomial]

/-- Reversal preserves the sum of the coefficients. -/
theorem eval₂_one_reverse (H : ExchangePolynomial R) (f : R →+* S) :
    H.reverse.toPolynomial.eval₂ f 1 = H.toPolynomial.eval₂ f 1 := by
  let : Invertible (1 : S) := invertibleOne
  simpa using eval₂_reflect_mul_pow f (1 : S) H.degree H.toPolynomial
    (natDegree_toPolynomial_le H)

/-- The reciprocal evaluation identity holds at every unit of the target semiring. -/
theorem eval₂_reverse_mul_pow (H : ExchangePolynomial R) (f : R →+* S) (x : Sˣ) :
    H.reverse.toPolynomial.eval₂ f (↑x⁻¹) * (x : S) ^ H.degree =
      H.toPolynomial.eval₂ f (x : S) := by
  let := x.invertible
  simpa using eval₂_reflect_mul_pow f (x : S) H.degree H.toPolynomial
    (natDegree_toPolynomial_le H)

end TauCeti.ExchangePolynomial
