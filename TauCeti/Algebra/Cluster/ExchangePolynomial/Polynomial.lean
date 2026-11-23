/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangePolynomial.Basic
public import TauCeti.Algebra.Polynomial.Reverse
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

variable {R : Type*} [CommSemiring R]

/-- The ordinary polynomial whose finite coefficient vector is the exchange polynomial. -/
noncomputable def toPolynomial (H : ExchangePolynomial R) : R[X] := by
  classical
  exact ofFn (H.degree + 1) (fun i => H.coeff i)

/-- Polynomial realization preserves every coefficient, including the zero extension. -/
@[simp↓] theorem coeff_toPolynomial (H : ExchangePolynomial R) (i : ℕ) :
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
@[simp↓] theorem natDegree_toPolynomial [Nontrivial R] (H : ExchangePolynomial R) :
    H.toPolynomial.natDegree = H.degree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_toPolynomial_le H)
  simp

/-- Polynomial realization has degree bounded by the specified exchange degree. -/
theorem degree_toPolynomial_le (H : ExchangePolynomial R) :
    H.toPolynomial.degree ≤ H.degree := by
  exact (degree_le_natDegree).trans (Nat.cast_le.mpr (natDegree_toPolynomial_le H))

/-- The unit leading coefficient supplies the polynomial's leading coefficient. -/
@[simp↓] theorem leadingCoeff_toPolynomial (H : ExchangePolynomial R) :
    H.toPolynomial.leadingCoeff = H.coeff H.degree := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  rw [← coeff_natDegree, natDegree_toPolynomial, coeff_toPolynomial]

/-- Over a nontrivial semiring the specified degree is the polynomial degree. -/
@[simp↓] theorem degree_toPolynomial [Nontrivial R] (H : ExchangePolynomial R) :
    H.toPolynomial.degree = H.degree := by
  exact degree_eq_iff_natDegree_eq_of_pos H.degree_pos |>.mpr
    (natDegree_toPolynomial H)

/-- Realization is nonzero over a nontrivial coefficient semiring. -/
@[simp↓] theorem toPolynomial_ne_zero [Nontrivial R] (H : ExchangePolynomial R) :
    H.toPolynomial ≠ 0 := by
  apply leadingCoeff_ne_zero.mp
  simp

/-- Exchange polynomial realization is faithful over nontrivial coefficient semirings. -/
theorem toPolynomial_injective [Nontrivial R] :
    Function.Injective (toPolynomial : ExchangePolynomial R → R[X]) := by
  intro H G h
  apply ext
  · simpa using congrArg Polynomial.natDegree h
  · intro i _hi
    simpa using congrArg (fun p : R[X] => p.coeff i) h

/-- Polynomial realizations agree exactly when the exchange polynomials do. -/
@[simp↓] theorem toPolynomial_inj [Nontrivial R] {H G : ExchangePolynomial R} :
    H.toPolynomial = G.toPolynomial ↔ H = G :=
  toPolynomial_injective.eq_iff

/-- Regard a positive-degree polynomial with unit endpoints as exchange data. -/
def _root_.Polynomial.toExchangePolynomial (p : R[X]) (hpos : 0 < p.natDegree)
    (h0 : IsUnit (p.coeff 0)) (hr : IsUnit p.leadingCoeff) : ExchangePolynomial R where
  degree := p.natDegree
  degree_pos := hpos
  coeff := p.coeff
  coeff_eq_zero i hi := coeff_eq_zero_of_natDegree_lt hi
  isUnit_coeff_zero := h0
  isUnit_coeff_degree := by simpa using hr

@[simp] theorem _root_.Polynomial.degree_toExchangePolynomial (p : R[X]) (hpos : 0 < p.natDegree)
    (h0 : IsUnit (p.coeff 0)) (hr : IsUnit p.leadingCoeff) :
    (p.toExchangePolynomial hpos h0 hr).degree = p.natDegree := (rfl)

@[simp] theorem _root_.Polynomial.coeff_toExchangePolynomial (p : R[X]) (hpos : 0 < p.natDegree)
    (h0 : IsUnit (p.coeff 0)) (hr : IsUnit p.leadingCoeff) (i : ℕ) :
    (p.toExchangePolynomial hpos h0 hr).coeff i = p.coeff i := (rfl)

@[simp] theorem _root_.Polynomial.constantUnit_toExchangePolynomial (p : R[X])
    (hpos : 0 < p.natDegree) (h0 : IsUnit (p.coeff 0)) (hr : IsUnit p.leadingCoeff) :
    (p.toExchangePolynomial hpos h0 hr).constantUnit = h0.unit :=
  Units.ext (by simp)

@[simp] theorem _root_.Polynomial.leadingUnit_toExchangePolynomial (p : R[X])
    (hpos : 0 < p.natDegree) (h0 : IsUnit (p.coeff 0)) (hr : IsUnit p.leadingCoeff) :
    (p.toExchangePolynomial hpos h0 hr).leadingUnit = hr.unit :=
  Units.ext (by simp only [TauCeti.ExchangePolynomial.coe_leadingUnit,
    degree_toExchangePolynomial, coeff_toExchangePolynomial, Polynomial.leadingCoeff,
    IsUnit.unit_spec])

@[simp] theorem _root_.Polynomial.toPolynomial_toExchangePolynomial (p : R[X])
    (hpos : 0 < p.natDegree)
    (h0 : IsUnit (p.coeff 0)) (hr : IsUnit p.leadingCoeff) :
    (p.toExchangePolynomial hpos h0 hr).toPolynomial = p := by
  ext i
  simp

/-- Two polynomials give the same exchange polynomial exactly when they are equal. -/
@[simp] theorem _root_.Polynomial.toExchangePolynomial_inj {p q : R[X]} {hp : 0 < p.natDegree}
    {hq : 0 < q.natDegree} {hp0 : IsUnit (p.coeff 0)} {hq0 : IsUnit (q.coeff 0)}
    {hpr : IsUnit p.leadingCoeff} {hqr : IsUnit q.leadingCoeff} :
    p.toExchangePolynomial hp hp0 hpr = q.toExchangePolynomial hq hq0 hqr ↔ p = q := by
  constructor
  · intro h
    simpa using congrArg toPolynomial h
  · rintro rfl
    rfl

/-- Recover an exchange polynomial from its realization, given any proofs of positive degree
`0 < H.toPolynomial.natDegree` and of the unit endpoint conditions. -/
@[simp↓] theorem toExchangePolynomial_toPolynomial (H : ExchangePolynomial R)
    (hpos : 0 < H.toPolynomial.natDegree) (h0 : IsUnit (H.toPolynomial.coeff 0))
    (hr : IsUnit H.toPolynomial.leadingCoeff) :
    H.toPolynomial.toExchangePolynomial hpos h0 hr = H := by
  have : Nontrivial R := Polynomial.Nontrivial.of_polynomial_ne (p := H.toPolynomial) (q := 0)
    fun h => by simp [h] at hpos
  apply ext <;> simp

section Map

variable {S : Type*} [CommSemiring S]

/-- Realization commutes with semiring homomorphisms on coefficients. -/
@[simp] theorem toPolynomial_map (H : ExchangePolynomial R) (f : R →+* S) :
    (H.map f.toMonoidWithZeroHom).toPolynomial = H.toPolynomial.map f := by
  ext i
  simp

end Map

/-- Reversal is reflection at the specified degree, even over the zero semiring. -/
@[simp] theorem toPolynomial_reverse (H : ExchangePolynomial R) :
    H.reverse.toPolynomial = H.toPolynomial.reflect H.degree := by
  ext i
  by_cases hi : i ≤ H.degree
  · simp [coeff_reflect, revAt_le hi, hi]
  · simp [coeff_reflect, revAt_eq_self_of_lt (by omega : H.degree < i), hi,
      H.coeff_eq_zero i (by omega)]

/-- Realizing an exchange polynomial reversal agrees with `Polynomial.reverse`, including over
 the zero semiring. -/
theorem toPolynomial_reverse_eq_reverse (H : ExchangePolynomial R) :
    H.reverse.toPolynomial = H.toPolynomial.reverse := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  simp only [toPolynomial_reverse, Polynomial.reverse, natDegree_toPolynomial]

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

@[simp] theorem toPolynomial_binomial (y : Rˣ) :
    (binomial y).toPolynomial = 1 + C (y : R) * X := by
  ext i
  obtain _ | _ | i := i <;> simp [coeff_binomial, Polynomial.coeff_one, coeff_X]

variable {S : Type*} [Semiring S]

/-- The reciprocal evaluation identity holds at every unit of the target semiring. -/
theorem eval₂_toPolynomial_reverse_mul_pow (H : ExchangePolynomial R) (f : R →+* S)
    (x : Sˣ) :
    H.reverse.toPolynomial.eval₂ f (↑x⁻¹) * (x : S) ^ H.degree =
      H.toPolynomial.eval₂ f (x : S) := by
  simpa only [toPolynomial_reverse, invOf_units] using
    H.toPolynomial.eval₂_reflect_mul_pow' f (x : S) H.natDegree_toPolynomial_le

/-- Evaluation is the finite sum of the realized coefficients times the corresponding powers. -/
theorem eval₂_toPolynomial (H : ExchangePolynomial R) (f : R →+* S) (x : S) :
    H.toPolynomial.eval₂ f x = ∑ i : Fin (H.degree + 1), f (H.coeff i) * x ^ (i : ℕ) := by
  classical
  simp only [toPolynomial, ofFn_eq_sum_monomial, eval₂_finsetSum, eval₂_monomial]

/-- The realized polynomial has evaluation equal to the finite coefficient sum. -/
theorem eval_toPolynomial (H : ExchangePolynomial R) (x : R) :
    H.toPolynomial.eval x = ∑ i : Fin (H.degree + 1), H.coeff i * x ^ (i : ℕ) := by
  simpa using H.eval₂_toPolynomial (.id R) x

/-- The reciprocal identity for polynomial evaluation holds at every coefficient unit. -/
theorem eval_toPolynomial_reverse_mul_pow (H : ExchangePolynomial R) (x : Rˣ) :
    H.reverse.toPolynomial.eval (↑x⁻¹) * (x : R) ^ H.degree = H.toPolynomial.eval (x : R) := by
  simpa using H.eval₂_toPolynomial_reverse_mul_pow (.id R) x

/-- In a nontrivial semiring in which sums vanish only when every summand does, an exchange
polynomial does not vanish anywhere: its constant term is a unit. -/
theorem eval_toPolynomial_ne_zero [Nontrivial R] [Subsingleton (AddUnits R)]
    (H : ExchangePolynomial R) (x : R) : H.toPolynomial.eval x ≠ 0 := by
  rw [eval_toPolynomial, Ne, Finset.sum_eq_zero_iff]
  intro h
  simpa using h 0 (Finset.mem_univ _)

end TauCeti.ExchangePolynomial
