/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
public import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.Algebra.Squarefree

/-!
# Polynomials of degree three and four

Splitting criteria for low-degree polynomials and a separability criterion, all read off the
coefficients.

* Away from characteristic two, a cubic that already has one root splits exactly when its
  discriminant is a square: the root splits off a quadratic factor whose discriminant differs from
  that of the cubic by a square, and a quadratic splits exactly when its discriminant is a square.
  Normalization by the leading coefficient reduces the statement to the monic case.
* A cubic with two distinct roots in its coefficient field splits there, and conversely a
  separable split polynomial of degree at least two has two distinct roots.
* An irreducible polynomial is separable as soon as its degree is nonzero in the coefficient
  field, which for a quartic is exactly what characteristic `≠ 2` gives.
* A monic quadratic `X² + aX + b` divides a depressed quartic `X⁴ + pX² + qX + r` exactly when
  the two coefficients of the remainder of the division vanish. Over `ℤ` this reduces the search
  for a quadratic factor of an explicit quartic to two Diophantine equations, which a reduction
  modulo a small prime can rule out.

Together these turn the single test "the resolvent cubic of a quartic has a root in the base
field" into the classical resolvent conditions — irreducible, splits completely, exactly one root
— used by the quartic label table of `TauCeti.FieldTheory.GaloisGroups.Quartic.Basic`.

## Main results

* `Polynomial.Irreducible.separable_of_natDegree_cast_ne_zero` and
  `Polynomial.separable_of_irreducible_of_natDegree_eq_four`
* `Polynomial.exists_natDegree_eq_two_of_natDegree_eq_three_of_isRoot`
* `Polynomial.splits_iff_isSquare_discr_of_natDegree_eq_two` and
  `Polynomial.splits_iff_isSquare_discr_of_natDegree_eq_three_of_isRoot`
* `Polynomial.Splits.of_natDegree_eq_three_of_isRoot_of_isRoot_of_ne` and
  `Polynomial.Splits.exists_isRoot_ne`
* `Polynomial.X_sq_add_C_mul_X_add_C_dvd_X_pow_four_add_iff`: when a monic quadratic divides a
  depressed quartic, by explicit division with remainder
-/

public section

open Polynomial

namespace Polynomial

variable {F : Type*} [Field F]

/-- An irreducible polynomial whose degree is nonzero in the coefficient field is separable: the
derivative then has the nonzero leading coefficient `natDegree • leadingCoeff`. -/
theorem Irreducible.separable_of_natDegree_cast_ne_zero {f : F[X]} (hirr : Irreducible f)
    (hdeg : (f.natDegree : F) ≠ 0) : f.Separable := by
  have hpos : 0 < f.natDegree := Nat.pos_of_ne_zero fun h0 => hdeg (by rw [h0]; simp)
  have hsucc : f.natDegree - 1 + 1 = f.natDegree := Nat.succ_pred_eq_of_pos hpos
  have hcast : ((f.natDegree - 1 : ℕ) : F) + 1 = (f.natDegree : F) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → F) hsucc
  rw [separable_iff_derivative_ne_zero hirr]
  intro hder
  have hcoeff := congrArg (fun p : F[X] => p.coeff (f.natDegree - 1)) hder
  rw [coeff_derivative, coeff_zero, hcast, hsucc, coeff_natDegree] at hcoeff
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hirr.ne_zero) hdeg hcoeff

/-- An irreducible quartic is separable away from characteristic two. -/
theorem separable_of_irreducible_of_natDegree_eq_four {f : F[X]} (hchar : ringChar F ≠ 2)
    (hirr : Irreducible f) (hdeg : f.natDegree = 4) : f.Separable := by
  refine hirr.separable_of_natDegree_cast_ne_zero ?_
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  have hfour : ((4 : ℕ) : F) = 2 * 2 := by norm_num
  rw [hdeg, hfour]
  exact mul_ne_zero htwo htwo

/-- A cubic with a root `a` in its coefficient field is `(X - a)` times a quadratic. This is the
one factorization step shared by the two splitting criteria below. -/
theorem exists_natDegree_eq_two_of_natDegree_eq_three_of_isRoot {g : F[X]}
    (hdeg : g.natDegree = 3) {a : F} (ha : g.IsRoot a) :
    ∃ q : F[X], q.natDegree = 2 ∧ g = (X - C a) * q := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.2 ha
  have hg0 : g ≠ 0 := fun h0 => by simp [h0] at hdeg
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hg0 hq
  refine ⟨q, ?_, hq⟩
  rw [hq, natDegree_mul (X_sub_C_ne_zero a) hq0, natDegree_X_sub_C] at hdeg
  omega

/-- Away from characteristic two, a quadratic splits over its coefficient field exactly when its
discriminant is a square. This is `Polynomial.splits_quadratic_iff_isSquare` read on `discr`
rather than on a coefficient triple. -/
theorem splits_iff_isSquare_discr_of_natDegree_eq_two {q : F[X]} (hchar : ringChar F ≠ 2)
    (hdeg : q.natDegree = 2) : q.Splits ↔ IsSquare q.discr := by
  have : NeZero (2 : F) := ⟨Ring.two_ne_zero hchar⟩
  have hq0 : q ≠ 0 := fun h0 => by simp [h0] at hdeg
  have hdeg2 : q.degree = 2 := by
    rw [← Nat.cast_two, degree_eq_iff_natDegree_eq_of_pos two_pos]
    exact hdeg
  have hlc : q.coeff 2 ≠ 0 := by
    rw [← hdeg, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hq0
  have hdiscr : q.discr = discrim (q.coeff 2) (q.coeff 1) (q.coeff 0) := by
    rw [discr_of_degree_eq_two hdeg2]
    simp only [discrim]
    ring
  rw [hdiscr]
  conv_lhs => rw [eq_quadratic_of_degree_le_two hdeg2.le]
  exact splits_quadratic_iff_isSquare hlc

/-- **Away from characteristic two, a monic cubic with a root in its coefficient field splits
there exactly when its discriminant is a square.** The root splits off a quadratic factor whose
discriminant differs from that of the cubic by the square of the value of the factor at the
root. -/
private theorem Monic.splits_iff_isSquare_discr_of_natDegree_eq_three_of_isRoot {g : F[X]}
    (hg : g.Monic)
    (hdeg : g.natDegree = 3) (hchar : ringChar F ≠ 2) {a : F} (ha : g.IsRoot a) :
    g.Splits ↔ IsSquare g.discr := by
  obtain ⟨q, hqdeg, hfactor⟩ :=
    exists_natDegree_eq_two_of_natDegree_eq_three_of_isRoot hdeg ha
  have hqm : q.Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [← hfactor]; exact hg)
  have hquad := splits_iff_isSquare_discr_of_natDegree_eq_two hchar hqdeg
  have hres : (X - C a).resultant q = q.eval a := by
    rw [natDegree_X_sub_C]
    exact resultant_X_sub_C_left q q.natDegree a le_rfl
  have hdiscr : g.discr = q.discr * q.eval a ^ 2 := by
    rw [hfactor, (monic_X_sub_C a).discr_mul hqm, discr_of_degree_eq_one (degree_X_sub_C a),
      one_mul, hres]
  have hsplit : g.Splits ↔ q.Splits := by
    rw [hfactor, splits_mul_iff_right (X_sub_C_ne_zero a) (Splits.X_sub_C a)]
  rw [hsplit, hdiscr]
  refine ⟨fun h => (hquad.1 h).mul (Even.isSquare_pow even_two _), fun h => ?_⟩
  by_cases hr : q.eval a = 0
  · exact Splits.of_natDegree_eq_two hqdeg hr
  · exact hquad.2 ((isSquare_mul_sq_iff hr).mp h)

/-- **Away from characteristic two, a cubic with a root in its coefficient field splits there
exactly when its discriminant is a square.** Multiplication by the inverse leading coefficient
reduces to the monic criterion, and changes the discriminant by a nonzero fourth power. -/
theorem splits_iff_isSquare_discr_of_natDegree_eq_three_of_isRoot {g : F[X]}
    (hdeg : g.natDegree = 3) (hchar : ringChar F ≠ 2) {a : F} (ha : g.IsRoot a) :
    g.Splits ↔ IsSquare g.discr := by
  have hg0 : g ≠ 0 := fun h0 => by simp [h0] at hdeg
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  let g' := C g.leadingCoeff⁻¹ * g
  have hg'monic : g'.Monic := by
    dsimp [g']
    rw [mul_comm]
    exact monic_mul_leadingCoeff_inv hg0
  have hg'deg : g'.natDegree = 3 := by
    dsimp [g']
    rw [natDegree_C_mul (inv_ne_zero hlc), hdeg]
  have hg'root : g'.IsRoot a := by
    dsimp [g', IsRoot]
    rw [eval_mul, eval_C, ha, mul_zero]
  have hcriterion := hg'monic.splits_iff_isSquare_discr_of_natDegree_eq_three_of_isRoot
    hg'deg hchar hg'root
  have hscale : C g.leadingCoeff * g' = g := by
    dsimp [g']
    rw [← mul_assoc, ← C_mul]
    simp [hlc]
  have hsplits : g.Splits ↔ g'.Splits := by
    refine ⟨fun h => h.C_mul g.leadingCoeff⁻¹, fun h => ?_⟩
    rw [← hscale]
    exact h.C_mul g.leadingCoeff
  have hdiscr : g'.discr = g.discr * (g.leadingCoeff⁻¹ ^ 2) ^ 2 := by
    dsimp [g']
    rw [TauCeti.discr_C_mul _ (inv_ne_zero hlc), hdeg]
    norm_num
    ring
  rw [hsplits, hcriterion, hdiscr]
  exact ⟨(isSquare_mul_sq_iff (pow_ne_zero 2 (inv_ne_zero hlc))).mp,
    fun h => h.mul (Even.isSquare_pow even_two _)⟩

/-- A cubic with two distinct roots in its coefficient field splits there. -/
theorem Splits.of_natDegree_eq_three_of_isRoot_of_isRoot_of_ne {g : F[X]} (hdeg : g.natDegree = 3)
    {a x : F} (ha : g.IsRoot a) (hx : g.IsRoot x) (hxa : x ≠ a) : g.Splits := by
  obtain ⟨q, hqdeg, hfactor⟩ :=
    exists_natDegree_eq_two_of_natDegree_eq_three_of_isRoot hdeg ha
  have hq0 : q ≠ 0 := fun h0 => by simp [h0] at hqdeg
  have hqx : q.eval x = 0 := by
    rw [hfactor, IsRoot, eval_mul, eval_sub, eval_X, eval_C] at hx
    exact (mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr hxa)
  rw [hfactor, splits_mul (X_sub_C_ne_zero a) hq0]
  exact ⟨Splits.X_sub_C a, Splits.of_natDegree_eq_two hqdeg hqx⟩

/-- **A separable split polynomial of degree at least two has a root away from any given
element.** This is the converse of
`Polynomial.Splits.of_natDegree_eq_three_of_isRoot_of_isRoot_of_ne` in the form the uniqueness of
a root is used: a split separable polynomial has as many roots as its degree. -/
theorem Splits.exists_isRoot_ne {g : F[X]} (hsplit : g.Splits) (hsep : g.Separable)
    (hdeg : 2 ≤ g.natDegree) (a : F) : ∃ x, g.IsRoot x ∧ x ≠ a := by
  have hg0 : g ≠ 0 := fun h0 => by simp [h0] at hdeg
  have hmap : (g.map (algebraMap F F)).Splits := by simpa using hsplit
  have hcard : Fintype.card (g.rootSet F) = g.natDegree := card_rootSet_eq_natDegree hsep hmap
  have hroot : ∀ z : g.rootSet F, g.IsRoot (z : F) := fun z => by
    simpa [IsRoot] using (mem_rootSet_of_ne (S := F) hg0).mp z.2
  have hone : 1 < Fintype.card (g.rootSet F) := by omega
  obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp hone
  by_cases hxa : (x : F) = a
  · exact ⟨y, hroot y, fun hya => hxy (Subtype.ext (hxa.trans hya.symm))⟩
  · exact ⟨x, hroot x, hxa⟩

section CommRing

variable {R : Type*} [CommRing R]

/-- **Division of a depressed quartic by a monic quadratic.** The monic quadratic `X² + aX + b`
divides the depressed quartic `X⁴ + pX² + qX + r` exactly when the linear remainder of the
division vanishes, that is when `q = a³ - 2ab + ap` and `r = a²b - b² + bp`. The quotient is
`X² - aX + (a² - b + p)`. Over the zero ring both sides hold trivially. -/
theorem X_sq_add_C_mul_X_add_C_dvd_X_pow_four_add_iff (a b p q r : R) :
    X ^ 2 + C a * X + C b ∣ X ^ 4 + C p * X ^ 2 + C q * X + C r ↔
      q = a ^ 3 - 2 * a * b + a * p ∧ r = a ^ 2 * b - b ^ 2 + b * p := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact iff_of_true ⟨1, Subsingleton.elim _ _⟩ ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hdiv : (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]) =
      (X ^ 2 + C a * X + C b) * (X ^ 2 - C a * X + C (a ^ 2 - b + p)) +
        (C (q - a ^ 3 + 2 * a * b - a * p) * X + C (r - a ^ 2 * b + b ^ 2 - b * p)) := by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    ring
  constructor
  · intro hdvd
    have hrem : X ^ 2 + C a * X + C b ∣
        C (q - a ^ 3 + 2 * a * b - a * p) * X + C (r - a ^ 2 * b + b ^ 2 - b * p) := by
      have := dvd_sub hdvd
        (dvd_mul_right (X ^ 2 + C a * X + C b) (X ^ 2 - C a * X + C (a ^ 2 - b + p)))
      rwa [hdiv, add_sub_cancel_left] at this
    have hmonic : (X ^ 2 + C a * X + C b : R[X]).Monic := by monicity!
    have hzero :
        C (q - a ^ 3 + 2 * a * b - a * p) * X + C (r - a ^ 2 * b + b ^ 2 - b * p) = 0 := by
      by_contra hne
      refine hmonic.not_dvd_of_natDegree_lt hne ?_ hrem
      calc (C (q - a ^ 3 + 2 * a * b - a * p) * X + C (r - a ^ 2 * b + b ^ 2 - b * p)).natDegree
          ≤ 1 := by compute_degree
        _ < 2 := one_lt_two
        _ = (X ^ 2 + C a * X + C b : R[X]).natDegree := by symm; compute_degree!
    have h1 := congrArg (fun g : R[X] => g.coeff 1) hzero
    have h0 := congrArg (fun g : R[X] => g.coeff 0) hzero
    simp only [coeff_add, coeff_C_mul_X, coeff_C, coeff_zero, one_ne_zero, zero_ne_one,
      ite_true, ite_false, add_zero, zero_add] at h1 h0
    exact ⟨by linear_combination h1, by linear_combination h0⟩
  · rintro ⟨hq, hr⟩
    refine ⟨X ^ 2 - C a * X + C (a ^ 2 - b + p), ?_⟩
    have hc1 : q - a ^ 3 + 2 * a * b - a * p = 0 := by rw [hq]; ring
    have hc0 : r - a ^ 2 * b + b ^ 2 - b * p = 0 := by rw [hr]; ring
    rw [hdiv, hc1, hc0, C_0, zero_mul, zero_add, add_zero]

end CommRing

end Polynomial
