/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Polynomials of degree three and four

This file supplies splitting and irreducibility criteria for cubics, together with a
separability criterion for irreducible quartics away from characteristic two.

## Main results

* `Polynomial.separable_of_irreducible_of_natDegree_eq_four`
* `Polynomial.splits_iff_isSquare_discr_of_isRoot_of_monic_cubic`
* `Polynomial.Splits.of_natDegree_eq_three_of_two_isRoot`
* `Polynomial.Monic.irreducible_iff_not_exists_isRoot_of_natDegree_eq_three`
-/

public section

open Polynomial

namespace Polynomial

variable {F : Type*} [Field F]

/-- An irreducible quartic is separable away from characteristic two. -/
theorem separable_of_irreducible_of_natDegree_eq_four {f : F[X]} (hchar : ringChar F ≠ 2)
    (hirr : Irreducible f) (hdeg : f.natDegree = 4) : f.Separable := by
  rw [separable_iff_derivative_ne_zero hirr]
  intro hder
  have hcoeff := congrArg (fun p : F[X] => p.coeff 3) hder
  rw [coeff_derivative, coeff_zero] at hcoeff
  norm_num at hcoeff
  rw [← hdeg, coeff_natDegree] at hcoeff
  rcases hcoeff with h | h
  · exact (leadingCoeff_ne_zero.mpr hirr.ne_zero) h
  · have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    have hfour : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num]
      exact mul_ne_zero htwo htwo
    exact hfour h

private theorem cubic_discr_factor (a b c : F) :
    Cubic.discr ⟨1, b, c, -(a ^ 3 + b * a ^ 2 + c * a)⟩ =
      discrim 1 (b + a) (c + b * a + a ^ 2) *
        (a ^ 2 + (b + a) * a + (c + b * a + a ^ 2)) ^ 2 := by
  simp only [Cubic.discr, discrim]
  ring

private theorem splits_iff_isSquare_discr_of_isRoot_of_eq_cubic {g : F[X]}
    (hchar : ringChar F ≠ 2) (b c d a : F) (hg : g = Cubic.toPoly ⟨1, b, c, d⟩)
    (hsep : g.Separable) (ha : g.IsRoot a) : g.Splits ↔ IsSquare g.discr := by
  have hroot : a ^ 3 + b * a ^ 2 + c * a + d = 0 := by
    rw [IsRoot, hg] at ha
    simpa only [Cubic.toPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X, one_mul] using ha
  have hd : d = -(a ^ 3 + b * a ^ 2 + c * a) := by linear_combination hroot
  have hfactor : g = (X - C a) *
      (X ^ 2 + C (b + a) * X + C (c + b * a + a ^ 2)) := by
    rw [hg, hd]
    simp only [Cubic.toPoly, C_add, C_neg, C_mul, C_pow, C_1, one_mul]
    ring
  have hdisc : g.discr = discrim 1 (b + a) (c + b * a + a ^ 2) *
      (a ^ 2 + (b + a) * a + (c + b * a + a ^ 2)) ^ 2 := by
    rw [hg, hd, Cubic.toPoly_discr one_ne_zero, cubic_discr_factor]
  have hqsplit : (X ^ 2 + C (b + a) * X + C (c + b * a + a ^ 2) : F[X]).Splits ↔
      IsSquare (discrim 1 (b + a) (c + b * a + a ^ 2)) := by
    simpa only [C_1, one_mul] using
      (@splits_quadratic_iff_isSquare F _ ⟨Ring.two_ne_zero hchar⟩ 1 (b + a)
        (c + b * a + a ^ 2) one_ne_zero)
  have hsplit : g.Splits ↔
      (X ^ 2 + C (b + a) * X + C (c + b * a + a ^ 2) : F[X]).Splits := by
    rw [hfactor, splits_mul_iff_right (X_sub_C_ne_zero a) (Splits.X_sub_C a)]
  rw [hsplit, hqsplit]
  constructor
  · intro hsq
    rw [hdisc]
    exact hsq.mul (Even.isSquare_pow (by simp) _)
  · intro hsq
    have hgmonic : g.Monic := hg ▸ Cubic.monic_of_a_eq_one' (b := b) (c := c) (d := d)
    have hdiscne : g.discr ≠ 0 := hgmonic.discr_ne_zero_iff.2 hsep
    have hr : a ^ 2 + (b + a) * a + (c + b * a + a ^ 2) ≠ 0 := by
      intro hr
      apply hdiscne
      rw [hdisc, hr]
      simp
    have hquot := hsq.div (Even.isSquare_pow even_two (a ^ 2 + (b + a) * a +
      (c + b * a + a ^ 2)))
    rw [hdisc] at hquot
    have heq : discrim 1 (b + a) (c + b * a + a ^ 2) =
        discrim 1 (b + a) (c + b * a + a ^ 2) *
          (a ^ 2 + (b + a) * a + (c + b * a + a ^ 2)) ^ 2 /
            (a ^ 2 + (b + a) * a + (c + b * a + a ^ 2)) ^ 2 := by
      exact (mul_div_cancel_right₀ _ (pow_ne_zero 2 hr)).symm
    rw [heq]
    exact hquot

/-- A separable monic cubic with a root splits exactly when its discriminant is a square. -/
theorem splits_iff_isSquare_discr_of_isRoot_of_monic_cubic {g : F[X]} (hg : g.Monic)
    (hdeg : g.natDegree = 3) (hchar : ringChar F ≠ 2) (hsep : g.Separable) {a : F}
    (ha : g.IsRoot a) : g.Splits ↔ IsSquare g.discr := by
  have hcubic : g = Cubic.toPoly ⟨1, g.coeff 2, g.coeff 1, g.coeff 0⟩ := by
    ext n
    by_cases hn : n < 4
    · interval_cases n
      · simp
      · simp
      · simp
      · simpa [hdeg] using hg.coeff_natDegree
    · have hn' : g.natDegree < n := by omega
      rw [coeff_eq_zero_of_natDegree_lt hn', Cubic.coeff_eq_zero (by omega)]
  exact splits_iff_isSquare_discr_of_isRoot_of_eq_cubic hchar _ _ _ a hcubic hsep ha

/-- A cubic with two distinct roots over its coefficient field splits there. -/
theorem Splits.of_natDegree_eq_three_of_two_isRoot {g : F[X]} (hdeg : g.natDegree = 3)
    {a x : F} (ha : g.IsRoot a) (hx : g.IsRoot x) (hxa : x ≠ a) : g.Splits := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.2 ha
  have hgne : g ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hdeg
    omega
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hq
    exact hgne hq
  have hqdeg : q.natDegree = 2 := by
    rw [hq, natDegree_mul (X_sub_C_ne_zero a) hqne, natDegree_X_sub_C] at hdeg
    omega
  have hqx : q.eval x = 0 := by
    rw [hq, IsRoot, eval_mul, eval_sub, eval_X, eval_C] at hx
    exact (mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr hxa)
  rw [hq, splits_mul (X_sub_C_ne_zero a) hqne]
  exact ⟨Splits.X_sub_C a, Splits.of_natDegree_eq_two hqdeg hqx⟩

/-- A monic cubic over a field is irreducible exactly when it has no root in that field. -/
theorem Monic.irreducible_iff_not_exists_isRoot_of_natDegree_eq_three {g : F[X]} (hg : g.Monic)
    (hdeg : g.natDegree = 3) : Irreducible g ↔ ¬ ∃ a : F, g.IsRoot a := by
  rw [hg.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  simp [Multiset.eq_zero_iff_forall_notMem, mem_roots hg.ne_zero]

end Polynomial
