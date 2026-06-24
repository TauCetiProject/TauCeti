/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Continuity of positive-definite functions

This file records the standard continuity upgrade for positive-definite functions on a seminormed
additive group with the negation involution. A positive-definite function that is continuous at
the origin is uniformly continuous. The proof uses the usual reproducing-kernel estimate
`‖F x - F y‖² ≤ 2 F(0).re ‖F (x - y) - F 0‖`, obtained from the `3 × 3` Gram matrix of the
points `x`, `y`, and `0`.

This advances Part C of the `OneParameterSemigroups` roadmap, whose positive-definite-function
API asks for the basic fact "continuity at `0` ⇒ uniform continuity" before Bochner's theorem.

## Main declarations

In the namespace `TauCeti.IsPositiveDefinite`:

* `norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_forall_star_eq_neg`:
  the real-part continuity estimate.
* `norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_forall_star_eq_neg`:
  the norm-valued continuity estimate.
* `uniformContinuous_of_continuousAt_zero_of_forall_star_eq_neg`:
  continuity at `0` implies uniform continuity.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

namespace IsPositiveDefinite

section Algebra

variable {E : Type*} [AddCommGroup E] [StarAddMonoid E] {F : E → ℂ}

private theorem apply_neg_eq_conj (hF : IsPositiveDefinite F)
    (hstar : ∀ x : E, star x = -x) (x : E) : F (-x) = conj (F x) := by
  have h := hF.conj_symm x 0
  simpa [hstar x] using congrArg conj h

private theorem eq_zero_of_map_zero_re_eq_zero (hF : IsPositiveDefinite F)
    (hstar : ∀ x : E, star x = -x) (h0 : (F 0).re = 0) (x : E) : F x = 0 := by
  have hnorm : ‖F x‖ ≤ 0 := by
    simpa [h0] using hF.norm_apply_le_map_zero_re_of_star_eq_neg x (hstar x)
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

private theorem gram_three_sub_re_eq (hF : IsPositiveDefinite F)
    (hstar : ∀ x : E, star x = -x) {x y : E} {C d lam : ℂ}
    (hC : C = F 0) (hd : d = F x - F y) (hlam : lam = -d / C)
    (hCpos : 0 < (F 0).re) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      ![1, -1, lam] i * conj (![1, -1, lam] j) *
        F (![x, y, 0] i + star (![x, y, 0] j))).re
      = 2 * (F 0).re - 2 * (F (x - y)).re - Complex.normSq d / (F 0).re := by
  have hyx : F (y - x) = conj (F (x - y)) := by
    have h := hF.conj_symm x y
    simpa [hstar x, hstar y, sub_eq_add_neg, add_comm] using congrArg conj h
  have hnx : F (-x) = conj (F x) := hF.apply_neg_eq_conj hstar x
  have hny : F (-y) = conj (F y) := hF.apply_neg_eq_conj hstar y
  have hny' : F (0 + -y) = conj (F y) := by simpa using hny
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  simp only [Matrix.vecHead, Matrix.vecTail]
  simp only [Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [hstar x, hstar y, hstar 0, neg_zero, zero_add, add_zero, sub_eq_add_neg,
    ← sub_eq_add_neg y x, hyx, hnx, hny']
  simp only [add_zero, add_neg_cancel]
  simp only [hC, hd, hlam]
  rw [hF.map_zero_eq_ofReal_re]
  field_simp [Complex.ofReal_ne_zero.mpr hCpos.ne']
  rw [← sub_eq_add_neg x y]
  simp [Complex.normSq_apply]
  field_simp [hCpos.ne']
  ring_nf

/-- The real-part form of the standard positive-definite continuity estimate. -/
theorem norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_forall_star_eq_neg
    (hF : IsPositiveDefinite F)
    (hstar : ∀ x : E, star x = -x) (x y : E) :
    ‖F x - F y‖ ^ 2
      ≤ 2 * (F 0).re * ((F 0).re - (F (x - y)).re) := by
  by_cases hC0 : (F 0).re = 0
  · simp [hF.eq_zero_of_map_zero_re_eq_zero hstar hC0]
  have hCpos : 0 < (F 0).re := lt_of_le_of_ne hF.map_zero_re_nonneg (Ne.symm hC0)
  let C : ℂ := F 0
  let d : ℂ := F x - F y
  let lam : ℂ := -d / C
  have hQ := hF 3 ![1, -1, lam] ![x, y, 0]
  have hQre : 0 ≤ (∑ i : Fin 3, ∑ j : Fin 3,
      ![1, -1, lam] i * conj (![1, -1, lam] j) *
        F (![x, y, 0] i + star (![x, y, 0] j))).re :=
    (Complex.nonneg_iff.mp hQ).1
  have hQcalc :
      (∑ i : Fin 3, ∑ j : Fin 3,
        ![1, -1, lam] i * conj (![1, -1, lam] j) *
          F (![x, y, 0] i + star (![x, y, 0] j))).re
        = 2 * (F 0).re - 2 * (F (x - y)).re - Complex.normSq d / (F 0).re := by
    exact hF.gram_three_sub_re_eq hstar rfl rfl rfl hCpos
  have hmain : Complex.normSq d ≤ (F 0).re *
      (2 * (F 0).re - 2 * (F (x - y)).re) := by
    have hnonneg : 0 ≤ 2 * (F 0).re - 2 * (F (x - y)).re
        - Complex.normSq d / (F 0).re := by
      simpa [hQcalc] using hQre
    have hdiv :
        Complex.normSq d / (F 0).re ≤ 2 * (F 0).re - 2 * (F (x - y)).re := by
      linarith
    have hmul := (div_le_iff₀ hCpos).mp hdiv
    nlinarith
  calc
    ‖F x - F y‖ ^ 2 = Complex.normSq d := by
      simp [d, Complex.normSq_eq_norm_sq]
    _ ≤ (F 0).re * (2 * (F 0).re - 2 * (F (x - y)).re) := hmain
    _ = 2 * (F 0).re * ((F 0).re - (F (x - y)).re) := by ring

/-- The norm-valued form of the standard positive-definite continuity estimate. -/
theorem norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_forall_star_eq_neg
    (hF : IsPositiveDefinite F)
    (hstar : ∀ x : E, star x = -x) (x y : E) :
    ‖F x - F y‖ ^ 2 ≤ 2 * (F 0).re * ‖F (x - y) - F 0‖ := by
  have hre :
      (F 0).re - (F (x - y)).re ≤ ‖F (x - y) - F 0‖ := by
    have h₁ : (F 0).re - (F (x - y)).re
        = -((F (x - y) - F 0).re) := by
      simp [Complex.sub_re]
    rw [h₁]
    exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  exact (hF.norm_sub_sq_le_two_mul_map_zero_re_mul_re_sub_of_forall_star_eq_neg hstar x y).trans
    (mul_le_mul_of_nonneg_left hre (mul_nonneg zero_le_two hF.map_zero_re_nonneg))

end Algebra

section Topology

variable {E : Type*} [SeminormedAddCommGroup E] [StarAddMonoid E] {F : E → ℂ}

/-- A positive-definite function on a seminormed additive group with the negation involution is
uniformly continuous as soon as it is continuous at the origin. -/
theorem uniformContinuous_of_continuousAt_zero_of_forall_star_eq_neg (hF : IsPositiveDefinite F)
    (hstar : ∀ x : E, star x = -x) (hcont : ContinuousAt F 0) :
    UniformContinuous F := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  by_cases hC0 : (F 0).re = 0
  · refine ⟨1, zero_lt_one, fun x y _ => ?_⟩
    simp [hF.eq_zero_of_map_zero_re_eq_zero hstar hC0, hε]
  have hCpos : 0 < (F 0).re := lt_of_le_of_ne hF.map_zero_re_nonneg (Ne.symm hC0)
  let η : ℝ := ε ^ 2 / (2 * (F 0).re)
  have hη : 0 < η := div_pos (sq_pos_of_pos hε) (mul_pos zero_lt_two hCpos)
  have hev := (Metric.tendsto_nhds.mp hcont) η hη
  rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδ, hδF⟩
  refine ⟨δ, hδ, fun x y hxy => ?_⟩
  have hdist : dist (x - y) 0 < δ := by
    simpa [dist_eq_norm, sub_eq_add_neg, add_comm] using hxy
  have hsmall : ‖F (x - y) - F 0‖ < η := by
    simpa [dist_eq_norm] using hδF hdist
  have hsquare_le : ‖F x - F y‖ ^ 2 < ε ^ 2 := by
    have hbound :=
      hF.norm_sub_sq_le_two_mul_map_zero_re_mul_norm_sub_of_forall_star_eq_neg hstar x y
    calc
      ‖F x - F y‖ ^ 2 ≤ 2 * (F 0).re * ‖F (x - y) - F 0‖ := hbound
      _ < 2 * (F 0).re * η := mul_lt_mul_of_pos_left hsmall (mul_pos zero_lt_two hCpos)
      _ = ε ^ 2 := by
        rw [show η = ε ^ 2 / (2 * (F 0).re) from rfl]
        field_simp [(mul_pos zero_lt_two hCpos).ne']
  have habs := sq_lt_sq.mp hsquare_le
  simpa [dist_eq_norm, abs_of_nonneg hε.le] using habs

end Topology

end IsPositiveDefinite

end TauCeti
