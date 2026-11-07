/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Derivative bounds for expanding cutoffs

Subtracting a constant from `χ (R⁻¹ • ·)` leaves every positive-order derivative unchanged.
For `R ≥ 1`, a bound `B` on the `i`-th derivative of `χ` therefore gives a bound `B / R` on
the corresponding derivative of the cutoff error. No regularity of `χ` is assumed.
Including order zero, the same hypotheses give a uniform bound `B + ‖c‖` after subtracting
an arbitrary constant `c`.

This estimate is shared by the Sobolev and Schwartz-space cutoff approximations. It is
extracted from the derivative scaling argument in
`TauCeti/Analysis/Distribution/SchwartzSpace/Cutoff.lean`, using Mathlib's
`ContinuousLinearEquiv.iteratedFDerivWithin_comp_right`.
-/

public section

namespace TauCeti

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a positive derivative order and `R ≥ 1`, subtracting a constant from an expanding
cutoff gives a derivative bound `B / R`, where `B` bounds that derivative of the cutoff. -/
theorem norm_iteratedFDeriv_comp_inv_smul_sub_const_le {χ : E → F} {i : ℕ} (hi : i ≠ 0)
    {B : ℝ} (hB : ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) (c : F) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y ↦ χ (R⁻¹ • y) - c) x‖ ≤ B / R := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let g : E ≃L[ℝ] E := .smulLeft (Units.mk0 R⁻¹ (inv_ne_zero hR0.ne'))
  have hgχ : χ ∘ g = fun y ↦ χ (R⁻¹ • y) := by ext; simp [g]
  have hg : ‖(g : E →L[ℝ] E)‖ ≤ R⁻¹ := ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    fun y ↦ by simp [g, norm_smul, abs_of_pos hR0]
  -- The constant disappears after the first derivative.
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp only [fderiv_sub_const]
  -- Scaling by `R⁻¹` is a continuous linear equivalence, so no smoothness of `χ` is needed.
  rw [← iteratedFDeriv_succ_eq_comp_right, ← hgχ, ← iteratedFDerivWithin_univ,
    ← Set.preimage_univ (f := g), g.iteratedFDerivWithin_comp_right χ uniqueDiffOn_univ
      (Set.mem_univ _), iteratedFDerivWithin_univ]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_eq_mul_inv]
  exact mul_le_mul (hB _) ((pow_le_of_le_one (norm_nonneg _) (hg.trans
    (inv_le_one_of_one_le₀ hR)) hi).trans hg) (by positivity) ((norm_nonneg _).trans (hB 0))

/-- For any derivative order and `R ≥ 1`, subtracting a constant from an expanding cutoff
gives a derivative bound `B + ‖c‖`, where `B` bounds that derivative of the cutoff. -/
theorem norm_iteratedFDeriv_comp_inv_smul_sub_const_le_add_norm {χ : E → F} {i : ℕ} {B : ℝ}
    (hB : ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) (c : F) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y ↦ χ (R⁻¹ • y) - c) x‖ ≤ B + ‖c‖ := by
  rcases eq_or_ne i 0 with rfl | hi
  · rw [norm_iteratedFDeriv_zero]
    exact (norm_sub_le _ _).trans (add_le_add (by simpa using hB (R⁻¹ • x)) le_rfl)
  · exact (norm_iteratedFDeriv_comp_inv_smul_sub_const_le hi hB hR c x).trans
      ((div_le_self ((norm_nonneg _).trans (hB 0)) hR).trans (le_add_of_nonneg_right
        (norm_nonneg c)))

end TauCeti
