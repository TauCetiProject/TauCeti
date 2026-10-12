/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Derivative bounds for expanding cutoffs

Subtracting a constant from `χ (R⁻¹ • ·)` leaves every positive-order derivative unchanged.
For `R ≥ 1`, a bound `B` on the `i`-th derivative of `χ` therefore gives a bound `B / R` on
the corresponding derivative of the cutoff error. Only `Cⁱ` regularity is needed.
Including order zero, the same hypotheses give a uniform bound `B + ‖c‖` after subtracting
an arbitrary constant `c`.

This estimate is shared by the Sobolev and Schwartz-space cutoff approximations. It is
extracted from the derivative scaling argument in
`TauCeti/Analysis/Distribution/SchwartzSpace/Cutoff.lean`, using Mathlib's
`iteratedFDeriv_comp_const_smul`.
-/

public section

namespace TauCeti

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a positive derivative order and `R ≥ 1`, subtracting a constant from an expanding
cutoff gives a derivative bound `B / R`, where `B` bounds that derivative of the cutoff. -/
theorem norm_iteratedFDeriv_comp_inv_smul_sub_const_le {χ : E → F} {i : ℕ}
    (hχ : ContDiff ℝ i χ) (hi : i ≠ 0) {B : ℝ}
    (hB : ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) (c : F) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y ↦ χ (R⁻¹ • y) - c) x‖ ≤ B / R := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  rw [fun_iteratedFDeriv_sub_apply (f := fun y ↦ χ (R⁻¹ • y)) (g := fun _ ↦ c)
    (hχ.comp (contDiff_const_smul R⁻¹)).contDiffAt
    (contDiffAt_const (c := c)), iteratedFDeriv_const_of_ne hi, Pi.zero_apply, sub_zero,
    iteratedFDeriv_comp_const_smul _ hχ, norm_smul, norm_pow, norm_inv,
    Real.norm_of_nonneg hR0.le]
  have hRi : (R⁻¹) ^ i ≤ R⁻¹ :=
    pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ hR) hi
  calc (R⁻¹) ^ i * ‖iteratedFDeriv ℝ i χ (R⁻¹ • x)‖ ≤ R⁻¹ * B :=
        mul_le_mul hRi (hB _) (norm_nonneg _) (by positivity)
    _ = B / R := by rw [inv_mul_eq_div]

/-- For any derivative order and `R ≥ 1`, subtracting a constant from an expanding cutoff
gives a derivative bound `B + ‖c‖`, where `B` bounds that derivative of the cutoff. -/
theorem norm_iteratedFDeriv_comp_inv_smul_sub_const_le_add_norm {χ : E → F} {i : ℕ}
    (hχ : ContDiff ℝ i χ) {B : ℝ}
    (hB : ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) (c : F) (x : E) :
    ‖iteratedFDeriv ℝ i (fun y ↦ χ (R⁻¹ • y) - c) x‖ ≤ B + ‖c‖ := by
  rcases eq_or_ne i 0 with rfl | hi
  · rw [norm_iteratedFDeriv_zero]
    have hb := hB (R⁻¹ • x)
    rw [norm_iteratedFDeriv_zero] at hb
    exact (norm_sub_le _ _).trans (add_le_add hb le_rfl)
  · have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    exact (norm_iteratedFDeriv_comp_inv_smul_sub_const_le hχ hi hB hR c x).trans
      ((div_le_self hB0 hR).trans (le_add_of_nonneg_right (norm_nonneg c)))

end TauCeti
