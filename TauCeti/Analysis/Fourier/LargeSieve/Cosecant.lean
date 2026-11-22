/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ZetaValues
import TauCeti.Algebra.BigOperators.Finset.Fiber
import TauCeti.Analysis.Normed.Group.AddCircle.Basic

/-!
# Cosecant row bound for well-spaced points on `UnitAddCircle`

This file proves Bombieri's circular cosecant row bound for `δ`-separated finite families in
`UnitAddCircle = ℝ / ℤ`:

* `TauCeti.sum_erase_inv_sin_sq_le`:
  `∑ j ∈ s.erase i, (sin (π * (x i - x j)) ^ 2)⁻¹ ≤ π ^ 2 / (12 * δ ^ 2)`.
-/

public section

namespace TauCeti

/-- Bombieri's cosecant row bound: for any `δ`-separated finite family in `UnitAddCircle` (`0 < δ`)
and any `i ∈ s`, `∑ j ∈ s.erase i, (sin (π * (x i - x j)) ^ 2)⁻¹ ≤ π ^ 2 / (12 * δ ^ 2)`. -/
theorem sum_erase_inv_sin_sq_le {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖)
    {i : ι} (hi : i ∈ s) :
    ∑ j ∈ s.erase i, (Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹ ≤
      Real.pi ^ 2 / (12 * δ ^ 2) := by
  let b : ι → ℕ := fun j ↦ ⌊‖((x i - x j : ℝ) : UnitAddCircle)‖ / δ⌋₊
  have hterm : ∀ j ∈ s.erase i,
      (Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹ ≤
        (4 * δ ^ 2)⁻¹ * ((1 : ℝ) / (b j : ℝ) ^ 2) := by
    intro j hj
    have hsep_ij := hsep i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
    have hb_pos : 0 < b j := Nat.floor_pos.mpr ((one_le_div hδ).mpr hsep_ij)
    have hb_le : (b j : ℝ) * δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖ :=
      (le_div_iff₀ hδ).mp (Nat.floor_le (by positivity))
    have hsin_lb : 4 * ((b j : ℝ) * δ) ^ 2 ≤ Real.sin (Real.pi * (x i - x j)) ^ 2 := by
      have hsq := pow_le_pow_left₀ (by positivity) hb_le 2
      linarith [(x i - x j).four_mul_norm_unitAddCircle_sq_le_sin_sq]
    calc
      (Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹
          ≤ (4 * ((b j : ℝ) * δ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hsin_lb
      _ = (4 * δ ^ 2)⁻¹ * ((1 : ℝ) / (b j : ℝ) ^ 2) := by ring
  have hfib :
      ∑ j ∈ s.erase i, ((1 : ℝ) / (b j : ℝ) ^ 2) ≤
        2 * ∑ m ∈ (s.erase i).image b, ((1 : ℝ) / (m : ℝ) ^ 2) := by
    rw [← sum_card_filter_nsmul_eq_sum_comp (s := s.erase i) (t := (s.erase i).image b)
        (fun j hj ↦ Finset.mem_image_of_mem b hj) (fun m ↦ (1 : ℝ) / (m : ℝ) ^ 2),
      Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ ↦ ?_
    rw [nsmul_eq_mul]
    have hsep' : ∀ a ∈ s.erase i, ∀ b ∈ s.erase i, a ≠ b →
        δ ≤ ‖((x a - x b : ℝ) : UnitAddCircle)‖ :=
      fun a ha b hb ↦ hsep a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast card_filter_floor_norm_unitAddCircle_div_le_two hδ hsep' (x i) m)
      (by positivity)
  have hzeta :
      ∑ m ∈ (s.erase i).image b, ((1 : ℝ) / (m : ℝ) ^ 2) ≤ Real.pi ^ 2 / 6 :=
    sum_le_hasSum ((s.erase i).image b) (fun n _ ↦ by positivity) hasSum_zeta_two
  calc
    ∑ j ∈ s.erase i, (Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹
        ≤ ∑ j ∈ s.erase i, (4 * δ ^ 2)⁻¹ * ((1 : ℝ) / (b j : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = (4 * δ ^ 2)⁻¹ * ∑ j ∈ s.erase i, ((1 : ℝ) / (b j : ℝ) ^ 2) := (Finset.mul_sum _ _ _).symm
    _ ≤ (4 * δ ^ 2)⁻¹ * (2 * ∑ m ∈ (s.erase i).image b, ((1 : ℝ) / (m : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hfib (by positivity)
    _ ≤ (4 * δ ^ 2)⁻¹ * (2 * (Real.pi ^ 2 / 6)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzeta (by positivity)) (by positivity)
    _ = Real.pi ^ 2 / (12 * δ ^ 2) := by ring

end TauCeti
