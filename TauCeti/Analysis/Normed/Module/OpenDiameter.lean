/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.Analysis.Normed.Module.Basic

/-!
# Negative-power radius-to-diameter bounds on bounded open sets

Converts chunkiness bounds `Metric.diam s ≤ γ * ρ` (`0 < ρ`) on nonempty bounded open subsets of a
real normed space into negative-power inequalities `ρ ^ (-α) ≤ γ ^ α * (Metric.diam s) ^ (-α)` for
`0 ≤ α` (`IsOpen.rpow_neg_le_mul_rpow_diam`, `IsOpen.rpow_neg_finrank_mul_le`), expressing
ball-cutoff integral estimates in terms of `Metric.diam s`.
-/

public section

/-- On a nonempty bounded open subset `s` of a nontrivial real normed space, `Metric.diam s ≤ γ * ρ`
(`0 < ρ`) implies `ρ ^ (-α) ≤ γ ^ α * (Metric.diam s) ^ (-α)` for every `0 ≤ α`. -/
theorem IsOpen.rpow_neg_le_mul_rpow_diam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {s : Set E} (hs : IsOpen s) (hb : Bornology.IsBounded s) (hne : s.Nonempty)
    {ρ γ α : ℝ} (hρ : 0 < ρ) (hdiam : Metric.diam s ≤ γ * ρ) (hα : 0 ≤ α) :
    ρ ^ (-α) ≤ γ ^ α * Metric.diam s ^ (-α) := by
  obtain ⟨y₀, hy₀⟩ := hne
  have hd : 0 < Metric.diam s := hs.diam_pos hb hy₀
  have hγ : 0 < γ := pos_of_mul_pos_left (hd.trans_le hdiam) hρ.le
  have hinv : ρ⁻¹ ≤ γ / Metric.diam s := by
    rw [inv_le_iff_one_le_mul₀ hρ, div_mul_eq_mul_div, le_div_iff₀ hd, one_mul]; exact hdiam
  calc ρ ^ (-α) = (ρ⁻¹) ^ α := by rw [Real.inv_rpow hρ.le, ← Real.rpow_neg hρ.le]
    _ ≤ (γ / Metric.diam s) ^ α := Real.rpow_le_rpow (by positivity) hinv hα
    _ = γ ^ α * Metric.diam s ^ (-α) := by
        rw [div_eq_mul_inv, Real.mul_rpow hγ.le (by positivity), Real.inv_rpow hd.le,
          ← Real.rpow_neg hd.le]

/-- Dimension-weighted form of `IsOpen.rpow_neg_le_mul_rpow_diam`, valid without
`[Nontrivial E]`. -/
theorem IsOpen.rpow_neg_finrank_mul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : IsOpen s) (hb : Bornology.IsBounded s) (hne : s.Nonempty)
    {ρ γ α : ℝ} (hρ : 0 < ρ) (hdiam : Metric.diam s ≤ γ * ρ) (hα : 0 ≤ α) :
    ρ ^ (-(Module.finrank ℝ E : ℝ) * α) ≤
      γ ^ ((Module.finrank ℝ E : ℝ) * α) * Metric.diam s ^ (-(Module.finrank ℝ E : ℝ) * α) := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hn0 | hn_pos
  · simp [hn0]
  have := Module.nontrivial_of_finrank_pos hn_pos
  simpa only [neg_mul] using
    hs.rpow_neg_le_mul_rpow_diam hb hne hρ hdiam (mul_nonneg (Nat.cast_nonneg _) hα)
