/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpOrder

/-!
# `Lᵖ` is an ordered module

Mathlib orders `Lᵖ` almost everywhere (`MeasureTheory.Lp.coeFn_le`). If scalar multiplication on
the values is monotone, then so is scalar multiplication on `Lᵖ` classes, since it is computed
almost everywhere pointwise. In particular real `Lᵖ` is an ordered real module, which is the
hypothesis under which Mathlib's Bochner integral of almost everywhere nonnegative functions is
nonnegative (`MeasureTheory.integral_nonneg_of_ae`), now applicable to `Lᵖ`-valued functions.

The positive part of a real `Lᵖ` class is nonnegative (`MeasureTheory.Lp.posPart_nonneg`), and it
vanishes exactly when the class is nonpositive (`MeasureTheory.Lp.posPart_eq_zero_iff`).
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α 𝕜 E : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [NormedRing 𝕜]
  [PartialOrder 𝕜] [NormedAddCommGroup E] [PartialOrder E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Multiplying an `Lᵖ` class by a nonnegative scalar is monotone if it is so on the values. -/
instance [PosSMulMono 𝕜 E] : PosSMulMono 𝕜 (Lp E p μ) where
  smul_le_smul_of_nonneg_left c hc f g hfg := by
    rw [← coeFn_le] at hfg ⊢
    filter_upwards [coeFn_smul c f, coeFn_smul c g, hfg] with x hf hg hx
    rw [hf, hg]
    exact smul_le_smul_of_nonneg_left hx hc

/-- Multiplying a nonnegative `Lᵖ` class by scalars is monotone if it is so on the values. -/
instance [SMulPosMono 𝕜 E] : SMulPosMono 𝕜 (Lp E p μ) where
  smul_le_smul_of_nonneg_right f hf c d hcd := by
    rw [← coeFn_nonneg] at hf
    rw [← coeFn_le]
    filter_upwards [coeFn_smul c f, coeFn_smul d f, hf] with x hc hd hx
    rw [hc, hd]
    exact smul_le_smul_of_nonneg_right hcd hx

/-- `Lᵖ` with values in an ordered module is an ordered module, ordered almost everywhere. -/
instance [IsOrderedModule 𝕜 E] : IsOrderedModule 𝕜 (Lp E p μ) where

/-- The positive part of a real `Lᵖ` class is nonnegative. -/
@[simp]
theorem posPart_nonneg (f : Lp ℝ p μ) : 0 ≤ Lp.posPart f := by
  rw [← coeFn_nonneg]
  filter_upwards [coeFn_posPart f] with x hx
  rw [Pi.zero_apply, hx]
  exact le_max_right _ _

/-- The positive part of a real `Lᵖ` class vanishes exactly when the class is nonpositive. -/
@[simp]
theorem posPart_eq_zero_iff {f : Lp ℝ p μ} : Lp.posPart f = 0 ↔ f ≤ 0 := by
  rw [← coeFn_le]
  constructor
  · intro h
    have hpos : Lp.posPart f =ᵐ[μ] 0 := by
      rw [h]
      exact coeFn_zero ℝ p μ
    filter_upwards [coeFn_posPart f, hpos, coeFn_zero ℝ p μ] with x hx h₀ h₀'
    rw [h₀', Pi.zero_apply, ← max_eq_right_iff, ← hx, h₀, Pi.zero_apply]
  · intro h
    refine Lp.ext ?_
    filter_upwards [coeFn_posPart f, coeFn_zero ℝ p μ, h] with x hx h₀ hle
    rw [hx, h₀, Pi.zero_apply, max_eq_right_iff]
    exact hle.trans_eq h₀

end MeasureTheory.Lp
