/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Superlevel sets and weak-type bounds

Two elementary facts about the superlevel sets `{y | ofReal t < T v y}` of an operator `T` that
are used in Marcinkiewicz interpolation but need no interpolation theory.

## Main statements

* `TauCeti.setOf_ofReal_lt_ae_le_union`: if `T v ≤ T g₁ + T g₂` almost everywhere and `d + e ≤ 1`,
  the superlevel set of `T v` is almost everywhere covered by those of `T g₁` and `T g₂`.
* `TauCeti.meas_ofReal_lt_le_of_weak`: a weak-type bound at the height `r` bounds the measure of
  the superlevel set at that height.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {α β G : Type*} {T : (α → G) → β → ℝ≥0∞}

/-- If `T v ≤ T g₁ + T g₂` almost everywhere and `d + e ≤ 1`, then the superlevel set of `T v` at
the height `t` is almost everywhere covered by the superlevel set of `T g₁` at the height `d * t`
and that of `T g₂` at the height `e * t`. -/
theorem setOf_ofReal_lt_ae_le_union [MeasurableSpace β] {ν : Measure β} {v g₁ g₂ : α → G}
    {d e t : ℝ} (ht : 0 ≤ t) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hde : d + e ≤ 1) (hTv : T v ≤ᵐ[ν] T g₁ + T g₂) :
    {y | ENNReal.ofReal t < T v y} ≤ᵐ[ν]
      {y | ENNReal.ofReal (d * t) < T g₁ y} ∪ {y | ENNReal.ofReal (e * t) < T g₂ y} := by
  filter_upwards [hTv] with y hsum hy
  rcases lt_or_ge (ENNReal.ofReal (d * t)) (T g₁ y) with h₁ | h₁
  · exact Or.inl (Set.mem_ofPred.2 h₁)
  rcases lt_or_ge (ENNReal.ofReal (e * t)) (T g₂ y) with h₂ | h₂
  · exact Or.inr (Set.mem_ofPred.2 h₂)
  have hy' : ENNReal.ofReal t < T v y := hy
  have hle : T v y ≤ ENNReal.ofReal t :=
    calc T v y ≤ ENNReal.ofReal (d * t) + ENNReal.ofReal (e * t) :=
          hsum.trans (add_le_add h₁ h₂)
      _ = ENNReal.ofReal (d * t + e * t) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal (by nlinarith)
  exact absurd (hy'.trans_le hle) (lt_irrefl _)

/-- A weak-type bound at the height `r` bounds the measure of the superlevel set at that height:
`r ^ q * ν {T w > r} ≤ B` gives `ν {T w > r} ≤ r ^ (-q) * B`. The right side `B` is arbitrary, so
the same step serves weak-type bounds of any form, such as `A * ∫⁻ ‖w‖ₑ ^ p` or
`A * (∫⁻ ‖w‖ₑ ^ p) ^ (q / p)`. -/
theorem meas_ofReal_lt_le_of_weak [MeasurableSpace β] {ν : Measure β} {w : α → G} {q r : ℝ}
    {B : ℝ≥0∞} (hr : 0 < r) (hweak : ENNReal.ofReal r ^ q * ν {y | ENNReal.ofReal r < T w y} ≤ B) :
    ν {y | ENNReal.ofReal r < T w y} ≤ ENNReal.ofReal (r ^ (-q)) * B := by
  rw [← ENNReal.ofReal_rpow_of_pos hr, ENNReal.rpow_neg]
  exact (ENNReal.mul_le_iff_le_inv
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hr) ENNReal.ofReal_ne_top).ne'
    (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top)).1 hweak

end TauCeti
