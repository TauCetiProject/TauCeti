/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.MellinTransform

/-!
# Mellin transforms of upper-tail indicators

For `0 ≤ a`, the Mellin transform of `(Ioi a).indicator f` is the upper Mellin integral
`∫ u in Ioi a, u ^ (s - 1) • f u`, and it converges exactly when that integrand is integrable
on `Ioi a`. These identities let a Mellin transform be split into tails over `(0, a]` and
`(a, ∞)`.

## Main results

* `TauCeti.mellinConvergent_indicator_Ioi_iff`: convergence of the Mellin transform of an
  upper-tail indicator is integrability of the upper Mellin integrand.
* `TauCeti.mellin_indicator_Ioi`: the Mellin transform of an upper-tail indicator is the upper
  Mellin integral.
-/

public section

open Set MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- For `0 ≤ a`, the Mellin transform of `(Ioi a).indicator f` converges at `s` exactly when the
upper Mellin integrand `u ^ (s - 1) • f u` is integrable on `Ioi a`. -/
theorem mellinConvergent_indicator_Ioi_iff {f : ℝ → E} {a : ℝ} (ha : 0 ≤ a) {s : ℂ} :
    MellinConvergent ((Ioi a).indicator f) s ↔
      IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • f u) (Ioi a) := by
  simp_rw [MellinConvergent, ← indicator_smul, integrableOn_indicator_iff
    measurableSet_Ioi.nullMeasurableSet, inter_eq_left.mpr (Ioi_subset_Ioi ha)]

/-- For `0 ≤ a`, the Mellin transform of `(Ioi a).indicator f` is the upper Mellin integral of
`f` over `Ioi a`. -/
theorem mellin_indicator_Ioi (f : ℝ → E) {a : ℝ} (ha : 0 ≤ a) (s : ℂ) :
    mellin ((Ioi a).indicator f) s = ∫ (u : ℝ) in Ioi a, (u : ℂ) ^ (s - 1) • f u := by
  simp_rw [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi ha)]

end TauCeti
