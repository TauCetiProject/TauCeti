/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Regular distributions and scaling of the measure

Mathlib's regular distribution `Distribution.ofFun Ω f μ n` of a function `f` integrates test
functions against `f` for the measure `μ`. Multiplying the measure by a finite constant `c`
multiplies the distribution by `c` (`Distribution.ofFun_smul_measure`), whether or not `f` is
locally integrable. Two additive Haar measures differ by such a constant, so this compares the
regular distributions of the same function for two Haar measures.
-/

public section

open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal NNReal

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞}

/-- Multiplying the measure by a finite constant multiplies a regular distribution by that
constant. -/
theorem ofFun_smul_measure (f : E → F) (μ : Measure E) (c : ℝ≥0) :
    ofFun Ω f ((c : ℝ≥0∞) • μ) n = (c : ℝ) • ofFun Ω f μ n := by
  by_cases hf : LocallyIntegrableOn f Ω μ
  · ext φ
    rw [smul_apply, ofFun_apply (hf.smul_measure ENNReal.coe_ne_top),
      ofFun_apply hf, integral_smul_measure, ENNReal.coe_toReal]
  rcases eq_or_ne c 0 with rfl | hc
  · ext φ
    simp [ofFun_apply_eq_ite]
  · rw [ofFun_eq_zero hf, smul_zero, ofFun_eq_zero fun h ↦ hf ?_]
    have h' := h.smul_measure (ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 hc))
    rwa [smul_smul, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hc) ENNReal.coe_ne_top,
      one_smul] at h'

end Distribution
