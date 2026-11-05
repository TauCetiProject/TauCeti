/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import TauCeti.Analysis.PDE.HopfLax.Basic

/-!
# Integrability of the Hopf–Lax value

For the cost `L w = ‖w‖ ^ p` and a bounded continuous initial datum, the Hopf–Lax value at a
positive time is bounded and continuous, hence integrable against a finite measure.

## Main results

* `TauCeti.integrable_hopfLax_norm_rpow`: the Hopf–Lax value of a bounded continuous function at
  a positive time is integrable against a finite measure.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The Hopf–Lax value of a bounded continuous function at a positive time is integrable against
a finite measure. -/
theorem integrable_hopfLax_norm_rpow {p : ℝ} (hp : 1 ≤ p) {g : E → ℝ}
    (hg : Continuous g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) {s : ℝ} (hs : 0 < s) (μ : Measure E)
    [IsFiniteMeasure μ] : Integrable (fun x ↦ hopfLax (‖·‖ ^ p) g s x) μ :=
  have hgb : BddBelow (range g) := ⟨-C, forall_mem_range.2 fun x ↦ (abs_le.1 (hgC x)).1⟩
  .of_bound (((continuousOn_hopfLax_norm_rpow hp hg hgb).comp_continuous
    (f := fun x : E ↦ (s, x)) (by fun_prop) fun _ ↦ hs).aestronglyMeasurable) C
    (ae_of_all _ fun x ↦ (abs_hopfLax_norm_rpow_le (zero_lt_one.trans_le hp).ne' hgC hs.le x))

end TauCeti
