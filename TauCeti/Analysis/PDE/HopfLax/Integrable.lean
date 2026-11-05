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

For the cost `L w = ‖w‖ ^ p` with `1 ≤ p` and a bounded initial datum, the Hopf–Lax value at a
positive time is bounded and upper semicontinuous, hence measurable, and so integrable against a
finite measure.

## Main results

* `TauCeti.integrable_hopfLax_norm_rpow`: for the cost `‖w‖ ^ p` with `1 ≤ p`, in a real
  seminormed space, the Hopf–Lax value of a bounded function at a positive time is integrable
  against a finite measure.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

/-- For the cost `L w = ‖w‖ ^ p` with `1 ≤ p`, in a real seminormed space, the Hopf–Lax value of a
bounded function at a positive time is integrable against a finite measure. -/
theorem integrable_hopfLax_norm_rpow {p : ℝ} (hp : 1 ≤ p) {g : E → ℝ} {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) {s : ℝ} (hs : 0 < s) (μ : Measure E)
    [IsFiniteMeasure μ] : Integrable (fun x ↦ hopfLax (‖·‖ ^ p) g s x) μ :=
  have hgb : BddBelow (range g) := ⟨-C, forall_mem_range.2 fun x ↦ (abs_le.1 (hgC x)).1⟩
  have hLb : BddBelow (range (‖·‖ ^ p : E → ℝ)) :=
    ⟨0, forall_mem_range.2 fun w ↦ Real.rpow_nonneg (norm_nonneg w) p⟩
  have hLc : Continuous (‖·‖ ^ p : E → ℝ) :=
    continuous_norm.rpow_const fun _ ↦ .inr (zero_le_one.trans hp)
  have husc : UpperSemicontinuous fun x : E ↦ hopfLax (‖·‖ ^ p) g s x :=
    upperSemicontinuousOn_univ_iff.1 <|
      (upperSemicontinuousOn_hopfLax hgb hLb hLc).comp
        (g := fun x : E ↦ (s, x)) (by fun_prop) fun _ _ ↦ hs
  .of_bound husc.measurable.aestronglyMeasurable C
    (ae_of_all _ fun x ↦ (abs_hopfLax_norm_rpow_le (zero_lt_one.trans_le hp).ne' hgC hs.le x))

end TauCeti
