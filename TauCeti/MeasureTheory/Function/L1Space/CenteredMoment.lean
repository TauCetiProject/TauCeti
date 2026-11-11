/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability from a centered first moment

## Main results

* `Continuous.integrable_of_integrable_sub_smul`: a continuous function on `ℝ` whose centered
  first moment `(x - c) • f x` is integrable against a finite measure is itself integrable.
-/

public section

open MeasureTheory

namespace Continuous

/-- A continuous function `f : ℝ → E` whose centered first moment `(x - c) • f x` is integrable
against a finite measure `ρ` is itself integrable against `ρ`. -/
theorem integrable_of_integrable_sub_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ρ : Measure ℝ} [IsFiniteMeasure ρ] {c : ℝ} {f : ℝ → E}
    (hf : Continuous f) (hxf : Integrable (fun x => (x - c) • f x) ρ) : Integrable f ρ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := c - 1) (b := c + 1)).exists_bound_of_continuousOn
    hf.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC c ⟨by linarith, by linarith⟩)
  refine Integrable.mono' (g := fun x => C + ‖(x - c) • f x‖) ((integrable_const C).add hxf.norm)
    hf.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  by_cases hx : |x - c| < 1
  · have hx' : x ∈ Set.Icc (c - 1) (c + 1) := by
      rw [abs_lt] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (hC x hx').trans (le_add_of_nonneg_right (norm_nonneg _))
  · calc
      ‖f x‖ ≤ |x - c| * ‖f x‖ := le_mul_of_one_le_left (norm_nonneg _) (not_lt.mp hx)
      _ =       ‖(x - c) • f x‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ C + ‖(x - c) • f x‖ := le_add_of_nonneg_left hC0

end Continuous
