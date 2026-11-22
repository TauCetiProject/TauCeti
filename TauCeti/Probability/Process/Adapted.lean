/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Probability.Process.Adapted

/-!
# Integrability of dominated increments of strongly adapted processes

An increment of a strongly adapted process dominated almost surely by a constant is integrable
under any finite measure (`MeasureTheory.StronglyAdapted.integrable_sub_of_bound`), with a
specialization to nonnegative real increments
(`MeasureTheory.StronglyAdapted.integrable_sub_of_nonneg_le`).
-/

public section

namespace MeasureTheory.StronglyAdapted

/-- An increment of a strongly adapted process dominated almost surely by a constant is integrable
under any finite measure. -/
theorem integrable_sub_of_bound {ι Ω E : Type*} [Preorder ι]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] [SeminormedAddCommGroup E]
    {ℱ : Filtration ι mΩ} {X : ι → Ω → E} (hX : StronglyAdapted ℱ X) {u v : ι} {C : ℝ}
    (hbd : ∀ᵐ ω ∂μ, ‖X v ω - X u ω‖ ≤ C) :
    Integrable (fun ω ↦ X v ω - X u ω) μ :=
  (integrable_const (max C 0)).mono_eNorm
    (((hX v).mono (ℱ.le v)).sub ((hX u).mono (ℱ.le u))).aestronglyMeasurable
    (hbd.mono fun _ hω ↦ by
      rw [← ofReal_norm, ← ofReal_norm, Real.norm_of_nonneg (le_max_right C 0)]
      exact ENNReal.ofReal_le_ofReal (hω.trans (le_max_left C 0)))

/-- A nonnegative real increment of a strongly adapted process bounded almost surely by a constant
is integrable under any finite measure. -/
theorem integrable_sub_of_nonneg_le {ι Ω : Type*} [Preorder ι]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ι mΩ}
    {A : ι → Ω → ℝ} (hA : StronglyAdapted ℱ A) {u v : ι} {C : ℝ}
    (hbd : ∀ᵐ ω ∂μ, 0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ C) :
    Integrable (fun ω ↦ A v ω - A u ω) μ :=
  hA.integrable_sub_of_bound <| hbd.mono fun _ hω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2

end MeasureTheory.StronglyAdapted
