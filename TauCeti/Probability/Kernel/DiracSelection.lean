/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Selecting the point of an almost surely Dirac kernel

A kernel can be Dirac only almost everywhere for a given source
measure. In that case its atoms form an almost everywhere measurable map. This is the
measure-relative version of Mathlib's
`ProbabilityTheory.Kernel.IsDeterministic.exists_eq_deterministic`, which assumes a
deterministic kernel at every source point.

The proof reads membership in a measurable target set from the kernel's value on that set.
The resulting null-measurable selector is almost everywhere measurable when the target
sigma algebra is countably generated. In particular, this applies to standard Borel targets.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

universe u v

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Nonempty Y]

/-- If a kernel is almost everywhere a Dirac measure, its atoms have a
measurable representative. The selected map represents the kernel almost everywhere. -/
theorem exists_measurable_of_ae_exists_kernel_eq_dirac
    (κ : Kernel X Y) (μ : Measure X)
    (hκ : ∀ᵐ x ∂μ, ∃ y : Y, κ x = Measure.dirac y) :
    ∃ T : X → Y, Measurable T ∧ ∀ᵐ x ∂μ, κ x = Measure.dirac (T x) := by
  classical
  let T : X → Y := fun x ↦
    if h : ∃ y : Y, κ x = Measure.dirac y then h.choose else Classical.choice inferInstance
  have hT : ∀ᵐ x ∂μ, κ x = Measure.dirac (T x) := by
    filter_upwards [hκ] with x hx
    simpa only [T, dite_eq_left hx] using hx.choose_spec
  have hnull : NullMeasurable T μ := by
    intro s hs
    have hm : MeasurableSet {x : X | κ x s = 1} :=
      (κ.measurable_coe hs) (measurableSet_singleton 1)
    have heq : {x : X | κ x s = 1} =ᵐ[μ] T ⁻¹' s := by
      filter_upwards [hT] with x hx
      by_cases hxs : T x ∈ s
      · simp [hx, Measure.dirac_apply' _ hs, hxs]
      · simp [hx, Measure.dirac_apply' _ hs, hxs]
    exact hm.nullMeasurableSet.congr heq
  let T' := hnull.aemeasurable.mk T
  have hT' : T =ᵐ[μ] T' := hnull.aemeasurable.ae_eq_mk
  refine ⟨T', hnull.aemeasurable.measurable_mk, ?_⟩
  filter_upwards [hT, hT'] with x hx hxx
  rw [← hxx]
  exact hx

end Probability

end TauCeti
