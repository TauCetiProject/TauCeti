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

A kernel into a nonempty, countably generated measurable space that is Dirac almost
everywhere for a given source measure agrees almost everywhere with the deterministic kernel
of a measurable map. This is the measure-relative version of Mathlib's
`ProbabilityTheory.Kernel.IsDeterministic.exists_eq_deterministic`, which assumes a
deterministic kernel at every source point.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Nonempty Y]

/-- If a kernel is almost everywhere a Dirac measure, then it agrees almost everywhere with
the deterministic kernel of a measurable map. -/
theorem exists_ae_eq_deterministic_of_ae_exists_eq_dirac (κ : Kernel X Y) {μ : Measure X}
    (hκ : ∀ᵐ x ∂μ, ∃ y, κ x = Measure.dirac y) :
    ∃ (f : X → Y) (hf : Measurable f), κ =ᵐ[μ] deterministic f hf := by
  classical
  let f : X → Y := fun x ↦
    if h : ∃ y, κ x = Measure.dirac y then h.choose else Classical.arbitrary Y
  have hκf : ∀ᵐ x ∂μ, κ x = Measure.dirac (f x) := by
    filter_upwards [hκ] with x hx
    simpa only [f, dite_eq_left hx] using hx.choose_spec
  have hf : AEMeasurable f μ := NullMeasurable.aemeasurable fun s hs ↦
    (κ.measurable_coe hs (measurableSet_singleton 1)).nullMeasurableSet.congr <| by
      filter_upwards [hκf] with x hx
      simp [hx, Measure.dirac_apply' _ hs, Set.indicator_eq_one_iff_mem]
  refine ⟨hf.mk f, hf.measurable_mk, ?_⟩
  filter_upwards [hκf, hf.ae_eq_mk] with x hx hfx
  rw [deterministic_apply, hx, hfx]

end ProbabilityTheory.Kernel
