/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Sigma-finite support for a.e. finite strong measurability

A.e. finite strong measurability is equivalent to a.e. strong measurability together with
vanishing a.e. outside a measurable sigma-finite support. This separates the topological
measurability requirement from the measure-theoretic support requirement, for arbitrary
measures and Hausdorff targets with zero.
-/

public section

open Filter Set

namespace MeasureTheory

/-- A function is a.e. finitely strongly measurable exactly when it is a.e. strongly measurable
and vanishes a.e. outside a measurable set on which the measure is sigma-finite. -/
theorem aefinStronglyMeasurable_iff_aestronglyMeasurable_and_exists_set_sigmaFinite
    {S X : Type*} [MeasurableSpace S] [TopologicalSpace X] [T2Space X] [Zero X]
    {μ : Measure S} {f : S → X} :
    AEFinStronglyMeasurable f μ ↔ AEStronglyMeasurable f μ ∧
      ∃ t, MeasurableSet t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t) := by
  refine ⟨fun hf ↦ ⟨?_, hf.exists_set_sigmaFinite⟩, ?_⟩
  · obtain ⟨g, hg, hfg⟩ := hf
    exact ⟨g, hg.stronglyMeasurable, hfg⟩
  rintro ⟨hf, t, ht, hzero, hσ⟩
  classical
  have hm := hf.stronglyMeasurable_mk.indicator ht
  refine ⟨t.indicator (hf.mk f), hm.finStronglyMeasurable_of_set_sigmaFinite
    ht (fun x hx ↦ indicator_of_notMem hx _) hσ, ?_⟩
  rw [EventuallyEq, ae_restrict_iff' ht.compl] at hzero
  filter_upwards [hf.ae_eq_mk, hzero] with s hs hz
  by_cases hst : s ∈ t
  · simp [hst, hs]
  · simp [hst, hz hst]

end MeasureTheory
