/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import TauCeti.Analysis.Normed.Module.Dual.Norming
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.Metric

/-!
# Pettis measurability with norming scalar tests

For functions taking values in a separable linear subspace, a norming family of
continuous linear functionals detects strong measurability. In particular, a function
into a real or complex normed space is strongly measurable exactly when its range is
separable and every scalar evaluation is measurable. Neither the ambient space nor the
supporting subspace needs to be complete.

The full-dual criterion is also stated using a closed separable supporting subspace.
Countable extraction of norming tests and the distance criterion provide the proof,
without imposing a measurable structure on the target.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*,
  Volume I, Proposition 1.1.1 and Corollaries 1.1.2 and 1.1.10.
-/

public section

open MeasureTheory Set TopologicalSpace

section Norming

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Norming scalar tests detect strong measurability on a separable supporting linear
subspace, even when that subspace is incomplete. -/
theorem Submodule.stronglyMeasurable_iff_norming_tests (S : Submodule 𝕜 E)
    (hS : IsSeparable (S : Set E)) (D : Set (StrongDual 𝕜 E))
    (hD : ∀ x ∈ S, IsLUB ((fun φ : StrongDual 𝕜 E ↦ ‖φ x‖) '' D) ‖x‖)
    (f : α → E) (hf : ∀ a, f a ∈ S) :
    StronglyMeasurable f ↔ ∀ φ ∈ D, Measurable (fun a ↦ φ (f a)) := by
  refine ⟨fun h φ _ ↦ (φ.continuous.comp_stronglyMeasurable h).measurable, fun h ↦ ?_⟩
  obtain ⟨D', hsub, hcount, hnorm⟩ := hS.exists_countable_dual_norming_subset hD
  have := hcount.to_subtype
  have := hS.separableSpace
  let g : α → S := fun a ↦ ⟨f a, hf a⟩
  have hg : StronglyMeasurable g := by
    refine (TauCeti.stronglyMeasurable_iff_measurable_dist g).2 ⟨.of_separableSpace _, ?_⟩
    intro x
    simp only [dist_eq_norm]
    refine Measurable.isLUB (f := fun φ : D' ↦ fun a ↦ ‖φ.val (f a) - φ.val x‖)
      (fun φ ↦ ((h φ (hsub φ.property)).sub_const _).norm) ?_
    intro a
    simpa [Set.image, Set.range, Subtype.exists, map_sub, g,
      ← Submodule.norm_coe, Submodule.coe_sub] using
      hnorm (f a - x) (S.sub_mem (hf a) x.property)
  exact continuous_subtypeVal.comp_stronglyMeasurable hg

end Norming

namespace TauCeti

variable {α 𝕜 E : Type*} [MeasurableSpace α] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The range-separability form of Pettis' measurability theorem for an arbitrary normed
target over the real or complex numbers. -/
theorem stronglyMeasurable_iff_isSeparable_scalar_tests (f : α → E) :
    StronglyMeasurable f ↔ IsSeparable (range f) ∧
      ∀ φ : StrongDual 𝕜 E, Measurable (fun a ↦ φ (f a)) := by
  refine ⟨fun hf ↦ ⟨hf.isSeparable_range,
    fun φ ↦ (φ.continuous.comp_stronglyMeasurable hf).measurable⟩, fun ⟨hs, htests⟩ ↦ ?_⟩
  let S := Submodule.span 𝕜 (range f)
  have hS : IsSeparable (S : Set E) := hs.span
  obtain ⟨D, -, -, hD⟩ := hS.exists_countable_dual_norming (𝕜 := 𝕜)
  exact (S.stronglyMeasurable_iff_norming_tests hS D hD f
    (fun a ↦ Submodule.subset_span (mem_range_self a))).2 (fun φ _ ↦ htests φ)

/-- **Pettis measurability theorem** for real or complex normed targets: strong measurability
is equivalent to a closed separable supporting linear subspace and measurable scalar tests.
No completeness assumption is required. -/
theorem stronglyMeasurable_iff_scalar_tests (f : α → E) :
    StronglyMeasurable f ↔
      (∃ S : Submodule 𝕜 E, IsClosed (S : Set E) ∧ IsSeparable (S : Set E) ∧
        ∀ a, f a ∈ S) ∧
      ∀ φ : StrongDual 𝕜 E, Measurable (fun a ↦ φ (f a)) := by
  refine ⟨fun hf ↦ ⟨?_, fun φ ↦ (φ.continuous.comp_stronglyMeasurable hf).measurable⟩,
    fun ⟨⟨S, _hclosed, hS, hf⟩, htests⟩ ↦ ?_⟩
  · refine ⟨(Submodule.span 𝕜 (range f)).topologicalClosure,
      (Submodule.span 𝕜 (range f)).isClosed_topologicalClosure, ?_, ?_⟩
    · rw [Submodule.topologicalClosure_coe]
      exact hf.isSeparable_range.span.closure
    · intro a
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self a))
  · exact (stronglyMeasurable_iff_isSeparable_scalar_tests (𝕜 := 𝕜) f).2
      ⟨hS.mono (range_subset_iff.mpr hf), htests⟩

end TauCeti
