/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Locally smoothly extendible maps on subsets

`SmoothOnSubset I f` means that a map from a subset of a normed space into a charted
space agrees locally with smooth maps on ambient neighbourhoods. In particular, the
extensions need not glue to one manifold-valued extension. This is the notion of smoothness
used for singular simplices, including at their faces and corners.

The convention follows Lee, *Introduction to Smooth Manifolds*, second edition,
Chapter 18 (smooth singular simplices).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E F G H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ G H} {s : Set E}

/-- A map on a subset is smooth if it has smooth ambient extensions near each point.
No single extension near the entire subset is required. -/
def SmoothOnSubset (I : ModelWithCorners ℝ G H) (f : s → M) : Prop :=
  ∀ x : s, ∃ U ∈ 𝓝 (x : E), ∃ g : E → M,
    ContMDiffOn 𝓘(ℝ, E) I ∞ g U ∧ ∀ y : s, (y : E) ∈ U → g y = f y

/-- Characterize smoothness on a subset by local ambient extensions. -/
theorem smoothOnSubset_iff {f : s → M} :
    SmoothOnSubset I f ↔ ∀ x : s, ∃ U ∈ 𝓝 (x : E), ∃ g : E → M,
      ContMDiffOn 𝓘(ℝ, E) I ∞ g U ∧ ∀ y : s, (y : E) ∈ U → g y = f y :=
  Iff.rfl

/-- Restricting an ambient smooth map gives a locally smoothly extendible map. -/
theorem smoothOnSubset_restrict {g : E → M} (hg : ContMDiff 𝓘(ℝ, E) I ∞ g) :
    SmoothOnSubset I (fun x : s ↦ g x) :=
  fun _ ↦ ⟨univ, univ_mem, g, hg.contMDiffOn, fun _ _ ↦ rfl⟩

namespace SmoothOnSubset

/-- Locally smoothly extendible maps are continuous, including at boundary points. -/
theorem continuous {f : s → M} (hf : SmoothOnSubset I f) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  obtain ⟨U, hU, g, hg, heq⟩ := hf x
  have hc := (hg.continuousOn.continuousAt hU).comp
    (continuous_subtype_val.continuousAt : ContinuousAt (Subtype.val : s → E) x)
  exact hc.congr (Filter.eventuallyEq_of_mem
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hU) (fun y hy ↦ heq y hy))

/-- Restriction to a smaller subset preserves local smooth extendibility. -/
theorem restrict {f : s → M} (hf : SmoothOnSubset I f) {t : Set E} (ht : t ⊆ s) :
    SmoothOnSubset I (fun x : t ↦ f ⟨x, ht x.property⟩) := by
  intro x
  obtain ⟨U, hU, g, hg, heq⟩ := hf ⟨x, ht x.property⟩
  exact ⟨U, hU, g, hg, fun y hy ↦ heq ⟨y, ht y.property⟩ hy⟩

/-- Precomposition by a smooth ambient map carrying one subset into another preserves
local smooth extendibility. -/
theorem comp {f : s → M} (hf : SmoothOnSubset I f) {t : Set F} {g : F → E}
    (hg : ContDiff ℝ ∞ g) (hgs : MapsTo g t s) :
    SmoothOnSubset I (fun x : t ↦ f ⟨g x, hgs x.property⟩) := by
  intro x
  obtain ⟨U, hU, k, hk, heq⟩ := hf ⟨g x, hgs x.property⟩
  exact ⟨g ⁻¹' U, hg.continuous.continuousAt.preimage_mem_nhds hU, k ∘ g,
    hk.comp hg.contMDiff.contMDiffOn (fun _ hy ↦ hy),
    fun y hy ↦ heq ⟨g y, hgs y.property⟩ hy⟩

end SmoothOnSubset

/-- Read local smooth extendibility in coordinates given by an injective parametrization.
This avoids choosing an ambient extension of the inverse parametrization. -/
theorem smoothOnSubset_range_iff {A : Type*} (e : A → E) (he : Function.Injective e)
    (f : A → M) :
    SmoothOnSubset I (f ∘ (Equiv.ofInjective e he).symm) ↔
      ∀ x : A, ∃ U ∈ 𝓝 (e x), ∃ g : E → M,
        ContMDiffOn 𝓘(ℝ, E) I ∞ g U ∧ ∀ y : A, e y ∈ U → g (e y) = f y := by
  constructor
  · intro hf x
    obtain ⟨U, hU, g, hg, heq⟩ := hf ⟨e x, ⟨x, rfl⟩⟩
    refine ⟨U, hU, g, hg, fun y hy ↦ ?_⟩
    simpa only [Function.comp_apply, Equiv.ofInjective_symm_apply] using
      heq ⟨e y, ⟨y, rfl⟩⟩ hy
  · intro hf x
    rcases x with ⟨_, ⟨x, rfl⟩⟩
    obtain ⟨U, hU, g, hg, heq⟩ := hf x
    refine ⟨U, hU, g, hg, ?_⟩
    rintro ⟨y, ⟨y, rfl⟩⟩ hy
    simpa only [Function.comp_apply, Equiv.ofInjective_symm_apply] using heq y hy

end TauCeti
