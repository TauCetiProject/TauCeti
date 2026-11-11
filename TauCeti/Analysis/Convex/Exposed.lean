/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv
public import TauCeti.Analysis.Convex.Intrinsic

/-!
# Exposed sets, relative interiors and continuous affine equivalences

An exposed subset of a set `P` which meets the intrinsic interior of `P` is all of `P`
(`IsExposed.eq_of_mem_intrinsicInterior`): the exposing functional is maximal at an intrinsic
interior point, hence constant on `P`. Continuous affine equivalences carry exposed subsets to
exposed subsets (`IsExposed.image_continuousAffineEquiv`): composing an exposing functional with
the inverse linear part preserves all comparisons, since the inverse translation contributes the
same additive constant at every point. The part of an exposed subset in a subset of the ambient
set is exposed in that subset (`IsExposed.inter_of_subset`).

Adapted from `Mei/Analysis/Convex/Exposed.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace IsExposed

section Restrict

variable {𝕜 E : Type*} [TopologicalSpace 𝕜] [Ring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {A F Q : Set E}

/-- Shrinking the ambient set of an exposed subset: the part of `F` in a subset `Q` of `A` is
exposed in `Q`. -/
theorem inter_of_subset (hF : IsExposed 𝕜 A F) (hQA : Q ⊆ A) : IsExposed 𝕜 Q (F ∩ Q) := by
  rintro ⟨x, hxF, hxQ⟩
  obtain ⟨l, rfl⟩ := hF ⟨x, hxF⟩
  exact ⟨l, Set.Subset.antisymm (fun z hz => ⟨hz.2, fun y hy => hz.1.2 y (hQA hy)⟩)
    fun z hz => ⟨⟨hQA hz.1, fun y hy => (hxF.2 y hy).trans (hz.2 x hxQ)⟩, hz.1⟩⟩

end Restrict

section IntrinsicInterior

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P F : Set V}

/-- An exposed subset meeting the intrinsic interior of its ambient set is the whole set.
Neither convexity nor finite dimensionality is required. -/
theorem eq_of_mem_intrinsicInterior (hF : IsExposed ℝ P F) {x : V} (hxF : x ∈ F)
    (hx : x ∈ intrinsicInterior ℝ P) : F = P := by
  obtain ⟨l, rfl⟩ := hF ⟨x, hxF⟩
  refine Set.Subset.antisymm (fun _ hy => hy.1) fun p hp => ⟨hp, fun q hq => ?_⟩
  have hg := TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior
    (g := AffineMap.const ℝ V (l x) - l.toLinearMap.toAffineMap)
    (fun y hy => by simpa using hxF.2 y hy) hx (by simp) hp
  simp only [AffineMap.coe_sub, Pi.sub_apply, AffineMap.const_apply, sub_eq_zero] at hg
  simpa [hg] using hxF.2 q hq

end IntrinsicInterior

section ContinuousAffineEquiv

variable {V W : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module ℝ V]
  [AddCommGroup W] [TopologicalSpace W] [Module ℝ W] [IsTopologicalAddGroup W]
  {P F : Set V}

/-- Continuous affine equivalences preserve exposed subsets. -/
theorem image_continuousAffineEquiv (hF : IsExposed ℝ P F) (e : V ≃ᴬ[ℝ] W) :
    IsExposed ℝ (e '' P) (e '' F) := by
  intro hne
  obtain ⟨l, hl⟩ := hF hne.of_image
  set g := e.symm.toContinuousAffineMap
  have hval (y : W) : l (e.symm y) = l (g.contLinear y) + l (e.symm 0) := by
    rw [← map_add]
    congr 1
    have := g.map_vadd 0 y
    simp only [vadd_eq_add, add_zero] at this
    exact this
  refine ⟨l.comp g.contLinear, ?_⟩
  ext y
  have hcmp (a b : W) : l.comp g.contLinear a ≤ l.comp g.contLinear b ↔
      l (e.symm a) ≤ l (e.symm b) := by
    simp only [hval a, hval b, add_le_add_iff_right, ContinuousLinearMap.comp_apply]
  simp only [hl, Set.mem_image, Set.mem_ofPred_eq, hcmp]
  constructor
  · rintro ⟨x, ⟨hxP, hxmax⟩, rfl⟩
    refine ⟨⟨x, hxP, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa using hxmax z hz
  · rintro ⟨⟨x, hxP, rfl⟩, hmax⟩
    exact ⟨x, ⟨hxP, fun z hz => by simpa using hmax (e z) ⟨z, hz, rfl⟩⟩, rfl⟩

end ContinuousAffineEquiv

end IsExposed
