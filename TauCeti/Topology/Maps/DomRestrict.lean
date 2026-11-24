/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Topology.ContinuousOn

/-!
# Restrictions of maps that are open or inducing

The restriction `s.domRestrict f` of a map `f : X → Y` to a subset `s ⊆ X` is an open map exactly
when, for each point `x ∈ s`, the image under `f` of every neighbourhood of `x` in `s` is a
neighbourhood of `f x` (`TauCeti.isOpenMap_domRestrict_iff`). The relatively open subsets of `s`
are the traces `t ∩ s` of open sets of `X`, so this is a pointwise test that does not mention the
subtype topology. When `f` is the projection of a cylinder to its base, it describes the sets whose
projection is open on every relatively open subset.

If `s.domRestrict f` is inducing, then `Function.invFunOn f s`, a right inverse of `f` on `f '' s`
that selects a preimage in `s`, is continuous on `f '' s`
(`Topology.IsInducing.continuousOn_invFunOn`). If moreover `f` is injective on `s`, then the inverse
of the partial equivalence `Set.InjOn.toPartialEquiv f s` is continuous on its target `f '' s`
(`Topology.IsInducing.continuousOn_toPartialEquiv_symm`), so `f` maps `s` homeomorphically onto
`f '' s`.
-/

public section

open Function Set Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The restriction of `f` to `s` is an open map if and only if, for every `x ∈ s` and every
neighbourhood `t` of `x`, the image `f '' (t ∩ s)` is a neighbourhood of `f x`. -/
theorem isOpenMap_domRestrict_iff {f : X → Y} {s : Set X} :
    IsOpenMap (s.domRestrict f) ↔ ∀ x ∈ s, ∀ t ∈ 𝓝 x, f '' (t ∩ s) ∈ 𝓝 (f x) := by
  refine ⟨fun h x hx t ht ↦ ?_, fun h V hV ↦ ?_⟩
  · rw [← image_domRestrict]
    exact h.image_mem_nhds (x := ⟨x, hx⟩) (continuous_subtypeVal.continuousAt.preimage_mem_nhds ht)
  · obtain ⟨t, ht, rfl⟩ := isOpen_induced_iff.1 hV
    rw [image_domRestrict, isOpen_iff_mem_nhds]
    rintro _ ⟨x, ⟨hxt, hxs⟩, rfl⟩
    exact h x hxs t (ht.mem_nhds hxt)

end TauCeti

/-- If the restriction of `f` to `s` is inducing, then `invFunOn f s`, a right inverse of `f` on
`f '' s` that selects a preimage in `s`, is continuous on `f '' s`. Injectivity of `f` on `s` is not
needed: `f (invFunOn f s y) = y` for `y ∈ f '' s`, and a map into `s` is continuous as soon as its
composite with `s.domRestrict f` is. -/
theorem Topology.IsInducing.continuousOn_invFunOn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] {f : X → Y} {s : Set X}
    (hf : IsInducing (s.domRestrict f)) : ContinuousOn (invFunOn f s) (f '' s) := by
  let g : f '' s → s := fun y ↦ ⟨invFunOn f s y, invFunOn_mem y.property⟩
  have hg : Continuous g :=
    hf.continuous_iff.2 (continuous_subtypeVal.congr fun y ↦ (invFunOn_eq y.property).symm)
  exact continuousOn_iff_continuous_domRestrict.2 (continuous_subtypeVal.comp hg)

/-- If the restriction of `f` to `s` is inducing and `f` is injective on `s`, then the inverse of
the partial equivalence `hinj.toPartialEquiv f s` is continuous on its target `f '' s`. -/
theorem Topology.IsInducing.continuousOn_toPartialEquiv_symm {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] {f : X → Y} {s : Set X} (hf : IsInducing (s.domRestrict f))
    (hinj : InjOn f s) :
    ContinuousOn (hinj.toPartialEquiv f s).symm (hinj.toPartialEquiv f s).target := by
  rw [InjOn.toPartialEquiv, BijOn.toPartialEquiv_symm_apply, BijOn.toPartialEquiv_target]
  exact hf.continuousOn_invFunOn
