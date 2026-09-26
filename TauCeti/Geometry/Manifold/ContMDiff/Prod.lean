/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import TauCeti.Geometry.Manifold.ContMDiff.Defs

/-!
# Smooth maps from products

Mathlib equips a product of model vector spaces both with the product of their self-models and
with the self-model of the product. This file provides the `C^n` bridge between those
definitionally distinct presentations.

These bridges are useful when transporting `C^n` and `C^n`-on-a-set statements between product
chart coordinates and the self-model of the product model space.

The file also records a tube lemma: a map from a product which is `C^n` at every point of a
compact slice `{x} × K` is `C^n` on a product of open neighbourhoods of `x` and of `K`.

## Main results

* `contMDiff_prod_modelWithCornersSelf_iff`: a map from a product of model vector spaces is `C^n`
  for the product of the self-models if and only if it is `C^n` for the self-model of the product.
* `contMDiffOn_prod_modelWithCornersSelf_iff`: the same bridge for `C^n` maps on a set.
* `TauCeti.exists_isOpen_prod_contMDiffOn`: the tube lemma for maps from a product which are
  `C^n` along a compact slice.

-/

public section

open Set
open scoped ContDiff Manifold

variable {𝕜 E₁ E₂ E' H' M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H' M]
  {n : WithTop ℕ∞} {f : E₁ × E₂ → M} {s : Set (E₁ × E₂)}

/-- A map from a product of model vector spaces is `C^n` for the product of the self-models if and
only if it is `C^n` for the self-model of the product. -/
theorem contMDiff_prod_modelWithCornersSelf_iff :
    ContMDiff (𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)) I' n f ↔
      ContMDiff 𝓘(𝕜, E₁ × E₂) I' n f := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]

/-- A map from a product of model vector spaces is `C^n` on a set for the product of the
self-models if and only if it is `C^n` on that set for the self-model of the product. -/
theorem contMDiffOn_prod_modelWithCornersSelf_iff :
    ContMDiffOn (𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)) I' n f s ↔
      ContMDiffOn 𝓘(𝕜, E₁ × E₂) I' n f s := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H' (X × Y)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- **The tube lemma for `C^n` maps from a product.** If `f : X × Y → N` is `C^n` at every point
of `{x} × K` with `K` compact and `n ≠ ∞`, then `f` is `C^n` on `U ×ˢ V` for some open
neighbourhoods `U` of `x` and `V` of `K`. -/
theorem exists_isOpen_prod_contMDiffOn [IsManifold I' n (X × Y)] [IsManifold J n N]
    {f : X × Y → N} {x : X} {K : Set Y} (hK : IsCompact K) (hn : n ≠ ∞)
    (hf : ∀ y ∈ K, ContMDiffAt I' J n f (x, y)) :
    ∃ U V, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ K ⊆ V ∧ ContMDiffOn I' J n f (U ×ˢ V) := by
  have hsub : {x} ×ˢ K ⊆ {z | ContMDiffAt I' J n f z} := by
    rintro ⟨x', y⟩ ⟨hx', hy⟩
    rw [mem_singleton_iff] at hx'
    subst hx'
    exact hf y hy
  obtain ⟨U, V, hUo, hVo, hU, hV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hK (isOpen_setOfPred_contMDiffAt hn) hsub
  exact ⟨U, V, hUo, hVo, hU (mem_singleton x), hV, fun z hz ↦ (hUV hz).contMDiffWithinAt⟩

end TauCeti
