/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Proper actions: compact groups and invariant subspaces

A continuous action of a compact group `G` on a Hausdorff space `X` is proper: the map
`(g, x) ↦ (g • x, x)` is proper because its first coordinate ranges over a compact space. In
particular the orbit space `X ⧸ G` is Hausdorff (`t2Space_quotient_mulAction_of_properSMul`), which
is how quotients such as complex projective space, the orbit space of the circle acting on an odd
sphere, are shown to be Hausdorff.

A proper action also restricts to a proper action on every invariant subspace, and more generally
pulls back along any equivariant topological embedding. It even pulls back to a subgroup acting on
a subspace, as long as every element of the group carrying a point of the subspace into the
subspace lies in the subgroup. This is the topological half of restricting a free proper action
to a level of an equivariant map, acted on by the stabilizer of the value, before taking its
quotient.

## Main results

* `TauCeti.properSMul_of_compactSpace`, `TauCeti.properVAdd_of_compactSpace`: a continuous action
  of a compact group, or of a compact additive group, on a Hausdorff space is proper.
* `Topology.IsEmbedding.properSMul`: an action which a topological embedding intertwines with a
  proper action is proper.
* `Topology.IsEmbedding.properSMul_of_monoidHom`: the same along an embedding of groups, provided
  the elements of the larger group carrying a point of the image into the image come from the
  smaller group.
-/

public section

namespace TauCeti

/-- **A continuous action of a compact group on a Hausdorff space is proper.** This is not an
instance, since `ProperSMul` itself provides `ContinuousSMul`. -/
@[to_additive /-- **A continuous action of a compact additive group on a Hausdorff space is
proper.** This is not an instance, since `ProperVAdd` itself provides `ContinuousVAdd`. -/]
theorem properSMul_of_compactSpace (G X : Type*) [Group G] [TopologicalSpace G] [CompactSpace G]
    [MulAction G X] [TopologicalSpace X] [T2Space X] [ContinuousSMul G X] : ProperSMul G X :=
  properSMul_iff_continuousSMul_ultrafilter_tendsto.2 ⟨inferInstance, fun 𝒰 _ _ hxx ↦ by
    obtain ⟨g, -, hg⟩ := isCompact_univ.ultrafilter_le_nhds (𝒰.map Prod.fst) (by simp)
    -- `Tendsto Prod.fst 𝒰 (𝓝 g)` is by definition `map Prod.fst 𝒰 ≤ 𝓝 g`.
    rw [Ultrafilter.coe_map] at hg
    change Filter.Tendsto (Prod.fst : G × X → G) 𝒰 (nhds g) at hg
    exact ⟨g, tendsto_nhds_unique (hg.smul ((continuous_snd.tendsto _).comp hxx))
      ((continuous_fst.tendsto _).comp hxx), hg⟩⟩

end TauCeti

open Filter Topology in
/-- **Proper actions pull back along slices.** Let `φ : H →* G` be a topological embedding of
groups and `f : Y → X` a topological embedding intertwining an action of `H` on `Y` with a proper
action of `G` on `X`, `f (h • y) = φ h • f y`. If every element of `G` carrying a point of the image
of `f` into the image of `f` comes from `H`, then the action of `H` on `Y` is proper. For instance
the coadjoint stabilizer of a value of an equivariant map acts properly on the corresponding
level. -/
@[to_additive /-- **Proper additive actions pull back along slices.** Let `φ : H →+ G` be a
topological embedding of additive groups and `f : Y → X` a topological embedding intertwining an
additive action of `H` on `Y` with a proper additive action of `G` on `X`. If every element of `G`
carrying a point of the image of `f` into the image of `f` comes from `H`, then the additive
action of `H` on `Y` is proper. -/]
theorem Topology.IsEmbedding.properSMul_of_monoidHom {G H X Y : Type*} [Group G]
    [TopologicalSpace G] [MulAction G X] [TopologicalSpace X] [ProperSMul G X] [Group H]
    [TopologicalSpace H] [MulAction H Y] [TopologicalSpace Y] {f : Y → X} (hf : IsEmbedding f)
    {φ : H →* G} (hφ : IsEmbedding φ) (hsmul : ∀ (h : H) (y : Y), f (h • y) = φ h • f y)
    (hrange : ∀ (g : G) (y y' : Y), g • f y = f y' → ∃ h : H, φ h = g) :
    ProperSMul H Y := by
  have : ContinuousSMul H Y := hf.isInducing.continuousSMul hφ.continuous (hsmul _ _)
  refine properSMul_iff_continuousSMul_ultrafilter_tendsto.2 ⟨inferInstance, fun 𝒰 y₁ y₂ h𝒰 ↦ ?_⟩
  have hcomp : (Prod.map f f ∘ fun p : H × Y ↦ (p.1 • p.2, p.2)) =
      (fun p : G × X ↦ (p.1 • p.2, p.2)) ∘ Prod.map φ f :=
    funext fun p ↦ by simp [hsmul]
  have hX : Tendsto (fun p : G × X ↦ (p.1 • p.2, p.2)) (𝒰.map (Prod.map φ f))
      (𝓝 (f y₁, f y₂)) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff, ← hcomp]
    exact (hf.continuous.prodMap hf.continuous).continuousAt.tendsto.comp h𝒰
  obtain ⟨g, hg, hg𝒰⟩ :=
    (properSMul_iff_continuousSMul_ultrafilter_tendsto.1 ‹ProperSMul G X›).2 _ _ _ hX
  obtain ⟨h, rfl⟩ := hrange g y₂ y₁ hg
  refine ⟨h, hf.injective (by rw [hsmul, hg]), ?_⟩
  rw [hφ.isInducing.tendsto_nhds_iff]
  rwa [Ultrafilter.coe_map, tendsto_map'_iff] at hg𝒰

open Topology in
/-- **Proper actions restrict to invariant subspaces.** If a topological embedding `f : Y → X`
intertwines an action of `G` on `Y` with a proper action of `G` on `X`, then the action on `Y` is
proper. For instance a proper action restricts to a proper action on an invariant subset, with the
action of the corresponding `SubMulAction`. -/
@[to_additive /-- If a topological embedding `f : Y → X` intertwines an additive action of `G` on
`Y` with a proper additive action of `G` on `X`, then the additive action on `Y` is proper. -/]
theorem Topology.IsEmbedding.properSMul {G X Y : Type*} [Group G] [TopologicalSpace G]
    [MulAction G X] [TopologicalSpace X] [ProperSMul G X] [MulAction G Y] [TopologicalSpace Y]
    {f : Y → X} (hf : IsEmbedding f) (hsmul : ∀ (g : G) (y : Y), f (g • y) = g • f y) :
    ProperSMul G Y :=
  hf.properSMul_of_monoidHom (φ := MonoidHom.id G) IsEmbedding.id hsmul fun g _ _ _ ↦ ⟨g, rfl⟩
