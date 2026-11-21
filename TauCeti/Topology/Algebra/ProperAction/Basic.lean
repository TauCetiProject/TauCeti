/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.TypeTags
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Topology.Maps.Proper.Basic

/-!
# Proper actions: compact groups, invariant subspaces, and type tags

A continuous action of a compact group `G` on a Hausdorff space `X` is proper: the map
`(g, x) ↦ (g • x, x)` is proper because its first coordinate ranges over a compact space. In
particular the orbit space `X ⧸ G` is Hausdorff (`t2Space_quotient_mulAction_of_properSMul`), which
is how quotients such as complex projective space, the orbit space of the circle acting on an odd
sphere, are shown to be Hausdorff.

Even without a separation axiom on `X`, the quotient map `X → X ⧸ G` of a continuous action of a
compact group is closed, because the saturation of a closed set `A` is the projection to `X` of the
closed set `{(g, x) | g • x ∈ A}` of `G × X`, and the projection `G × X → X` is a closed map. Its
fibres are orbits, continuous images of `G`, so it is proper.

A proper action also restricts to a proper action on every invariant subspace, and more generally
pulls back along any equivariant topological embedding. It even pulls back to a subgroup acting on
a subspace, as long as every element of the group carrying a point of the subspace into the
subspace lies in the subgroup. This is the topological half of restricting a free proper action
to a level of an equivariant map, acted on by the stabilizer of the value, before taking its
quotient. Properness also pulls back along continuous equivariant maps out of Hausdorff spaces,
such as the projection of a cotangent bundle carrying the cotangent-lifted action.

This file also transfers `ProperVAdd` and `ProperSMul` across the `Multiplicative` and `Additive`
type tags (`Multiplicative.properSMul`, `Additive.properVAdd`).

## Main results

* `TauCeti.properSMul_of_compactSpace`, `TauCeti.properVAdd_of_compactSpace`: a continuous action
  of a compact group, or of a compact additive group, on a Hausdorff space is proper.
* `Multiplicative.properSMul`, `Additive.properVAdd`: properness transfers across the
  `Multiplicative` and `Additive` type tags on the acting group.
* `MulAction.isClosedMap_quotientMk_of_compactSpace`,
  `MulAction.isProperMap_quotientMk_of_compactSpace`: for a continuous action of a compact group,
  with no separation axiom, the quotient map `X → X ⧸ G` is closed and proper.
* `Topology.IsEmbedding.properSMul`: an action which a topological embedding intertwines with a
  proper action is proper.
* `Topology.IsEmbedding.properSMul_of_isEmbedding`: the same along a topological embedding of
  the acting groups, provided the elements of the larger group carrying a point of the image into
  the image come from the smaller group.
* `Continuous.properSMul`: a continuous action on a Hausdorff space which a continuous map
  intertwines with a proper action is proper.
* `ProperSMul.prod_of_smul_eq`: a factorwise action of a product of groups, each acting properly
  on its factor, is proper.
-/

public section

/-- A proper additive group action becomes a proper multiplicative action of `Multiplicative G`. -/
instance Multiplicative.properSMul {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
    [AddGroup G] [AddAction G X] [ProperVAdd G X] : ProperSMul (Multiplicative G) X where
  isProperMap_smul_pair := ProperVAdd.isProperMap_vadd_pair (G := G) (X := X)

/-- A proper multiplicative group action becomes a proper additive action of `Additive G`. -/
instance Additive.properVAdd {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
    [Group G] [MulAction G X] [ProperSMul G X] : ProperVAdd (Additive G) X where
  isProperMap_vadd_pair := ProperSMul.isProperMap_smul_pair (G := G) (X := X)

namespace TauCeti

/-- **A continuous action of a compact group on a Hausdorff space is proper.** This is not an
instance, since `ProperSMul` itself provides `ContinuousSMul`. -/
@[to_additive /-- **A continuous action of a compact additive group on a Hausdorff space is
proper.** This is not an instance, since `ProperVAdd` itself provides `ContinuousVAdd`. -/]
theorem properSMul_of_compactSpace (G X : Type*) [Group G] [TopologicalSpace G] [CompactSpace G]
    [MulAction G X] [TopologicalSpace X] [T2Space X] [ContinuousSMul G X] : ProperSMul G X :=
  properSMul_iff_continuousSMul_ultrafilter_tendsto.2 ⟨inferInstance, fun 𝒰 _ _ hxx ↦ by
    -- In the compact space `G` the ultrafilter `𝒰.map Prod.fst` converges to its limit.
    have hg : Filter.Tendsto Prod.fst (𝒰 : Filter (G × X)) (nhds (𝒰.map Prod.fst).lim) := by
      rw [Filter.Tendsto, ← Ultrafilter.coe_map]
      exact (𝒰.map Prod.fst).le_nhds_lim
    exact ⟨_, tendsto_nhds_unique (hg.smul ((continuous_snd.tendsto _).comp hxx))
      ((continuous_fst.tendsto _).comp hxx), hg⟩⟩

end TauCeti

namespace MulAction

variable {G X : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [MulAction G X]
  [TopologicalSpace X] [ContinuousSMul G X]

/-- **The orbit map of a compact group is closed.** For a continuous action of a compact group `G`
on `X`, the quotient map `X → X ⧸ G` is closed. -/
@[to_additive /-- **The orbit map of a compact additive group is closed.** For a continuous
additive action of a compact additive group `G` on `X`, the quotient map `X → X ⧸ G` is
closed. -/]
theorem isClosedMap_quotientMk_of_compactSpace : IsClosedMap (Quotient.mk (orbitRel G X)) :=
  fun A hA ↦ by
    rw [← isOpenQuotientMap_quotientMk.isQuotientMap.isClosed_preimage]
    convert isClosedMap_snd_of_compactSpace _ (hA.preimage (continuous_smul (M := G) (X := X)))
    ext x
    simp only [Set.mem_preimage, Set.mem_image, Quotient.eq, orbitRel_apply, mem_orbit_iff,
      Prod.exists]
    exact ⟨fun ⟨_, ha, g, hg⟩ ↦ ⟨g, x, hg ▸ ha, rfl⟩, fun ⟨g, _, ha, rfl⟩ ↦ ⟨_, ha, g, rfl⟩⟩

/-- **The orbit map of a compact group is proper.** For a continuous action of a compact group `G`
on `X`, the quotient map `X → X ⧸ G` is proper. -/
@[to_additive /-- **The orbit map of a compact additive group is proper.** For a continuous
additive action of a compact additive group `G` on `X`, the quotient map `X → X ⧸ G` is
proper. -/]
theorem isProperMap_quotientMk_of_compactSpace : IsProperMap (Quotient.mk (orbitRel G X)) := by
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨continuous_quotient_mk', isClosedMap_quotientMk_of_compactSpace, fun y ↦ ?_⟩
  induction y using Quotient.inductionOn with | h x => ?_
  convert isCompact_range (continuous_smul.comp (Continuous.prodMk_left (X := G) x))
  ext w
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, orbitRel_apply, mem_orbit_iff,
    Set.mem_range, Function.comp_apply]

end MulAction

open Filter Topology in
/-- **Proper actions pull back along slices.** Let `φ : H → G` be a topological embedding between
groups and `f : Y → X` a topological embedding intertwining an action of `H` on `Y` with a proper
action of `G` on `X`, `f (h • y) = φ h • f y`. If every element of `G` carrying a point of the image
of `f` into the image of `f` comes from `H`, then the action of `H` on `Y` is proper. For instance
the coadjoint stabilizer of a value of an equivariant map acts properly on the corresponding
level. -/
@[to_additive /-- **Proper additive actions pull back along slices.** Let `φ : H → G` be a
topological embedding between additive groups and `f : Y → X` a topological embedding
intertwining an additive action of `H` on `Y` with a proper additive action of `G` on `X`. If every
element of `G` carrying a point of the image of `f` into the image of `f` comes from `H`, then the
additive action of `H` on `Y` is proper. -/]
theorem Topology.IsEmbedding.properSMul_of_isEmbedding {G H X Y : Type*} [Group G]
    [TopologicalSpace G] [MulAction G X] [TopologicalSpace X] [ProperSMul G X] [Group H]
    [TopologicalSpace H] [MulAction H Y] [TopologicalSpace Y] {f : Y → X} (hf : IsEmbedding f)
    {φ : H → G} (hφ : IsEmbedding φ) (hsmul : ∀ (h : H) (y : Y), f (h • y) = φ h • f y)
    (hrange : ∀ (g : G) (y y' : Y), g • f y = f y' → ∃ h : H, φ h = g) :
    ProperSMul H Y where
  isProperMap_smul_pair := by
    refine ProperSMul.isProperMap_smul_pair.of_isEmbedding_of_range_eq (hφ.prodMap hf)
      (hf.prodMap hf) (funext fun p ↦ by simp [hsmul]) (Set.ext fun ⟨g, x⟩ ↦ ⟨?_, ?_⟩)
    · rintro ⟨⟨h, y⟩, hp⟩
      simp only [Prod.map_apply, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨(h • y, y), by simp [hsmul]⟩
    · rintro ⟨⟨y', y⟩, hp⟩
      simp only [Prod.map_apply, Prod.mk.injEq] at hp
      obtain ⟨hy', rfl⟩ := hp
      obtain ⟨h, rfl⟩ := hrange g y y' (by rw [hy'])
      exact ⟨(h, y), rfl⟩

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
  hf.properSMul_of_isEmbedding IsEmbedding.id hsmul fun g _ _ _ ↦ ⟨g, rfl⟩

open Filter in
/-- **Proper actions pull back along continuous equivariant maps.** If a continuous map
`f : Y → X` into a space with a proper action of `G` intertwines it with a continuous action of `G`
on a Hausdorff space `Y`, then the action on `Y` is proper. For instance the cotangent lift of a
proper action is proper, through the bundle projection. -/
theorem Continuous.properSMul {G X Y : Type*} [Group G] [TopologicalSpace G] [MulAction G X]
    [TopologicalSpace X] [ProperSMul G X] [MulAction G Y] [TopologicalSpace Y] [T2Space Y]
    [ContinuousSMul G Y] {f : Y → X} (hf : Continuous f)
    (hsmul : ∀ (g : G) (y : Y), f (g • y) = g • f y) : ProperSMul G Y := by
  refine properSMul_iff_continuousSMul_ultrafilter_tendsto_t2.2 ⟨inferInstance, fun 𝒰 y₁ y₂ h ↦ ?_⟩
  -- Push the ultrafilter forward along `id × f`, where the action on `X` is proper.
  have hX : Tendsto (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) (𝒰.map (Prod.map id f))
      (nhds (f y₁, f y₂)) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    refine (((hf.prodMap hf).tendsto (y₁, y₂)).comp h).congr fun gy ↦ ?_
    simp [hsmul]
  obtain ⟨g, -, hg⟩ := (properSMul_iff_continuousSMul_ultrafilter_tendsto.1 ‹_›).2 _ _ _ hX
  rw [Ultrafilter.coe_map, tendsto_map'_iff] at hg
  exact ⟨g, hg⟩

/-- **Products of proper actions are proper.** If `G` acts properly on `X` and `K` acts properly on
`Y`, then an action of `G × K` on `X × Y` acting factorwise, `(g, k) • (x, y) = (g • x, k • y)`,
is proper: up to reordering the factors, its map `((g, k), (x, y)) ↦ ((g, k) • (x, y), (x, y))` is
the product of the proper maps of the two actions. -/
@[to_additive /-- **Products of proper additive actions are proper.** If `G` acts properly on `X`
and `K` acts properly on `Y`, then an additive action of `G × K` on `X × Y` acting factorwise,
`(g, k) +ᵥ (x, y) = (g +ᵥ x, k +ᵥ y)`, is proper. -/]
theorem ProperSMul.prod_of_smul_eq {G K X Y : Type*} [Group G] [Group K] [TopologicalSpace G]
    [TopologicalSpace K] [TopologicalSpace X] [TopologicalSpace Y] [MulAction G X]
    [MulAction K Y] [ProperSMul G X] [ProperSMul K Y] [MulAction (G × K) (X × Y)]
    (hsmul : ∀ (g : G × K) (p : X × Y), g • p = (g.1 • p.1, g.2 • p.2)) :
    ProperSMul (G × K) (X × Y) where
  isProperMap_smul_pair := by
    have h := ((Homeomorph.prodProdProdComm X X Y Y).isProperMap.comp
      ((ProperSMul.isProperMap_smul_pair (G := G) (X := X)).prodMap
        (ProperSMul.isProperMap_smul_pair (G := K) (X := Y)))).comp
      (Homeomorph.prodProdProdComm G K X Y).isProperMap
    convert h using 1
    funext ⟨⟨g, k⟩, x, y⟩
    simp [hsmul, Homeomorph.prodProdProdComm]
