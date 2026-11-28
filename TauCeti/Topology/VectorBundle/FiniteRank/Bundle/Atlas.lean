/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

import TauCeti.Topology.FiberBundle.TotalSpace

/-!
# The coordinate atlas of a variable-rank vector bundle

A genuine finite-rank bundle `E : TauCeti.FiniteRankBundle.{w} 𝕜 X` has fibres in an arbitrary
universe `w`, while a variable-rank atlas `TauCeti.FiniteRankAtlas 𝕜 X` stores only the rank and
point-indexed coordinate cores on the clopen rank strata, all in the universes of `X` and `𝕜`.
This file defines the comparison functor from genuine bundles to small atlases.

`FiniteRankBundle.toAtlas E` is the atlas of the preferred stratum trivializations of `E`, and
`FiniteRankBundle.toAtlasHomeomorph E` identifies the total space of `E` with the reconstructed
total space of that atlas, over the identity of `X` and by the preferred chart
`FiniteRankBundle.fiberContinuousLinearEquiv` on each fibre. Conjugating bundle maps by these
identifications gives the additive functor `FiniteRankBundle.toAtlasFunctor`, which is fully
faithful (`FiniteRankBundle.fullyFaithfulToAtlasFunctor`). Hence in every fibre universe the
category of genuine bundles is essentially small, in the universe of `X` and `𝕜`
(`FiniteRankBundle.instEssentiallySmall`).

For the reconstruction of a genuine bundle from an atlas in any fibre universe `w` satisfying
`UnivLE.{v, w}` see `TauCeti.Topology.VectorBundle.FiniteRank.Bundle.OfAtlas`, and for the
resulting categorical equivalence `FiniteRankBundle.atlasEquivalence` see
`TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Equivalence`.

## Main definitions

* `TauCeti.FiniteRankBundle.toAtlas`: the coordinate atlas of a genuine bundle.
* `TauCeti.FiniteRankBundle.toAtlasFunctor`: the comparison functor
  `FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X`.

## Main results

* `TauCeti.FiniteRankBundle.fullyFaithfulToAtlasFunctor`: the comparison functor is fully
  faithful in every fibre universe.
* `TauCeti.FiniteRankBundle.instEssentiallySmall`: genuine bundles form an essentially small
  category.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press (1951), Part I, §2–3,
  for coordinate bundles and the construction of a bundle from its coordinate transformations.
-/

public section

open Bundle CategoryTheory

namespace TauCeti

universe w u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankBundle

variable (E : FiniteRankBundle.{w} 𝕜 X) {F G : FiniteRankBundle.{w} 𝕜 X}

/-! ### The atlas of a genuine bundle -/

/-- The small coordinate atlas of a genuine variable-rank bundle: on each clopen rank stratum, the
point-indexed core of the preferred trivializations of `E`. -/
-- Reducible, so that the atlas fibres are the coordinate fibres `Fin (E.rank x) → 𝕜` and the
-- reconstruction API of `FiniteRankAtlas.ofBundles` applies to it.
noncomputable abbrev toAtlas : FiniteRankAtlas 𝕜 X :=
  FiniteRankAtlas.ofBundles 𝕜 E.rank E.StratumFiber

/-- The total space of a genuine bundle is homeomorphic, over `X`, to the reconstructed total space
of its atlas. On each fibre it is the preferred chart `E.fiberContinuousLinearEquiv`. -/
noncomputable def toAtlasHomeomorph :
    TotalSpace Unit E.Fiber ≃ₜ TotalSpace Unit E.toAtlas.Fiber :=
  E.totalSpaceHomeomorph.symm.trans
    (FiniteRankAtlas.reconstructionHomeomorph 𝕜 E.rank E.StratumFiber).symm

@[simp] theorem toAtlasHomeomorph_apply (p : TotalSpace Unit E.Fiber) :
    E.toAtlasHomeomorph p = ⟨p.proj, E.fiberContinuousLinearEquiv p.proj p.snd⟩ := by
  rw [toAtlasHomeomorph, Homeomorph.trans_apply, totalSpaceHomeomorph_symm_apply,
    FiniteRankAtlas.reconstructionHomeomorph_symm_apply, FiniteRankAtlas.totalSpaceHomeomorph_apply]
  simp only [pointIndexedCoreFiberEquiv_symm_apply, fiberContinuousLinearEquiv_apply]
  -- The remaining `Fin.cast` reindexes along `E.toAtlas.rank x = E.rank x`, which is
  -- `FiniteRankAtlas.rank_ofBundles` and holds by `rfl`, so it is the identity.
  rfl

@[simp] theorem toAtlasHomeomorph_symm_apply (p : TotalSpace Unit E.toAtlas.Fiber) :
    E.toAtlasHomeomorph.symm p =
      ⟨p.proj, (E.fiberContinuousLinearEquiv p.proj).symm p.snd⟩ := by
  rw [Homeomorph.symm_apply_eq, toAtlasHomeomorph_apply]
  exact (congrArg (TotalSpace.mk p.proj)
    ((E.fiberContinuousLinearEquiv p.proj).apply_symm_apply p.snd)).symm

/-! ### The comparison functor -/

/-- A bundle map, read in the preferred charts of its source and target, as a map of atlases. -/
noncomputable def toAtlasMap (f : E ⟶ F) : E.toAtlas ⟶ F.toAtlas where
  fiberMap x := (F.fiberContinuousLinearEquiv x).toLinearMap ∘ₗ f.fiberMap x ∘ₗ
    (E.fiberContinuousLinearEquiv x).symm.toLinearMap
  continuous_totalSpaceMap :=
    -- `rfl` unfolds `LinearMap.comp`; `LinearMap.comp_apply` does not fire syntactically because
    -- `E.toAtlas.Fiber x` is `Fin (E.rank x) → 𝕜` only up to the `rfl` lemma `rank_ofBundles`.
    continuous_totalSpace_conj E.toAtlasHomeomorph.symm.continuous
      F.toAtlasHomeomorph.continuous E.toAtlasHomeomorph_symm_apply F.toAtlasHomeomorph_apply
      (fun _ ↦ rfl) f.continuous_totalSpaceMap

@[simp] theorem fiberMap_toAtlasMap (f : E ⟶ F) (x : X) :
    (toAtlasMap E f).fiberMap x = (F.fiberContinuousLinearEquiv x).toLinearMap ∘ₗ f.fiberMap x ∘ₗ
      (E.fiberContinuousLinearEquiv x).symm.toLinearMap := (rfl)

theorem fiberMap_toAtlasMap_apply (f : E ⟶ F) (x : X) (v : E.toAtlas.Fiber x) :
    (toAtlasMap E f).fiberMap x v =
      F.fiberContinuousLinearEquiv x (f.fiberMap x ((E.fiberContinuousLinearEquiv x).symm v)) :=
  (rfl)

/-- A map of atlases of genuine bundles, read back through the preferred charts, as a bundle
map. This inverts `toAtlasMap`. -/
noncomputable def ofAtlasMap (g : E.toAtlas ⟶ F.toAtlas) : E ⟶ F where
  fiberMap x := (F.fiberContinuousLinearEquiv x).symm.toLinearMap ∘ₗ g.fiberMap x ∘ₗ
    (E.fiberContinuousLinearEquiv x).toLinearMap
  continuous_totalSpaceMap :=
    -- `rfl` unfolds `LinearMap.comp`, as in `toAtlasMap`.
    continuous_totalSpace_conj E.toAtlasHomeomorph.continuous
      F.toAtlasHomeomorph.symm.continuous E.toAtlasHomeomorph_apply F.toAtlasHomeomorph_symm_apply
      (fun _ ↦ rfl) g.continuous_totalSpaceMap

@[simp] theorem fiberMap_ofAtlasMap (g : E.toAtlas ⟶ F.toAtlas) (x : X) :
    (ofAtlasMap E g).fiberMap x = (F.fiberContinuousLinearEquiv x).symm.toLinearMap ∘ₗ
      g.fiberMap x ∘ₗ (E.fiberContinuousLinearEquiv x).toLinearMap := (rfl)

@[simp] theorem toAtlasMap_id : toAtlasMap E (𝟙 E) = 𝟙 E.toAtlas :=
  FiniteRankAtlas.hom_ext fun x ↦ by
    simp
    -- The identities of `E.toAtlas.Fiber x` and `Fin (E.rank x) → 𝕜` agree by the `rfl` lemma
    -- `FiniteRankAtlas.rank_ofBundles`, which `simp` does not see through.
    rfl

@[simp] theorem toAtlasMap_comp (f : E ⟶ F) (g : F ⟶ G) :
    toAtlasMap E (f ≫ g) = toAtlasMap E f ≫ toAtlasMap F g :=
  FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun _ ↦ by
    simp only [fiberMap_toAtlasMap, fiberMap_comp, ContinuousLinearEquiv.toLinearEquiv_symm,
      FiniteRankAtlas.fiberMap_comp]
    -- `simp` cannot evaluate the compositions at a point of `E.toAtlas.Fiber x`, which is
    -- `Fin (E.rank x) → 𝕜` only up to the `rfl` lemma `FiniteRankAtlas.rank_ofBundles`.
    exact congrArg (fun u ↦ G.fiberContinuousLinearEquiv x (g.fiberMap x u))
      ((F.fiberContinuousLinearEquiv x).symm_apply_apply _).symm

@[simp] theorem toAtlasMap_add (f g : E ⟶ F) :
    toAtlasMap E (f + g) = toAtlasMap E f + toAtlasMap E g :=
  FiniteRankAtlas.hom_ext fun x ↦ by
    rw [FiniteRankAtlas.fiberMap_add, fiberMap_toAtlasMap, fiberMap_toAtlasMap,
      fiberMap_toAtlasMap, fiberMap_add, LinearMap.add_comp, LinearMap.comp_add]
    -- The two sides differ only in the additive structures of `F.toAtlas.Fiber x` and
    -- `Fin (F.rank x) → 𝕜`, which agree by the `rfl` lemma `FiniteRankAtlas.rank_ofBundles`.
    rfl

@[simp] theorem toAtlasMap_ofAtlasMap (g : E.toAtlas ⟶ F.toAtlas) :
    toAtlasMap E (ofAtlasMap E g) = g :=
  FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun v ↦ by
    rw [fiberMap_toAtlasMap, fiberMap_ofAtlasMap]
    exact ((F.fiberContinuousLinearEquiv x).apply_symm_apply _).trans
      (congrArg (g.fiberMap x) ((E.fiberContinuousLinearEquiv x).apply_symm_apply v))

@[simp] theorem ofAtlasMap_toAtlasMap (f : E ⟶ F) : ofAtlasMap E (toAtlasMap E f) = f :=
  hom_ext fun x ↦ LinearMap.ext fun v ↦ by
    rw [fiberMap_ofAtlasMap, fiberMap_toAtlasMap]
    exact ((F.fiberContinuousLinearEquiv x).symm_apply_apply _).trans
      (congrArg (f.fiberMap x) ((E.fiberContinuousLinearEquiv x).symm_apply_apply v))

variable (𝕜 X) in
/-- The comparison functor from genuine variable-rank bundles, with fibres in any universe, to
their small coordinate atlases. -/
-- Expose the object assignment so mapped morphisms are maps between the atlases `E.toAtlas`.
@[expose] noncomputable def toAtlasFunctor : FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X where
  obj E := E.toAtlas
  map f := toAtlasMap _ f
  map_id E := toAtlasMap_id E
  map_comp f g := toAtlasMap_comp _ f g

@[simp] theorem toAtlasFunctor_obj : (toAtlasFunctor 𝕜 X).obj E = E.toAtlas := (rfl)

@[simp] theorem toAtlasFunctor_map (f : E ⟶ F) :
    (toAtlasFunctor 𝕜 X).map f = toAtlasMap E f := (rfl)

/-- Every map between the atlases of two genuine bundles comes from a unique bundle map: the
comparison functor is fully faithful. -/
noncomputable def fullyFaithfulToAtlasFunctor : (toAtlasFunctor.{w} 𝕜 X).FullyFaithful where
  preimage {E _} g := ofAtlasMap E g
  map_preimage {E _} g := toAtlasMap_ofAtlasMap E g
  preimage_map {E _} f := ofAtlasMap_toAtlasMap E f

@[simp] theorem fullyFaithfulToAtlasFunctor_preimage (g : E.toAtlas ⟶ F.toAtlas) :
    fullyFaithfulToAtlasFunctor.preimage g = ofAtlasMap E g := (rfl)

instance : (toAtlasFunctor.{w} 𝕜 X).Full := fullyFaithfulToAtlasFunctor.full

instance : (toAtlasFunctor.{w} 𝕜 X).Faithful := fullyFaithfulToAtlasFunctor.faithful

instance : (toAtlasFunctor.{w} 𝕜 X).Additive where
  map_add := toAtlasMap_add _ _ _

/-- Genuine finite-rank bundles over `X`, with fibres in any universe, form an essentially small
category in the universe of `X` and `𝕜`. -/
instance instEssentiallySmall : EssentiallySmall.{max u v} (FiniteRankBundle.{w} 𝕜 X) :=
  essentiallySmall_of_fully_faithful (toAtlasFunctor 𝕜 X)

end FiniteRankBundle

end TauCeti
