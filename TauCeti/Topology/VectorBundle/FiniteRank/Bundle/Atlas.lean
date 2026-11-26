/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

import TauCeti.Topology.Algebra.Module.Equiv.Basic
import TauCeti.Topology.Algebra.Module.Equiv.Pi
import TauCeti.Topology.FiberBundle.TotalSpace

/-!
# Genuine variable-rank bundles are equivalent to their small atlases

A genuine finite-rank bundle `E : TauCeti.FiniteRankBundle.{w} 𝕜 X` has fibres in an arbitrary
universe `w`, while a variable-rank atlas `TauCeti.FiniteRankAtlas 𝕜 X` stores only the rank and
point-indexed coordinate cores on the clopen rank strata, all in the universes of `X` and `𝕜`.
This file compares the two categories.

`FiniteRankBundle.toAtlas E` is the atlas of the preferred stratum trivializations of `E`, and
`FiniteRankBundle.toAtlasHomeomorph E` identifies the total space of `E` with the reconstructed
total space of that atlas, over the identity of `X` and by the preferred chart
`FiniteRankBundle.fiberContinuousLinearEquiv` on each fibre. Conjugating bundle maps by these
identifications gives the additive functor `FiniteRankBundle.toAtlasFunctor`, which is fully
faithful (`FiniteRankBundle.fullyFaithfulToAtlasFunctor`).

Conversely `FiniteRankAtlas.toBundle.{w} A` reconstructs from an atlas `A` a genuine bundle with
fibres `ULift.{w} (A.Fiber x)`; this is the functor `FiniteRankAtlas.toBundleFunctor`, and
`FiniteRankAtlas.toAtlasToBundleIso` shows, naturally in `A`, that `A` is recovered. Read back
through the fully faithful comparison functor, these isomorphisms also recover every genuine bundle
from its atlas (`FiniteRankBundle.toAtlasFunctorCompToBundleFunctorIso`). Hence
`toAtlasFunctor` is an equivalence `FiniteRankBundle.atlasEquivalence`, with inverse
`toBundleFunctor`, whenever the fibre universe can hold the scalars, that is for
`FiniteRankBundle.{max v w} 𝕜 X` with `𝕜 : Type v`. In every fibre universe the category of
genuine bundles is essentially small, in the universe of `X` and `𝕜`. No compactness, separation,
finite-cover or bounded-rank hypothesis is needed.

## Main definitions

* `TauCeti.FiniteRankBundle.toAtlas`: the coordinate atlas of a genuine bundle.
* `TauCeti.FiniteRankBundle.toAtlasFunctor`: the comparison functor
  `FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankAtlas 𝕜 X`.
* `TauCeti.FiniteRankAtlas.toBundle`: the genuine bundle reconstructed from an atlas.
* `TauCeti.FiniteRankAtlas.toBundleFunctor`: the reconstruction functor
  `FiniteRankAtlas 𝕜 X ⥤ FiniteRankBundle.{max v w} 𝕜 X`.
* `TauCeti.FiniteRankBundle.atlasEquivalence`: the equivalence
  `FiniteRankBundle.{max v w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X`.

## Main results

* `TauCeti.FiniteRankBundle.fullyFaithfulToAtlasFunctor`: the comparison functor is fully
  faithful in every fibre universe.
* `TauCeti.FiniteRankAtlas.toAtlasToBundleIso`: every atlas is isomorphic to the atlas of its
  reconstruction, so the comparison functor is essentially surjective from fibre universe
  `max v w`. These isomorphisms form the natural isomorphism
  `TauCeti.FiniteRankAtlas.toBundleFunctorCompToAtlasFunctorIso`.
* `TauCeti.FiniteRankBundle.toAtlasFunctorCompToBundleFunctorIso`: every genuine bundle with
  fibre universe `max v w` is naturally isomorphic to the reconstruction of its atlas.
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

/-! ### Reconstruction of a genuine bundle from an atlas -/

namespace FiniteRankAtlas

variable (A : FiniteRankAtlas 𝕜 X)

/-- The genuine bundle reconstructed from an atlas, with fibres `ULift.{w} (A.Fiber x)` and the
bundle structure of the core of `A` on each rank stratum. -/
-- Reducible, so that the fibres are `ULift.{w} (A.Fiber x)` and the API of
-- `FiniteRankBundle.ofBundles` applies to it.
noncomputable abbrev toBundle : FiniteRankBundle.{max v w} 𝕜 X :=
  FiniteRankBundle.ofBundles 𝕜 A.rank (fun x ↦ ULift.{w} (A.Fiber x)) (fun n ↦ (A.charts n).Fiber)
    fun _ x ↦ ContinuousLinearEquiv.ulift.trans
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ ↦ 𝕜) (finCongr x.property))

/-- The total space of the reconstructed bundle is homeomorphic, over `X`, to the reconstructed
total space of the atlas, by `ULift.down` on each fibre. -/
noncomputable def toBundleHomeomorph :
    TotalSpace Unit (toBundle.{w} A).Fiber ≃ₜ TotalSpace Unit A.Fiber :=
  (FiniteRankBundle.ofBundlesHomeomorph 𝕜 A.rank _ _ _).trans A.totalSpaceHomeomorph

@[simp] theorem toBundleHomeomorph_apply (p : TotalSpace Unit (toBundle.{w} A).Fiber) :
    toBundleHomeomorph.{w} A p = ⟨p.proj, ULift.down p.snd⟩ := by
  rw [toBundleHomeomorph, Homeomorph.trans_apply, FiniteRankBundle.ofBundlesHomeomorph_apply,
    totalSpaceHomeomorph_apply]
  simp only [finCongr_refl, Fin.cast_eq_self, ContinuousLinearEquiv.piCongrLeft_refl,
    TotalSpace.mk_inj]
  -- `A.toBundle.Fiber x` is `ULift (A.Fiber x)` only up to the `rfl` lemma
  -- `FiniteRankBundle.fiber_ofBundles`, so the lemmas are applied by unification, not `rw`.
  exact (ContinuousLinearEquiv.trans_apply ContinuousLinearEquiv.ulift (.refl 𝕜 _) _).trans <|
    (ContinuousLinearEquiv.refl_apply _ _ _).trans (ContinuousLinearEquiv.ulift_apply _)

@[simp] theorem toBundleHomeomorph_symm_apply (p : TotalSpace Unit A.Fiber) :
    (toBundleHomeomorph.{w} A).symm p = ⟨p.proj, ULift.up p.snd⟩ :=
  (toBundleHomeomorph.{w} A).injective <| by
    rw [Homeomorph.apply_symm_apply, toBundleHomeomorph_apply]

/-- Every atlas is isomorphic to the atlas of the genuine bundle reconstructed from it. On each
fibre the isomorphism is the inverse preferred chart of the reconstruction, followed by
`ULift.down`. -/
noncomputable def toAtlasToBundleIso : (toBundle.{w} A).toAtlas ≅ A :=
  isoMk (fun x ↦ (((toBundle.{w} A).fiberContinuousLinearEquiv x).symm.trans
      ContinuousLinearEquiv.ulift).toLinearEquiv)
    (continuous_totalSpace_conj (toBundle.{w} A).toAtlasHomeomorph.symm.continuous
      (toBundleHomeomorph A).continuous
      (f := fun q ↦ q.snd) (FiniteRankBundle.toAtlasHomeomorph_symm_apply _)
      (toBundleHomeomorph_apply A)
      (fun _ ↦ (ContinuousLinearEquiv.trans_apply _ _ _).trans
        (ContinuousLinearEquiv.ulift_apply _))
      continuous_id)
    (continuous_totalSpace_conj (toBundleHomeomorph A).symm.continuous
      (toBundle.{w} A).toAtlasHomeomorph.continuous
      (f := fun q ↦ q.snd) (toBundleHomeomorph_symm_apply A)
      (FiniteRankBundle.toAtlasHomeomorph_apply _)
      (fun _ ↦ (ContinuousLinearEquiv.symm_trans_apply _ _ _).trans <|
        congrArg _ (ContinuousLinearEquiv.ulift_symm_apply _))
      continuous_id)

@[simp] theorem fiberMap_toAtlasToBundleIso_hom_apply (x : X)
    (v : (toBundle.{w} A).toAtlas.Fiber x) :
    (toAtlasToBundleIso.{w} A).hom.fiberMap x v =
      (((toBundle.{w} A).fiberContinuousLinearEquiv x).symm v).down :=
  LinearMap.congr_fun (fiberMap_isoMk_hom _ _ _ x) v

@[simp] theorem fiberMap_toAtlasToBundleIso_inv_apply (x : X) (v : A.Fiber x) :
    (toAtlasToBundleIso.{w} A).inv.fiberMap x v =
      (toBundle.{w} A).fiberContinuousLinearEquiv x (ULift.up v) :=
  LinearMap.congr_fun (fiberMap_isoMk_inv _ _ _ x) v

/-- A linear map conjugated by `ContinuousLinearEquiv.ulift` acts on `ULift` by `ULift.down`,
the map and `ULift.up`. This evaluates the fibre maps of `toBundleMap`. -/
private theorem ulift_conj_apply {M N : Type*} [AddCommMonoid M] [Module 𝕜 M]
    [TopologicalSpace M] [AddCommMonoid N] [Module 𝕜 N] [TopologicalSpace N] (φ : M →ₗ[𝕜] N)
    (u : ULift.{w} M) :
    ((ContinuousLinearEquiv.ulift : ULift.{w} N ≃L[𝕜] N).symm.toLinearMap ∘ₗ φ ∘ₗ
      (ContinuousLinearEquiv.ulift : ULift.{w} M ≃L[𝕜] M).toLinearMap) u = ULift.up (φ u.down) := by
  simp

/-- An atlas map as a map of the reconstructed genuine bundles, acting on the fibres
`ULift.{w} (A.Fiber x)` through `ULift.down` and `ULift.up`. -/
noncomputable def toBundleMap {B : FiniteRankAtlas 𝕜 X} (g : A ⟶ B) :
    toBundle.{w} A ⟶ toBundle.{w} B where
  fiberMap x := ContinuousLinearEquiv.ulift.symm.toLinearMap ∘ₗ g.fiberMap x ∘ₗ
    ContinuousLinearEquiv.ulift.toLinearMap
  continuous_totalSpaceMap :=
    continuous_totalSpace_conj (toBundleHomeomorph A).continuous
      (toBundleHomeomorph B).symm.continuous
      (toBundleHomeomorph_apply A) (toBundleHomeomorph_symm_apply B)
      (fun _ ↦ ulift_conj_apply _ _) g.continuous_totalSpaceMap

@[simp] theorem fiberMap_toBundleMap_apply {B : FiniteRankAtlas 𝕜 X} (g : A ⟶ B) (x : X)
    (u : (toBundle.{w} A).Fiber x) :
    (toBundleMap.{w} A g).fiberMap x u = ULift.up (g.fiberMap x (ULift.down u)) :=
  ulift_conj_apply _ _

@[simp] theorem toBundleMap_id : toBundleMap.{w} A (𝟙 A) = 𝟙 (toBundle.{w} A) :=
  FiniteRankBundle.hom_ext fun x ↦ LinearMap.ext fun u ↦ by
    simp only [fiberMap_toBundleMap_apply, fiberMap_id, LinearMap.id_coe, id_eq,
      FiniteRankBundle.fiberMap_id]
    -- `A.toBundle.Fiber x` is `ULift (A.Fiber x)` only up to the `rfl` lemma
    -- `FiniteRankBundle.fiber_ofBundles`, so `ULift.up_down` is applied by unification.
    exact ULift.up_down u

@[simp] theorem toBundleMap_comp {B C : FiniteRankAtlas 𝕜 X} (f : A ⟶ B) (g : B ⟶ C) :
    toBundleMap.{w} A (f ≫ g) = toBundleMap.{w} A f ≫ toBundleMap.{w} B g :=
  FiniteRankBundle.hom_ext fun x ↦ LinearMap.ext fun u ↦ by
    simp only [fiberMap_toBundleMap_apply, fiberMap_comp, LinearMap.coe_comp, Function.comp_apply,
      FiniteRankBundle.fiberMap_comp]
    -- As in `toBundleMap_id`, the last evaluation is applied by unification.
    exact (fiberMap_toBundleMap_apply B g x _).symm

variable (𝕜 X) in
/-- The reconstruction of genuine bundles from atlases, as a functor. -/
-- Expose the object assignment so mapped morphisms are maps between the bundles `A.toBundle`.
@[expose] noncomputable def toBundleFunctor :
    FiniteRankAtlas 𝕜 X ⥤ FiniteRankBundle.{max v w} 𝕜 X where
  obj A := toBundle.{w} A
  map g := toBundleMap _ g
  map_id A := toBundleMap_id A
  map_comp f g := toBundleMap_comp _ f g

@[simp] theorem toBundleFunctor_obj : (toBundleFunctor.{w} 𝕜 X).obj A = toBundle.{w} A := (rfl)

@[simp] theorem toBundleFunctor_map {B : FiniteRankAtlas 𝕜 X} (g : A ⟶ B) :
    (toBundleFunctor.{w} 𝕜 X).map g = toBundleMap.{w} A g := (rfl)

/-- `toAtlasToBundleIso` is natural in the atlas. -/
theorem toAtlasToBundleIso_hom_naturality {B : FiniteRankAtlas 𝕜 X} (g : A ⟶ B) :
    FiniteRankBundle.toAtlasMap _ (toBundleMap.{w} A g) ≫ (toAtlasToBundleIso.{w} B).hom =
      (toAtlasToBundleIso.{w} A).hom ≫ g :=
  hom_ext fun x ↦ LinearMap.ext fun v ↦ by
    rw [fiberMap_comp, fiberMap_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      FiniteRankBundle.fiberMap_toAtlasMap_apply]
    -- `rw` cannot use the remaining lemmas, because `B.toBundle.toAtlas.Fiber x` is
    -- `Fin (B.rank x) → 𝕜` only up to the `rfl` lemma `FiniteRankAtlas.rank_ofBundles`.
    exact (fiberMap_toAtlasToBundleIso_hom_apply B x _).trans <|
      (congrArg ULift.down ((B.toBundle.fiberContinuousLinearEquiv x).symm_apply_apply _)).trans <|
      (congrArg ULift.down (fiberMap_toBundleMap_apply A g x _)).trans <|
      (congrArg (g.fiberMap x) (fiberMap_toAtlasToBundleIso_hom_apply A x v)).symm

variable (𝕜 X) in
/-- Reconstructing a genuine bundle from an atlas and taking its atlas is naturally isomorphic to
the identity, by `toAtlasToBundleIso`. -/
noncomputable def toBundleFunctorCompToAtlasFunctorIso :
    toBundleFunctor.{w} 𝕜 X ⋙ FiniteRankBundle.toAtlasFunctor 𝕜 X ≅ 𝟭 (FiniteRankAtlas 𝕜 X) :=
  NatIso.ofComponents (fun A ↦ toAtlasToBundleIso.{w} A) fun g ↦
    toAtlasToBundleIso_hom_naturality _ g

@[simp] theorem toBundleFunctorCompToAtlasFunctorIso_hom_app :
    (toBundleFunctorCompToAtlasFunctorIso.{w} 𝕜 X).hom.app A = (toAtlasToBundleIso.{w} A).hom :=
  (rfl)

@[simp] theorem toBundleFunctorCompToAtlasFunctorIso_inv_app :
    (toBundleFunctorCompToAtlasFunctorIso.{w} 𝕜 X).inv.app A = (toAtlasToBundleIso.{w} A).inv :=
  (rfl)

end FiniteRankAtlas

namespace FiniteRankBundle

instance : (toAtlasFunctor.{max v w} 𝕜 X).EssSurj where
  mem_essImage A := ⟨FiniteRankAtlas.toBundle.{w} A, ⟨FiniteRankAtlas.toAtlasToBundleIso A⟩⟩

instance : (toAtlasFunctor.{max v w} 𝕜 X).IsEquivalence where

variable (𝕜 X) in
/-- Taking the atlas of a genuine bundle and reconstructing a bundle from it is naturally
isomorphic to the identity: at `E` the isomorphism is `FiniteRankAtlas.toAtlasToBundleIso`
for `E.toAtlas`, read back as a bundle isomorphism through `ofAtlasMap`. -/
noncomputable def toAtlasFunctorCompToBundleFunctorIso :
    toAtlasFunctor 𝕜 X ⋙ FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X ≅
      𝟭 (FiniteRankBundle.{max v w} 𝕜 X) :=
  NatIso.ofComponents
    (fun E ↦ fullyFaithfulToAtlasFunctor.preimageIso
      (FiniteRankAtlas.toAtlasToBundleIso.{w} E.toAtlas))
    fun f ↦ fullyFaithfulToAtlasFunctor.map_injective <| by
      rw [Functor.map_comp, Functor.map_comp]
      -- The objects match only up to unfolding `toAtlasFunctor` and `toBundleFunctor`, so the
      -- `map_preimage` steps are applied by unification rather than by `rw`.
      exact (congrArg (_ ≫ ·) (fullyFaithfulToAtlasFunctor.map_preimage _)).trans <|
        (FiniteRankAtlas.toAtlasToBundleIso_hom_naturality _ (toAtlasMap _ f)).trans
          (congrArg (· ≫ _) (fullyFaithfulToAtlasFunctor.map_preimage _).symm)

@[simp] theorem toAtlasFunctorCompToBundleFunctorIso_hom_app
    (E : FiniteRankBundle.{max v w} 𝕜 X) :
    (toAtlasFunctorCompToBundleFunctorIso.{w} 𝕜 X).hom.app E =
      ofAtlasMap _ (FiniteRankAtlas.toAtlasToBundleIso.{w} E.toAtlas).hom :=
  (rfl)

@[simp] theorem toAtlasFunctorCompToBundleFunctorIso_inv_app
    (E : FiniteRankBundle.{max v w} 𝕜 X) :
    (toAtlasFunctorCompToBundleFunctorIso.{w} 𝕜 X).inv.app E =
      ofAtlasMap E (FiniteRankAtlas.toAtlasToBundleIso.{w} E.toAtlas).inv :=
  (rfl)

/-- The triangle identity of `atlasEquivalence`: the atlas of the unit at `E` is inverse to the
counit at the atlas of `E`. -/
theorem toAtlasFunctor_map_toAtlasFunctorCompToBundleFunctorIso_inv_app_comp
    (E : FiniteRankBundle.{max v w} 𝕜 X) :
    (toAtlasFunctor 𝕜 X).map ((toAtlasFunctorCompToBundleFunctorIso.{w} 𝕜 X).inv.app E) ≫
        (FiniteRankAtlas.toBundleFunctorCompToAtlasFunctorIso.{w} 𝕜 X).hom.app
          ((toAtlasFunctor 𝕜 X).obj E) =
      𝟙 ((toAtlasFunctor 𝕜 X).obj E) :=
  (congrArg (· ≫ _) (toAtlasMap_ofAtlasMap E _)).trans (Iso.inv_hom_id _)

variable (𝕜 X) in
/-- Genuine variable-rank bundles whose fibre universe can hold the scalars are equivalent to the
small variable-rank atlases, by `toAtlasFunctor` with inverse `FiniteRankAtlas.toBundleFunctor`,
unit the inverse of `toAtlasFunctorCompToBundleFunctorIso` and counit
`FiniteRankAtlas.toBundleFunctorCompToAtlasFunctorIso`. -/
-- Exposed because the statements of `atlasEquivalence_unitIso` and `atlasEquivalence_counitIso`
-- only typecheck when the functor and inverse unfold.
@[expose] noncomputable def atlasEquivalence :
    FiniteRankBundle.{max v w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X where
  functor := toAtlasFunctor 𝕜 X
  inverse := FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X
  unitIso := (toAtlasFunctorCompToBundleFunctorIso.{w} 𝕜 X).symm
  counitIso := FiniteRankAtlas.toBundleFunctorCompToAtlasFunctorIso.{w} 𝕜 X
  functor_unitIso_comp := toAtlasFunctor_map_toAtlasFunctorCompToBundleFunctorIso_inv_app_comp.{w}

@[simp] theorem atlasEquivalence_functor :
    (atlasEquivalence.{w} 𝕜 X).functor = toAtlasFunctor 𝕜 X := (rfl)

@[simp] theorem atlasEquivalence_inverse :
    (atlasEquivalence.{w} 𝕜 X).inverse = FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X := (rfl)

@[simp] theorem atlasEquivalence_counitIso :
    (atlasEquivalence.{w} 𝕜 X).counitIso =
      FiniteRankAtlas.toBundleFunctorCompToAtlasFunctorIso.{w} 𝕜 X := (rfl)

@[simp] theorem atlasEquivalence_unitIso :
    (atlasEquivalence.{w} 𝕜 X).unitIso = (toAtlasFunctorCompToBundleFunctorIso.{w} 𝕜 X).symm :=
  (rfl)

end FiniteRankBundle

end TauCeti
