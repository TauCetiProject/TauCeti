/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Atlas
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.OfAtlas

import TauCeti.Topology.FiberBundle.TotalSpace

/-!
# Universe-indexed categorical equivalence and universe change for variable-rank vector bundles

Under `[UnivLE.{v, w}]`, `FiniteRankAtlas.toBundleFunctor 𝕜 X` (from `Bundle/OfAtlas.lean`)
provides the inverse to `FiniteRankBundle.toAtlasFunctor 𝕜 X` (from `Bundle/Atlas.lean`), yielding
the categorical equivalence `FiniteRankBundle.atlasEquivalence 𝕜 X : FiniteRankBundle.{w} 𝕜 X ≌
FiniteRankAtlas 𝕜 X` directly in fibre universe `w`. Composing this equivalence in two fibre
universes gives `FiniteRankBundle.changeUniverseEquivalence` whenever `[UnivLE.{v, w}]` and
`[UnivLE.{v, w'}]`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti

universe w w' u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankAtlas

section Equivalence

variable [UnivLE.{v, w}] (A : FiniteRankAtlas 𝕜 X)

/-- Canonical isomorphism `(toAtlasFunctor 𝕜 X).obj A.toBundle ≅ A` in `FiniteRankAtlas 𝕜 X`,
given by the identity on every coordinate fibre. -/
noncomputable def toAtlasToBundleIso :
    (FiniteRankBundle.toAtlasFunctor.{w} 𝕜 X).obj A.toBundle ≅ A :=
  isoMk (fun x ↦ LinearEquiv.refl 𝕜 (A.Fiber x))
    (continuous_totalSpace_conj A.toBundle.toAtlasHomeomorph.symm.continuous
      A.toBundleHomeomorph.continuous (f := fun q ↦ q.snd)
      (FiniteRankBundle.toAtlasHomeomorph_symm_apply _) A.toBundleHomeomorph_apply
      (fun p ↦ by
        -- `erw` unifies `A.toBundle.toAtlas.Fiber p.proj` with `A.Fiber p.proj` across
        -- `rank_toBundle` and `rank_ofBundles`, and `A.toBundle.Fiber p.proj` with
        -- `Shrink (A.Fiber p.proj)` across `fiber_toBundle`.
        erw [FiniteRankBundle.fiberContinuousLinearEquiv_toBundle A p.proj]
        exact ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj)).apply_symm_apply _).symm)
      continuous_id)
    (continuous_totalSpace_conj A.toBundleHomeomorph.symm.continuous
      A.toBundle.toAtlasHomeomorph.continuous (f := fun q ↦ q.snd)
      A.toBundleHomeomorph_symm_apply (FiniteRankBundle.toAtlasHomeomorph_apply _)
      (fun p ↦ by
        -- Same `rfl` wrapper alignment as in the forward continuity proof above.
        erw [FiniteRankBundle.fiberContinuousLinearEquiv_toBundle A p.proj]
        exact ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj)).apply_symm_apply _).symm)
      continuous_id)

/-- The forward morphism of `toAtlasToBundleIso A` is the identity on every coordinate fibre. -/
@[simp] theorem fiberMap_toAtlasToBundleIso_hom (x : X) :
    (toAtlasToBundleIso.{w} A).hom.fiberMap x = LinearMap.id :=
  LinearMap.ext fun _ ↦ by
    dsimp only [toAtlasToBundleIso]
    erw [fiberMap_isoMk_hom]
    rfl

/-- The inverse morphism of `toAtlasToBundleIso A` is the identity on every coordinate fibre. -/
@[simp] theorem fiberMap_toAtlasToBundleIso_inv (x : X) :
    (toAtlasToBundleIso.{w} A).inv.fiberMap x = LinearMap.id :=
  LinearMap.ext fun _ ↦ by
    dsimp only [toAtlasToBundleIso]
    erw [fiberMap_isoMk_inv]
    rfl

private theorem fiberMap_toAtlasMap_toBundle_apply {B : FiniteRankAtlas 𝕜 X} (g : A ⟶ B)
    (x : X) (v : A.Fiber x) :
    (FiniteRankBundle.toAtlasMap A.toBundle ((toBundleFunctor.{w} 𝕜 X).map g)).fiberMap x v =
      g.fiberMap x v := by
  -- `erw` bridges `A.toBundle.toAtlas.Fiber x = A.Fiber x` and
  -- `A.toBundle.Fiber x = Shrink (A.Fiber x)` across `rank_toBundle`, `rank_ofBundles`,
  -- and `fiber_toBundle`.
  erw [FiniteRankBundle.fiberMap_toAtlasMap_apply, fiberMap_toBundleFunctor_map_apply,
    FiniteRankBundle.fiberContinuousLinearEquiv_toBundle A x,
    FiniteRankBundle.fiberContinuousLinearEquiv_toBundle B x]
  exact ((Shrink.continuousLinearEquiv 𝕜 (B.Fiber x)).apply_symm_apply _).trans
    (congrArg (g.fiberMap x) ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).apply_symm_apply v))

/-- `toAtlasToBundleIso` is natural in the atlas. -/
theorem toAtlasToBundleIso_hom_naturality {B : FiniteRankAtlas 𝕜 X} (g : A ⟶ B) :
    (FiniteRankBundle.toAtlasFunctor.{w} 𝕜 X).map ((toBundleFunctor.{w} 𝕜 X).map g) ≫
        (toAtlasToBundleIso.{w} B).hom =
      (toAtlasToBundleIso.{w} A).hom ≫ g :=
  hom_ext fun x ↦ LinearMap.ext fun v ↦ by
    rw [fiberMap_comp, fiberMap_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      FiniteRankBundle.toAtlasFunctor_map]
    -- `erw` bridges `A.toBundle.toAtlas.Fiber x = A.Fiber x` across `rank_toBundle` and
    -- `rank_ofBundles`.
    erw [fiberMap_toAtlasToBundleIso_hom B x, fiberMap_toAtlasToBundleIso_hom A x,
      LinearMap.id_apply (R := 𝕜), LinearMap.id_apply (R := 𝕜)]
    exact fiberMap_toAtlasMap_toBundle_apply A g x v

variable (𝕜 X) in
/-- Reconstructing a genuine bundle from an atlas and taking its atlas is naturally isomorphic to
the identity, by `toAtlasToBundleIso`. -/
noncomputable def toBundleFunctorCompToAtlasFunctorIso :
    toBundleFunctor.{w} 𝕜 X ⋙ FiniteRankBundle.toAtlasFunctor.{w} 𝕜 X ≅ 𝟭 (FiniteRankAtlas 𝕜 X) :=
  NatIso.ofComponents (fun A ↦ toAtlasToBundleIso.{w} A) fun g ↦
    toAtlasToBundleIso_hom_naturality _ g

@[simp] theorem toBundleFunctorCompToAtlasFunctorIso_hom_app :
    (toBundleFunctorCompToAtlasFunctorIso.{w} 𝕜 X).hom.app A = (toAtlasToBundleIso.{w} A).hom :=
  (rfl)

@[simp] theorem toBundleFunctorCompToAtlasFunctorIso_inv_app :
    (toBundleFunctorCompToAtlasFunctorIso.{w} 𝕜 X).inv.app A = (toAtlasToBundleIso.{w} A).inv :=
  (rfl)

end Equivalence

end FiniteRankAtlas

namespace FiniteRankBundle

section Equivalence

variable [UnivLE.{v, w}]

instance : (toAtlasFunctor.{w} 𝕜 X).EssSurj where
  mem_essImage A := ⟨A.toBundle, ⟨FiniteRankAtlas.toAtlasToBundleIso A⟩⟩

variable (𝕜 X) in
/-- Taking the atlas of a genuine bundle and reconstructing a bundle from it is naturally
isomorphic to the identity: at `E` the isomorphism is `FiniteRankAtlas.toAtlasToBundleIso`
for `E.toAtlas`, read back as a bundle isomorphism through `ofAtlasMap`. -/
noncomputable def toAtlasFunctorCompToBundleFunctorIso :
    toAtlasFunctor.{w} 𝕜 X ⋙ FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X ≅
      𝟭 (FiniteRankBundle.{w} 𝕜 X) :=
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
    (E : FiniteRankBundle.{w} 𝕜 X) :
    (toAtlasFunctorCompToBundleFunctorIso.{w} 𝕜 X).hom.app E =
      ofAtlasMap _ (FiniteRankAtlas.toAtlasToBundleIso.{w} E.toAtlas).hom :=
  (fullyFaithfulToAtlasFunctor.preimageIso_hom _).trans (fullyFaithfulToAtlasFunctor_preimage _ _)

@[simp] theorem toAtlasFunctorCompToBundleFunctorIso_inv_app
    (E : FiniteRankBundle.{w} 𝕜 X) :
    (toAtlasFunctorCompToBundleFunctorIso.{w} 𝕜 X).inv.app E =
      ofAtlasMap E (FiniteRankAtlas.toAtlasToBundleIso.{w} E.toAtlas).inv :=
  (fullyFaithfulToAtlasFunctor.preimageIso_inv _).trans (fullyFaithfulToAtlasFunctor_preimage _ _)

/-- The triangle identity of `atlasEquivalence`: the atlas of the unit at `E` is inverse to the
counit at the atlas of `E`. -/
theorem toAtlasFunctor_map_toAtlasFunctorCompToBundleFunctorIso_inv_app_comp
    (E : FiniteRankBundle.{w} 𝕜 X) :
    (toAtlasFunctor.{w} 𝕜 X).map ((toAtlasFunctorCompToBundleFunctorIso.{w} 𝕜 X).inv.app E) ≫
        (FiniteRankAtlas.toBundleFunctorCompToAtlasFunctorIso.{w} 𝕜 X).hom.app
          ((toAtlasFunctor.{w} 𝕜 X).obj E) =
      𝟙 ((toAtlasFunctor.{w} 𝕜 X).obj E) := by
  rw [toAtlasFunctorCompToBundleFunctorIso_inv_app,
    FiniteRankAtlas.toBundleFunctorCompToAtlasFunctorIso_hom_app]
  exact (congrArg (· ≫ _) (toAtlasMap_ofAtlasMap E _)).trans (Iso.inv_hom_id _)

variable (𝕜 X) in
/-- When the fibre universe `w` satisfies `UnivLE.{v, w}`, variable-rank vector bundles with
fibres in `Type w` are categorically equivalent to small coordinate atlases, by `toAtlasFunctor`
with inverse `FiniteRankAtlas.toBundleFunctor`. -/
-- Exposed because the statements of the unit and counit fibre-map lemmas only typecheck when the
-- functor and inverse unfold.
@[expose] noncomputable def atlasEquivalence :
    FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X where
  functor := toAtlasFunctor.{w} 𝕜 X
  inverse := FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X
  unitIso := (toAtlasFunctorCompToBundleFunctorIso.{w} 𝕜 X).symm
  counitIso := FiniteRankAtlas.toBundleFunctorCompToAtlasFunctorIso.{w} 𝕜 X
  functor_unitIso_comp := toAtlasFunctor_map_toAtlasFunctorCompToBundleFunctorIso_inv_app_comp.{w}

instance : (toAtlasFunctor.{w} 𝕜 X).IsEquivalence :=
  (atlasEquivalence.{w} 𝕜 X).isEquivalence_functor

@[simp] theorem atlasEquivalence_functor :
    (atlasEquivalence.{w} 𝕜 X).functor = toAtlasFunctor.{w} 𝕜 X := (rfl)

@[simp] theorem atlasEquivalence_inverse :
    (atlasEquivalence.{w} 𝕜 X).inverse = FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X := (rfl)

theorem atlasEquivalence_counitIso :
    (atlasEquivalence.{w} 𝕜 X).counitIso =
      FiniteRankAtlas.toBundleFunctorCompToAtlasFunctorIso.{w} 𝕜 X := (rfl)

theorem atlasEquivalence_unitIso :
    (atlasEquivalence.{w} 𝕜 X).unitIso =
      (toAtlasFunctorCompToBundleFunctorIso.{w} 𝕜 X).symm := (rfl)

/-- On every fibre, the forward unit component of `atlasEquivalence` composes the preferred chart
of `E` with `(Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).symm`. -/
@[simp] theorem fiberMap_atlasEquivalence_unitIso_hom_app (E : FiniteRankBundle.{w} 𝕜 X)
    (x : X) :
    ((atlasEquivalence.{w} 𝕜 X).unitIso.hom.app E).fiberMap x =
      (Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).symm.toLinearMap ∘ₗ
        (E.fiberContinuousLinearEquiv x).toLinearMap :=
  LinearMap.ext fun _ ↦ by
    rw [atlasEquivalence_unitIso, Iso.symm_hom,
      toAtlasFunctorCompToBundleFunctorIso_inv_app]
    erw [fiberMap_ofAtlasMap, FiniteRankAtlas.fiberMap_toAtlasToBundleIso_inv]
    dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv]
    erw [LinearMap.id_apply (R := 𝕜), fiberContinuousLinearEquiv_toBundle]
    rfl

/-- On every fibre, the inverse unit component of `atlasEquivalence` composes
`Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)` with the inverse preferred chart of `E`. -/
@[simp] theorem fiberMap_atlasEquivalence_unitIso_inv_app (E : FiniteRankBundle.{w} 𝕜 X)
    (x : X) :
    ((atlasEquivalence.{w} 𝕜 X).unitIso.inv.app E).fiberMap x =
      (E.fiberContinuousLinearEquiv x).symm.toLinearMap ∘ₗ
        (Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).toLinearMap :=
  LinearMap.ext fun _ ↦ by
    rw [atlasEquivalence_unitIso, Iso.symm_inv,
      toAtlasFunctorCompToBundleFunctorIso_hom_app]
    erw [fiberMap_ofAtlasMap, FiniteRankAtlas.fiberMap_toAtlasToBundleIso_hom]
    dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv]
    erw [LinearMap.id_apply (R := 𝕜), fiberContinuousLinearEquiv_toBundle]
    rfl

/-- On every coordinate fibre, the forward counit component of `atlasEquivalence` is the
identity. -/
@[simp] theorem fiberMap_atlasEquivalence_counitIso_hom_app (A : FiniteRankAtlas 𝕜 X) (x : X) :
    ((atlasEquivalence.{w} 𝕜 X).counitIso.hom.app A).fiberMap x = LinearMap.id :=
  FiniteRankAtlas.fiberMap_toAtlasToBundleIso_hom A x

/-- On every coordinate fibre, the inverse counit component of `atlasEquivalence` is the
identity. -/
@[simp] theorem fiberMap_atlasEquivalence_counitIso_inv_app (A : FiniteRankAtlas 𝕜 X) (x : X) :
    ((atlasEquivalence.{w} 𝕜 X).counitIso.inv.app A).fiberMap x = LinearMap.id :=
  FiniteRankAtlas.fiberMap_toAtlasToBundleIso_inv A x

end Equivalence

variable (𝕜 X) in
/-- Equivalence between variable-rank vector bundle categories in any two fibre universes `w, w'`
satisfying `UnivLE.{v, w}` and `UnivLE.{v, w'}`. -/
noncomputable def changeUniverseEquivalence [UnivLE.{v, w}] [UnivLE.{v, w'}] :
    FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankBundle.{w'} 𝕜 X :=
  (atlasEquivalence.{w} 𝕜 X).trans (atlasEquivalence.{w'} 𝕜 X).symm

@[simp] theorem changeUniverseEquivalence_functor [UnivLE.{v, w}] [UnivLE.{v, w'}] :
    (changeUniverseEquivalence.{w, w'} 𝕜 X).functor =
      toAtlasFunctor.{w} 𝕜 X ⋙ FiniteRankAtlas.toBundleFunctor.{w'} 𝕜 X := (rfl)

@[simp] theorem changeUniverseEquivalence_inverse [UnivLE.{v, w}] [UnivLE.{v, w'}] :
    (changeUniverseEquivalence.{w, w'} 𝕜 X).inverse =
      toAtlasFunctor.{w'} 𝕜 X ⋙ FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X := (rfl)

end FiniteRankBundle

end TauCeti
