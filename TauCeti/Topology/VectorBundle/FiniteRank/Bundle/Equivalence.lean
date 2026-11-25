/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.OfAtlas
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.ToAtlas

/-!
# Categorical equivalence with small coordinate atlases and universe independence

Under `[UnivLE.{v, w}]`, `FiniteRankAtlas.toBundle` (from `Bundle/OfAtlas.lean`) reconstructs a
`Type w`-fibred variable-rank vector bundle from a small coordinate atlas
`A : FiniteRankAtlas 𝕜 X`, and the forward functor `FiniteRankBundle.toAtlasFunctor 𝕜 X` from
`Bundle/ToAtlas.lean` becomes an equivalence `FiniteRankBundle.atlasEquivalence 𝕜 X`. Composing
`atlasEquivalence` in two fibre universes gives `FiniteRankBundle.changeUniverseEquivalence`
whenever `[UnivLE.{v, w}]` and `[UnivLE.{v, w'}]`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti

universe w w' u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankBundle

section Equivalence

variable [UnivLE.{v, w}]

section

variable (A : FiniteRankAtlas 𝕜 X)

/-- Canonical isomorphism `(toAtlasFunctor 𝕜 X).obj A.toBundle ≅ A` in `FiniteRankAtlas 𝕜 X`,
given by the identity on every coordinate fibre. -/
noncomputable def toAtlasToBundleIso : (toAtlasFunctor.{w} 𝕜 X).obj A.toBundle ≅ A :=
  FiniteRankAtlas.isoMk (fun x ↦ LinearEquiv.refl 𝕜 (A.Fiber x))
    ((A.toBundleTotalSpaceHomeomorph.continuous.comp
      A.toBundle.toAtlasTotalSpaceHomeomorph.symm.continuous).congr fun p ↦ by
      simp only [Function.comp_apply, toAtlasTotalSpaceHomeomorph_symm_apply,
        FiniteRankAtlas.toBundleTotalSpaceHomeomorph_apply]
      rw [show VectorBundle.continuousLinearEquivAt 𝕜 (Fin (A.toBundle.rank p.proj) → 𝕜)
          (A.toBundle.StratumFiber (A.toBundle.rank p.proj)) ⟨p.proj, rfl⟩ =
          Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj) from
          continuousLinearEquivAt_toBundle A p.proj]
      exact congrArg (TotalSpace.mk p.proj)
        ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj)).apply_symm_apply _))
    ((A.toBundle.toAtlasTotalSpaceHomeomorph.continuous.comp
      A.toBundleTotalSpaceHomeomorph.symm.continuous).congr fun p ↦ by
      simp only [Function.comp_apply, FiniteRankAtlas.toBundleTotalSpaceHomeomorph_symm_apply,
        toAtlasTotalSpaceHomeomorph_apply]
      rw [show VectorBundle.continuousLinearEquivAt 𝕜 (Fin (A.toBundle.rank p.proj) → 𝕜)
          (A.toBundle.StratumFiber (A.toBundle.rank p.proj)) ⟨p.proj, rfl⟩ =
          Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj) from
          continuousLinearEquivAt_toBundle A p.proj]
      exact congrArg (TotalSpace.mk p.proj)
        ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj)).apply_symm_apply _))

/-- The forward morphism of `toAtlasToBundleIso A` is the identity on every coordinate fibre. -/
@[simp] theorem fiberMap_toAtlasToBundleIso_hom (x : X) :
    (toAtlasToBundleIso.{w} A).hom.fiberMap x = LinearMap.id :=
  LinearMap.ext fun _ ↦ by
    dsimp only [toAtlasToBundleIso]
    erw [FiniteRankAtlas.fiberMap_isoMk_hom]
    rfl

/-- The inverse morphism of `toAtlasToBundleIso A` is the identity on every coordinate fibre. -/
@[simp] theorem fiberMap_toAtlasToBundleIso_inv (x : X) :
    (toAtlasToBundleIso.{w} A).inv.fiberMap x = LinearMap.id :=
  LinearMap.ext fun _ ↦ by
    dsimp only [toAtlasToBundleIso]
    erw [FiniteRankAtlas.fiberMap_isoMk_inv]
    rfl

end

private noncomputable def toBundleToAtlasIso (E : FiniteRankBundle.{w} 𝕜 X) :
    E ≅ (FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X).obj
      ((toAtlasFunctor.{w} 𝕜 X).obj E) :=
  isoMk
    (fun x ↦ (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜)
      (E.StratumFiber (E.rank x)) ⟨x, rfl⟩).toLinearEquiv.trans
      (Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).symm.toLinearEquiv)
    ((E.toAtlas.toBundleTotalSpaceHomeomorph.symm.continuous.comp
      E.toAtlasTotalSpaceHomeomorph.continuous).congr fun p ↦ by
      simp only [Function.comp_apply, toAtlasTotalSpaceHomeomorph_apply,
        FiniteRankAtlas.toBundleTotalSpaceHomeomorph_symm_apply]
      rfl)
    ((E.toAtlasTotalSpaceHomeomorph.symm.continuous.comp
      E.toAtlas.toBundleTotalSpaceHomeomorph.continuous).congr fun p ↦ by
      simp only [Function.comp_apply, FiniteRankAtlas.toBundleTotalSpaceHomeomorph_apply,
        toAtlasTotalSpaceHomeomorph_symm_apply]
      rfl)

instance : (toAtlasFunctor.{w} 𝕜 X).EssSurj where
  mem_essImage A := ⟨A.toBundle, ⟨toAtlasToBundleIso A⟩⟩

variable (𝕜 X) in
/-- When the fibre universe `w` is at least the scalar field universe `v`, variable-rank vector
bundles with fibres in `Type w` are categorically equivalent to small coordinate atlases, with
explicit inverse `FiniteRankAtlas.toBundleFunctor 𝕜 X`. -/
noncomputable def atlasEquivalence :
    FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X where
  functor := toAtlasFunctor.{w} 𝕜 X
  inverse := FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X
  unitIso := NatIso.ofComponents toBundleToAtlasIso fun {E F} f ↦
    hom_ext fun x ↦ LinearMap.ext fun v ↦ by
      dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map]
      rw [fiberMap_comp, fiberMap_comp]
      dsimp only [LinearMap.comp_apply, toBundleToAtlasIso]
      erw [fiberMap_isoMk_hom, fiberMap_isoMk_hom]
      erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
      dsimp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
        ContinuousLinearEquiv.toLinearEquiv_symm]
      erw [FiniteRankAtlas.fiberMap_toBundleFunctor_map_apply, fiberMap_toAtlasFunctor_map_apply]
      dsimp only [toAtlasFunctor]
      erw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
      rfl
  counitIso := NatIso.ofComponents toAtlasToBundleIso fun {A D} f ↦
    FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun u ↦ by
      dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map]
      rw [FiniteRankAtlas.fiberMap_comp, FiniteRankAtlas.fiberMap_comp]
      dsimp only [LinearMap.comp_apply]
      erw [fiberMap_toAtlasToBundleIso_hom, fiberMap_toAtlasToBundleIso_hom]
      change VectorBundle.continuousLinearEquivAt 𝕜 (Fin (D.rank x) → 𝕜)
          (D.toBundle.StratumFiber (D.rank x)) ⟨x, rfl⟩
          ((Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm
            ((f.fiberMap x)
              ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber x))
                ((VectorBundle.continuousLinearEquivAt 𝕜 (Fin (A.rank x) → 𝕜)
                  (A.toBundle.StratumFiber (A.rank x)) ⟨x, rfl⟩).symm u)))) =
        (f.fiberMap x) u
      erw [continuousLinearEquivAt_toBundle A x]
      erw [continuousLinearEquivAt_toBundle D x]
      exact ((Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).apply_symm_apply _).trans
        (congrArg (f.fiberMap x) ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).apply_symm_apply _))
  functor_unitIso_comp E := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun u ↦ by
    dsimp only [Functor.comp_obj, Functor.id_obj, NatIso.ofComponents_hom_app,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [FiniteRankAtlas.fiberMap_comp]
    dsimp only [LinearMap.comp_apply]
    erw [fiberMap_toAtlasToBundleIso_hom]
    erw [LinearMap.id_apply]
    erw [fiberMap_toAtlasFunctor_map_apply]
    dsimp only [toBundleToAtlasIso]
    erw [fiberMap_isoMk_hom, LinearEquiv.trans_apply]
    dsimp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.toLinearEquiv_symm]
    change VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.toAtlas.rank x) → 𝕜)
        (E.toAtlas.toBundle.StratumFiber (E.toAtlas.rank x)) ⟨x, rfl⟩
        ((Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).symm
          ((VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜)
            (E.StratumFiber (E.rank x)) ⟨x, rfl⟩)
            ((VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜)
              (E.StratumFiber (E.rank x)) ⟨x, rfl⟩).symm u))) = u
    rw [continuousLinearEquivAt_toBundle E.toAtlas x]
    exact ((Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).apply_symm_apply _).trans
      ((VectorBundle.continuousLinearEquivAt 𝕜 (Fin (E.rank x) → 𝕜)
        (E.StratumFiber (E.rank x)) ⟨x, rfl⟩).apply_symm_apply _)

instance : (toAtlasFunctor.{w} 𝕜 X).IsEquivalence :=
  (atlasEquivalence.{w} 𝕜 X).isEquivalence_functor

@[simp] theorem atlasEquivalence_functor :
    (atlasEquivalence.{w} 𝕜 X).functor = toAtlasFunctor.{w} 𝕜 X := by rfl

@[simp] theorem atlasEquivalence_inverse :
    (atlasEquivalence.{w} 𝕜 X).inverse =
      FiniteRankAtlas.toBundleFunctor.{w} 𝕜 X := by rfl

end Equivalence

variable (𝕜 X) in
/-- Equivalence between variable-rank vector bundle categories in any two fibre universes `w, w'`
at least as large as the scalar field universe `v`. -/
noncomputable def changeUniverseEquivalence [UnivLE.{v, w}] [UnivLE.{v, w'}] :
    FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankBundle.{w'} 𝕜 X :=
  (atlasEquivalence.{w} 𝕜 X).trans (atlasEquivalence.{w'} 𝕜 X).symm

@[simp] theorem changeUniverseEquivalence_functor [UnivLE.{v, w}] [UnivLE.{v, w'}] :
    (changeUniverseEquivalence.{w, w'} 𝕜 X).functor =
      toAtlasFunctor.{w} 𝕜 X ⋙ FiniteRankAtlas.toBundleFunctor.{w'} 𝕜 X := by rfl

end FiniteRankBundle

end TauCeti
