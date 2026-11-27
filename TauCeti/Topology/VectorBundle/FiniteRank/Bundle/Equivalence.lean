/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Atlas
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.OfAtlas

/-!
# Universe-indexed categorical equivalence and universe change for variable-rank vector bundles

While `TauCeti.FiniteRankBundle.atlasEquivalence` (in `Bundle/Atlas.lean`) establishes the
equivalence `FiniteRankBundle.{max v w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X` via `ULift`, under
`[UnivLE.{v, w}]` `FiniteRankAtlas.toBundleShrinkFunctor` (from `Bundle/OfAtlas.lean`) yields an
equivalence `FiniteRankBundle.atlasEquivalenceOfUnivLE 𝕜 X : FiniteRankBundle.{w} 𝕜 X ≌
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

namespace FiniteRankBundle

section Equivalence

variable [UnivLE.{v, w}]

section

variable (A : FiniteRankAtlas 𝕜 X)

/-- Canonical isomorphism `(toAtlasFunctor 𝕜 X).obj A.toBundleShrink ≅ A` in `FiniteRankAtlas 𝕜 X`,
given by the identity on every coordinate fibre. -/
noncomputable def toAtlasToBundleShrinkIso : (toAtlasFunctor.{w} 𝕜 X).obj A.toBundleShrink ≅ A :=
  FiniteRankAtlas.isoMk (fun x ↦ LinearEquiv.refl 𝕜 (A.Fiber x))
    ((A.toBundleShrinkHomeomorph.continuous.comp
      A.toBundleShrink.toAtlasHomeomorph.symm.continuous).congr fun p ↦ by
      simp only [Function.comp_apply, toAtlasHomeomorph_symm_apply,
        FiniteRankAtlas.toBundleShrinkHomeomorph_apply]
      -- `erw` unifies `A.toBundleShrink.toAtlas.Fiber p.proj` with `A.Fiber p.proj` via the `rfl`
      -- lemmas `rank_toBundleShrink` and `FiniteRankAtlas.rank_ofBundles`, and
      -- `A.toBundleShrink.Fiber p.proj` with `Shrink (A.Fiber p.proj)` via `fiber_toBundleShrink`.
      erw [fiberContinuousLinearEquiv_toBundleShrink A p.proj]
      exact congrArg (TotalSpace.mk p.proj)
        ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj)).apply_symm_apply _))
    ((A.toBundleShrink.toAtlasHomeomorph.continuous.comp
      A.toBundleShrinkHomeomorph.symm.continuous).congr fun p ↦ by
      simp only [Function.comp_apply, FiniteRankAtlas.toBundleShrinkHomeomorph_symm_apply,
        toAtlasHomeomorph_apply]
      -- Same `rfl` wrapper alignment as in the forward continuity proof above.
      erw [fiberContinuousLinearEquiv_toBundleShrink A p.proj]
      exact congrArg (TotalSpace.mk p.proj)
        ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj)).apply_symm_apply _))

/-- The forward morphism of `toAtlasToBundleShrinkIso A` is the identity on every coordinate fibre.
-/
@[simp] theorem fiberMap_toAtlasToBundleShrinkIso_hom (x : X) :
    (toAtlasToBundleShrinkIso.{w} A).hom.fiberMap x = LinearMap.id :=
  LinearMap.ext fun _ ↦ by
    dsimp only [toAtlasToBundleShrinkIso]
    erw [FiniteRankAtlas.fiberMap_isoMk_hom]
    rfl

/-- The inverse morphism of `toAtlasToBundleShrinkIso A` is the identity on every coordinate fibre.
-/
@[simp] theorem fiberMap_toAtlasToBundleShrinkIso_inv (x : X) :
    (toAtlasToBundleShrinkIso.{w} A).inv.fiberMap x = LinearMap.id :=
  LinearMap.ext fun _ ↦ by
    dsimp only [toAtlasToBundleShrinkIso]
    erw [FiniteRankAtlas.fiberMap_isoMk_inv]
    rfl

end

private noncomputable def toBundleShrinkToAtlasIso (E : FiniteRankBundle.{w} 𝕜 X) :
    E ≅ (FiniteRankAtlas.toBundleShrinkFunctor.{w} 𝕜 X).obj
      ((toAtlasFunctor.{w} 𝕜 X).obj E) :=
  isoMk
    (fun x ↦ (E.fiberContinuousLinearEquiv x).toLinearEquiv.trans
      (Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).symm.toLinearEquiv)
    ((E.toAtlas.toBundleShrinkHomeomorph.symm.continuous.comp
      E.toAtlasHomeomorph.continuous).congr fun p ↦ by
      simp only [Function.comp_apply, toAtlasHomeomorph_apply,
        FiniteRankAtlas.toBundleShrinkHomeomorph_symm_apply]
      rfl)
    ((E.toAtlasHomeomorph.symm.continuous.comp
      E.toAtlas.toBundleShrinkHomeomorph.continuous).congr fun p ↦ by
      simp only [Function.comp_apply, FiniteRankAtlas.toBundleShrinkHomeomorph_apply,
        toAtlasHomeomorph_symm_apply]
      rfl)

instance (priority := 1100) : (toAtlasFunctor.{w} 𝕜 X).EssSurj where
  mem_essImage A := ⟨A.toBundleShrink, ⟨toAtlasToBundleShrinkIso A⟩⟩

variable (𝕜 X) in
/-- When the fibre universe `w` satisfies `UnivLE.{v, w}`, variable-rank vector bundles with
fibres in `Type w` are categorically equivalent to small coordinate atlases, with explicit inverse
`FiniteRankAtlas.toBundleShrinkFunctor 𝕜 X`. -/
noncomputable def atlasEquivalenceOfUnivLE :
    FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X where
  functor := toAtlasFunctor.{w} 𝕜 X
  inverse := FiniteRankAtlas.toBundleShrinkFunctor.{w} 𝕜 X
  unitIso := NatIso.ofComponents toBundleShrinkToAtlasIso fun {E F} f ↦
    hom_ext fun x ↦ LinearMap.ext fun v ↦ by
      dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map]
      rw [fiberMap_comp, fiberMap_comp]
      dsimp only [LinearMap.comp_apply, toBundleShrinkToAtlasIso]
      erw [fiberMap_isoMk_hom, fiberMap_isoMk_hom]
      erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
      dsimp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
        ContinuousLinearEquiv.toLinearEquiv_symm]
      erw [FiniteRankAtlas.fiberMap_toBundleShrinkFunctor_map_apply, toAtlasFunctor_map,
        fiberMap_toAtlasMap_apply]
      erw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
      rfl
  counitIso := NatIso.ofComponents toAtlasToBundleShrinkIso fun {A D} f ↦
    FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun u ↦ by
      dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map]
      rw [FiniteRankAtlas.fiberMap_comp, FiniteRankAtlas.fiberMap_comp]
      dsimp only [LinearMap.comp_apply]
      erw [fiberMap_toAtlasToBundleShrinkIso_hom, fiberMap_toAtlasToBundleShrinkIso_hom]
      erw [toAtlasFunctor_map, fiberMap_toAtlasMap_apply,
        FiniteRankAtlas.fiberMap_toBundleShrinkFunctor_map_apply]
      erw [fiberContinuousLinearEquiv_toBundleShrink A x,
        fiberContinuousLinearEquiv_toBundleShrink D x]
      exact ((Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).apply_symm_apply _).trans
        (congrArg (f.fiberMap x) ((Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).apply_symm_apply _))
  functor_unitIso_comp E := FiniteRankAtlas.hom_ext fun x ↦ LinearMap.ext fun u ↦ by
    dsimp only [Functor.comp_obj, Functor.id_obj, NatIso.ofComponents_hom_app,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [FiniteRankAtlas.fiberMap_comp]
    dsimp only [LinearMap.comp_apply]
    erw [fiberMap_toAtlasToBundleShrinkIso_hom, LinearMap.id_apply,
      toAtlasFunctor_map, fiberMap_toAtlasMap_apply]
    dsimp only [toBundleShrinkToAtlasIso]
    erw [fiberMap_isoMk_hom, LinearEquiv.trans_apply]
    dsimp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.toLinearEquiv_symm]
    erw [fiberContinuousLinearEquiv_toBundleShrink E.toAtlas x]
    exact ((Shrink.continuousLinearEquiv 𝕜 (E.toAtlas.Fiber x)).apply_symm_apply _).trans
      ((E.fiberContinuousLinearEquiv x).apply_symm_apply _)

instance (priority := 1100) : (toAtlasFunctor.{w} 𝕜 X).IsEquivalence :=
  (atlasEquivalenceOfUnivLE.{w} 𝕜 X).isEquivalence_functor

@[simp] theorem atlasEquivalenceOfUnivLE_functor :
    (atlasEquivalenceOfUnivLE.{w} 𝕜 X).functor = toAtlasFunctor.{w} 𝕜 X := by rfl

@[simp] theorem atlasEquivalenceOfUnivLE_inverse :
    (atlasEquivalenceOfUnivLE.{w} 𝕜 X).inverse =
      FiniteRankAtlas.toBundleShrinkFunctor.{w} 𝕜 X := by rfl

end Equivalence

variable (𝕜 X) in
/-- Equivalence between variable-rank vector bundle categories in any two fibre universes `w, w'`
satisfying `UnivLE.{v, w}` and `UnivLE.{v, w'}`. -/
noncomputable def changeUniverseEquivalence [UnivLE.{v, w}] [UnivLE.{v, w'}] :
    FiniteRankBundle.{w} 𝕜 X ≌ FiniteRankBundle.{w'} 𝕜 X :=
  (atlasEquivalenceOfUnivLE.{w} 𝕜 X).trans (atlasEquivalenceOfUnivLE.{w'} 𝕜 X).symm

@[simp] theorem changeUniverseEquivalence_functor [UnivLE.{v, w}] [UnivLE.{v, w'}] :
    (changeUniverseEquivalence.{w, w'} 𝕜 X).functor =
      toAtlasFunctor.{w} 𝕜 X ⋙ FiniteRankAtlas.toBundleShrinkFunctor.{w'} 𝕜 X := by rfl

end FiniteRankBundle

end TauCeti
