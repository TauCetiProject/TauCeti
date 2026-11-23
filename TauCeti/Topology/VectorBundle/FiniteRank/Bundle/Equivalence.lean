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
`A : FiniteRankAtlas 𝕜 X`, and the forward functor `FiniteRankVectorBundle.toAtlasFunctor 𝕜 X`
from `Bundle/ToAtlas.lean` becomes an equivalence `FiniteRankVectorBundle.atlasEquivalence 𝕜 X`.
Composing `atlasEquivalence` in two fibre universes gives
`FiniteRankVectorBundle.changeUniverseEquivalence` whenever `[UnivLE.{v, w}]` and
`[UnivLE.{v, w'}]`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section
open Bundle CategoryTheory Topology
namespace TauCeti
open VariableRankBundle
universe u v w w'
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankVectorBundle
section Equivalence
variable [UnivLE.{v, w}]
section
variable (A : FiniteRankAtlas 𝕜 X)

/-- Canonical isomorphism `(toAtlasFunctor 𝕜 X).obj A.toBundle ≅ A` in `FiniteRankAtlas 𝕜 X`,
given by the identity on every coordinate fibre. -/
noncomputable def toAtlasToBundleIso : (toAtlasFunctor.{u, v, w} 𝕜 X).obj A.toBundle ≅ A :=
  let V : FiniteRankVectorBundle.{u, v, w} 𝕜 X := A.toBundle
  isoOfTotalSpaceHomeomorph (fun x ↦ LinearEquiv.refl 𝕜 (A.Fiber x))
    (V.toAtlasTotalSpaceHomeomorph.symm.trans A.toBundleTotalSpaceHomeomorph) fun x v ↦ by
      simp only [V, Homeomorph.trans_apply, toAtlasTotalSpaceHomeomorph_symm_apply,
        FiniteRankAtlas.toBundleTotalSpaceHomeomorph_apply, preferredChartEquiv_toBundle,
        ContinuousLinearEquiv.apply_symm_apply]
      exact congrArg (TotalSpace.mk x) (LinearEquiv.refl_apply (R := 𝕜) (v : A.Fiber x)).symm
/-- The forward morphism of `toAtlasToBundleIso A` is the identity on every coordinate fibre. -/
@[simp] theorem fiberMap_toAtlasToBundleIso_hom (x : X) :
    (toAtlasToBundleIso.{u, v, w} A).hom.fiberMap x = LinearMap.id := by
  rw [toAtlasToBundleIso, fiberMap_isoOfTotalSpaceHomeomorph_hom, LinearEquiv.refl_toLinearMap]
/-- The inverse morphism of `toAtlasToBundleIso A` is the identity on every coordinate fibre. -/
@[simp] theorem fiberMap_toAtlasToBundleIso_inv (x : X) :
    (toAtlasToBundleIso.{u, v, w} A).inv.fiberMap x = LinearMap.id := by
  rw [toAtlasToBundleIso, fiberMap_isoOfTotalSpaceHomeomorph_inv]
  rfl
end

private noncomputable def toBundleToAtlasIso (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    V ≅ (FiniteRankAtlas.toBundleFunctor.{u, v, w} 𝕜 X).obj
      ((toAtlasFunctor.{u, v, w} 𝕜 X).obj V) :=
  isoOfTotalSpaceHomeomorph
    (fun x ↦ (V.preferredChartEquiv x).toLinearEquiv.trans
      (Shrink.continuousLinearEquiv 𝕜 (V.toAtlas.Fiber x)).symm.toLinearEquiv)
    (V.toAtlasTotalSpaceHomeomorph.trans V.toAtlas.toBundleTotalSpaceHomeomorph.symm)
    fun x v ↦ by
      rw [Homeomorph.trans_apply, toAtlasTotalSpaceHomeomorph_apply,
        FiniteRankAtlas.toBundleTotalSpaceHomeomorph_symm_apply]
      exact congrArg (TotalSpace.mk x) (LinearEquiv.trans_apply _).symm

instance : (toAtlasFunctor.{u, v, w} 𝕜 X).EssSurj where
  mem_essImage A := ⟨A.toBundle, ⟨toAtlasToBundleIso A⟩⟩
variable (𝕜 X) in
/-- When the fibre universe `w` is at least the scalar field universe `v`, variable-rank vector
bundles with fibres in `Type w` are categorically equivalent to small coordinate atlases, with
explicit inverse `FiniteRankAtlas.toBundleFunctor 𝕜 X`. -/
noncomputable def atlasEquivalence :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X ≌ FiniteRankAtlas 𝕜 X where
  functor := toAtlasFunctor.{u, v, w} 𝕜 X
  inverse := FiniteRankAtlas.toBundleFunctor.{u, v, w} 𝕜 X
  unitIso := NatIso.ofComponents toBundleToAtlasIso fun {V W} f ↦
    hom_ext fun x ↦ LinearMap.ext fun v ↦ by
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
        fiberMap_comp, LinearMap.comp_apply, toBundleToAtlasIso,
        fiberMap_isoOfTotalSpaceHomeomorph_hom, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv, FiniteRankAtlas.fiberMap_toBundleFunctor_map_apply,
        fiberMap_toAtlasFunctor_map_apply]
      dsimp only [toAtlasFunctor]
      simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  counitIso := NatIso.ofComponents toAtlasToBundleIso fun {A D} f ↦
    hom_ext fun x ↦ LinearMap.ext fun u ↦ by
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
        fiberMap_comp, LinearMap.comp_apply, fiberMap_toAtlasToBundleIso_hom, LinearMap.id_apply,
        fiberMap_toAtlasFunctor_map_apply, FiniteRankAtlas.fiberMap_toBundleFunctor_map_apply]
      dsimp only [FiniteRankAtlas.toBundleFunctor]
      simp only [preferredChartEquiv_toBundle, ContinuousLinearEquiv.apply_symm_apply]
  functor_unitIso_comp V := hom_ext fun x ↦ LinearMap.ext fun u ↦ by
    simp only [Functor.comp_obj, Functor.id_obj, NatIso.ofComponents_hom_app,
      fiberMap_comp, LinearMap.comp_apply, fiberMap_toAtlasToBundleIso_hom, LinearMap.id_apply,
      fiberMap_toAtlasFunctor_map_apply, toBundleToAtlasIso,
      fiberMap_isoOfTotalSpaceHomeomorph_hom, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv, fiberMap_id]
    dsimp only [FiniteRankAtlas.toBundleFunctor, toAtlasFunctor]
    simp only [preferredChartEquiv_toBundle, ContinuousLinearEquiv.apply_symm_apply]
instance : (toAtlasFunctor.{u, v, w} 𝕜 X).IsEquivalence :=
  (atlasEquivalence.{u, v, w} 𝕜 X).isEquivalence_functor
@[simp] theorem atlasEquivalence_functor :
    (atlasEquivalence.{u, v, w} 𝕜 X).functor = toAtlasFunctor.{u, v, w} 𝕜 X := by rfl
@[simp] theorem atlasEquivalence_inverse :
    (atlasEquivalence.{u, v, w} 𝕜 X).inverse =
      FiniteRankAtlas.toBundleFunctor.{u, v, w} 𝕜 X := by rfl
end Equivalence

variable (𝕜 X) in
/-- Equivalence between variable-rank vector bundle categories in any two fibre universes `w, w'`
at least as large as the scalar field universe `v`. -/
noncomputable def changeUniverseEquivalence [UnivLE.{v, w}] [UnivLE.{v, w'}] :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X ≌ FiniteRankVectorBundle.{u, v, w'} 𝕜 X :=
  (atlasEquivalence.{u, v, w} 𝕜 X).trans (atlasEquivalence.{u, v, w'} 𝕜 X).symm
@[simp] theorem changeUniverseEquivalence_functor [UnivLE.{v, w}] [UnivLE.{v, w'}] :
    (changeUniverseEquivalence.{u, v, w, w'} 𝕜 X).functor =
      toAtlasFunctor.{u, v, w} 𝕜 X ⋙ FiniteRankAtlas.toBundleFunctor.{u, v, w'} 𝕜 X := by rfl
end FiniteRankVectorBundle
end TauCeti
