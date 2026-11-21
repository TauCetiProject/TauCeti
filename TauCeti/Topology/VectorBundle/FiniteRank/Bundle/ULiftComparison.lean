/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Equivalence
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.ULift

/-!
# Comparison of universe lifting with the atlas equivalence

`FiniteRankVectorBundle.uliftFunctor 𝕜 X` commutes with `FiniteRankVectorBundle.toAtlasFunctor 𝕜 X`
up to the canonical natural isomorphism `FiniteRankVectorBundle.uliftToAtlasNatIso`, which is the
identity on every coordinate fibre. Consequently, `uliftFunctor 𝕜 X` is an equivalence of categories
whenever `[UnivLE.{v, w}]` holds.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory

namespace TauCeti.FiniteRankVectorBundle

open VariableRankBundle

universe u v w w'

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜] (X : Type u) [TopologicalSpace X]

/-- `uliftFunctor` commutes with `toAtlasFunctor` up to canonical natural isomorphism,
given by the identity on every coordinate fibre. -/
noncomputable def uliftToAtlasNatIso :
    uliftFunctor.{u, v, w, w'} 𝕜 X ⋙ toAtlasFunctor.{u, v, max w w'} 𝕜 X ≅
      toAtlasFunctor.{u, v, w} 𝕜 X :=
  NatIso.ofComponents (fun V ↦
    let V' : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X := V.ulift
    isoOfTotalSpaceHomeomorph (fun x ↦ LinearEquiv.refl 𝕜 (V.toAtlas.Fiber x))
      (V'.toAtlasTotalSpaceHomeomorph.symm.trans
        (V.uliftTotalSpaceHomeomorph.trans V.toAtlasTotalSpaceHomeomorph)) fun x v ↦ by
          simp only [V', Homeomorph.trans_apply, toAtlasTotalSpaceHomeomorph_symm_apply,
            uliftTotalSpaceHomeomorph_apply, toAtlasTotalSpaceHomeomorph_apply,
            preferredChartEquiv_ulift, ContinuousLinearEquiv.symm_trans_apply,
            uliftFiberEquiv_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
          exact congrArg (TotalSpace.mk x) (LinearEquiv.refl_apply (R := 𝕜) (v : _)).symm)
    fun {_ _} _ ↦ hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
      dsimp only [Functor.comp_obj, uliftFunctor]
      simp [-preferredChartEquiv_apply, -preferredChartEquiv_symm_apply]

variable {𝕜 X}

/-- On every coordinate fibre, the forward component of `uliftToAtlasNatIso` is the identity. -/
@[simp] theorem fiberMap_uliftToAtlasNatIso_hom_app (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (x : X) : ((uliftToAtlasNatIso.{u, v, w, w'} 𝕜 X).hom.app V).fiberMap x = LinearMap.id := by
  rw [uliftToAtlasNatIso, NatIso.ofComponents_hom_app (naturality := _),
    fiberMap_isoOfTotalSpaceHomeomorph_hom, LinearEquiv.refl_toLinearMap]

/-- On every coordinate fibre, the inverse component of `uliftToAtlasNatIso` is the identity. -/
@[simp] theorem fiberMap_uliftToAtlasNatIso_inv_app (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (x : X) : ((uliftToAtlasNatIso.{u, v, w, w'} 𝕜 X).inv.app V).fiberMap x = LinearMap.id := by
  simpa only [fiberMap_comp, fiberMap_uliftToAtlasNatIso_hom_app, LinearMap.id_comp, fiberMap_id]
    using congrArg (fun k : (toAtlasFunctor.{u, v, w} 𝕜 X).obj V ⟶ _ ↦ k.fiberMap x)
      ((uliftToAtlasNatIso.{u, v, w, w'} 𝕜 X).inv_hom_id_app V)

instance [UnivLE.{v, w}] : (uliftFunctor.{u, v, w, w'} 𝕜 X).IsEquivalence := by
  have : UnivLE.{v, max w w'} := @UnivLE.trans.{v, w, max w w'} ‹_› inferInstance
  have := Functor.isEquivalence_of_iso (uliftToAtlasNatIso.{u, v, w, w'} 𝕜 X).symm
  exact Functor.isEquivalence_of_comp_right (uliftFunctor 𝕜 X) (toAtlasFunctor 𝕜 X)

end TauCeti.FiniteRankVectorBundle
