/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.ToAtlas
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.ULift.Basic

/-!
# Comparison of universe lifting with the forward atlas functor

`FiniteRankVectorBundle.uliftFunctor 𝕜 X` commutes unconditionally with
`FiniteRankVectorBundle.toAtlasFunctor 𝕜 X` up to the canonical natural isomorphism
`FiniteRankVectorBundle.uliftToAtlasNatIso`, which is the identity on every coordinate fibre.
For the conditional equivalence instance when `[UnivLE.{v, w}]` holds, see
`TauCeti.Topology.VectorBundle.FiniteRank.Bundle.ULift.Equivalence`.

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
      simp

variable {𝕜 X}

/-- On every coordinate fibre, the forward component of `uliftToAtlasNatIso` is the identity. -/
@[simp] theorem fiberMap_uliftToAtlasNatIso_hom_app (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (x : X) : ((uliftToAtlasNatIso.{u, v, w, w'} 𝕜 X).hom.app V).fiberMap x = LinearMap.id := by
  rw [uliftToAtlasNatIso, NatIso.ofComponents_hom_app (naturality := _),
    fiberMap_isoOfTotalSpaceHomeomorph_hom, LinearEquiv.refl_toLinearMap]

/-- On every coordinate fibre, the inverse component of `uliftToAtlasNatIso` is the identity. -/
@[simp] theorem fiberMap_uliftToAtlasNatIso_inv_app (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (x : X) : ((uliftToAtlasNatIso.{u, v, w, w'} 𝕜 X).inv.app V).fiberMap x = LinearMap.id := by
  rw [uliftToAtlasNatIso, NatIso.ofComponents_inv_app (naturality := _),
    fiberMap_isoOfTotalSpaceHomeomorph_inv]
  rfl

end TauCeti.FiniteRankVectorBundle
