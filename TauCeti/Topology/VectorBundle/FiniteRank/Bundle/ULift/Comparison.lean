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
Combining this with full faithfulness of `toAtlasFunctor 𝕜 X` shows that `uliftFunctor 𝕜 X` is
unconditionally fully faithful (`FiniteRankVectorBundle.fullyFaithfulUliftFunctor`).
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
            uliftTotalSpaceHomeomorph_apply, toAtlasTotalSpaceHomeomorph_apply]
          rw [show VectorBundle.continuousLinearEquivAt 𝕜 (Fin (V'.rank x) → 𝕜)
              (V'.StratumFiber (V'.rank x)) ⟨x, rfl⟩ =
              (ContinuousLinearEquiv.ulift : ULift.{w'} (V.Fiber x) ≃L[𝕜] V.Fiber x).trans
                (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (V.rank x) → 𝕜)
                  (V.StratumFiber (V.rank x)) ⟨x, rfl⟩) from
                continuousLinearEquivAt_ulift.{u, v, w, w'} V x,
            ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.ulift_symm_apply,
            ContinuousLinearEquiv.apply_symm_apply]
          exact congrArg (TotalSpace.mk x) (LinearEquiv.refl_apply (R := 𝕜) (v : _)).symm)
    fun {V W} f ↦ hom_ext fun x ↦ LinearMap.ext fun u ↦ by
      let V' : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X := V.ulift
      let W' : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X := W.ulift
      dsimp only [Functor.comp_obj, Functor.comp_map, uliftFunctor]
      simp only [fiberMap_comp, LinearMap.comp_apply, fiberMap_isoOfTotalSpaceHomeomorph_hom,
        LinearEquiv.refl_toLinearMap, LinearMap.id_apply, fiberMap_toAtlasFunctor_map_apply,
        LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
      rw [show VectorBundle.continuousLinearEquivAt 𝕜 (Fin (V'.rank x) → 𝕜)
          (V'.StratumFiber (V'.rank x)) ⟨x, rfl⟩ =
          (ContinuousLinearEquiv.ulift : ULift.{w'} (V.Fiber x) ≃L[𝕜] V.Fiber x).trans
            (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (V.rank x) → 𝕜)
              (V.StratumFiber (V.rank x)) ⟨x, rfl⟩) from
            continuousLinearEquivAt_ulift.{u, v, w, w'} V x,
        show VectorBundle.continuousLinearEquivAt 𝕜 (Fin (W'.rank x) → 𝕜)
          (W'.StratumFiber (W'.rank x)) ⟨x, rfl⟩ =
          (ContinuousLinearEquiv.ulift : ULift.{w'} (W.Fiber x) ≃L[𝕜] W.Fiber x).trans
            (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (W.rank x) → 𝕜)
              (W.StratumFiber (W.rank x)) ⟨x, rfl⟩) from
            continuousLinearEquivAt_ulift.{u, v, w, w'} W x]
      simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_trans_apply,
        ContinuousLinearEquiv.apply_symm_apply]

variable {𝕜 X}

/-- On every coordinate fibre, the forward component of `uliftToAtlasNatIso` is the identity. -/
@[simp] theorem fiberMap_uliftToAtlasNatIso_hom_app (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (x : X) : ((uliftToAtlasNatIso.{u, v, w, w'} 𝕜 X).hom.app V).fiberMap x = LinearMap.id := by
  change (isoOfTotalSpaceHomeomorph _ _ _).hom.fiberMap x = _
  rw [fiberMap_isoOfTotalSpaceHomeomorph_hom, LinearEquiv.refl_toLinearMap]

/-- On every coordinate fibre, the inverse component of `uliftToAtlasNatIso` is the identity. -/
@[simp] theorem fiberMap_uliftToAtlasNatIso_inv_app (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
    (x : X) : ((uliftToAtlasNatIso.{u, v, w, w'} 𝕜 X).inv.app V).fiberMap x = LinearMap.id := by
  change (isoOfTotalSpaceHomeomorph _ _ _).inv.fiberMap x = _
  rw [fiberMap_isoOfTotalSpaceHomeomorph_inv]
  rfl

variable (𝕜 X) in
/-- `uliftFunctor 𝕜 X` is unconditionally fully faithful in all universes `u, v, w, w'`. -/
noncomputable def fullyFaithfulUliftFunctor : (uliftFunctor.{u, v, w, w'} 𝕜 X).FullyFaithful :=
  ((fullyFaithfulToAtlasFunctor.{u, v, w} 𝕜 X).ofIso
    (uliftToAtlasNatIso.{u, v, w, w'} 𝕜 X).symm).ofCompFaithful
instance : (uliftFunctor.{u, v, w, w'} 𝕜 X).Full := (fullyFaithfulUliftFunctor 𝕜 X).full
instance : (uliftFunctor.{u, v, w, w'} 𝕜 X).Faithful := (fullyFaithfulUliftFunctor 𝕜 X).faithful

end TauCeti.FiniteRankVectorBundle
