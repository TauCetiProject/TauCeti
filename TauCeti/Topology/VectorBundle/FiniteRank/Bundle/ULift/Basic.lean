/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Topology.Homeomorph.Sigma
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic
public import TauCeti.Topology.VectorBundle.ULift

/-!
# Universe lifting for variable-rank vector bundles

For `V : FiniteRankBundle.{w} 𝕜 X`, `V.ulift` lifts every fibre to
`ULift.{w'} (V.Fiber x)` in `Type (max w w')`, equipped with the fibrewise equivalence
`ContinuousLinearEquiv.ulift` and glued total-space comparison `uliftTotalSpaceHomeomorph`. This
defines `uliftFunctor 𝕜 X : FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankBundle.{max w w'} 𝕜 X`,
which is unconditionally additive in all universes `w, w', u, v`. For its comparison with
`toAtlasFunctor` and full faithfulness, see
`TauCeti.Topology.VectorBundle.FiniteRank.Bundle.ULift.Comparison`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti.FiniteRankBundle

universe w w' u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

section ULift

variable (V : FiniteRankBundle.{w} 𝕜 X)

/-- Lift the fibres of a variable-rank vector bundle from `Type w` to `Type (max w w')`. -/
-- Expose the rank and fibre projections so `V.ulift.Fiber` reduces to `ULift (V.Fiber ·)`.
@[expose, implicit_reducible] noncomputable def ulift :
    FiniteRankBundle.{max w w'} 𝕜 X :=
  { rank := V.rank, Fiber x := ULift.{w'} (V.Fiber x) }

@[simp] theorem rank_ulift :
    (V.ulift : FiniteRankBundle.{max w w'} 𝕜 X).rank = V.rank := by rfl

@[simp] theorem fiber_ulift (x : X) :
    (V.ulift : FiniteRankBundle.{max w w'} 𝕜 X).Fiber x =
      ULift.{w'} (V.Fiber x) := by rfl

/-- On `V.ulift`, the preferred stratum chart equivalence at `x` factors through
`ContinuousLinearEquiv.ulift`. -/
@[simp] theorem continuousLinearEquivAt_ulift (x : X) :
    VectorBundle.continuousLinearEquivAt 𝕜 (Fin (V.rank x) → 𝕜)
      ((V.ulift : FiniteRankBundle.{max w w'} 𝕜 X).StratumFiber (V.rank x))
      ⟨x, rfl⟩ =
      (ContinuousLinearEquiv.ulift : ULift.{w'} (V.Fiber x) ≃L[𝕜] V.Fiber x).trans
        (VectorBundle.continuousLinearEquivAt 𝕜 (Fin (V.rank x) → 𝕜)
          (V.StratumFiber (V.rank x)) ⟨x, rfl⟩) := by
  refine DFunLike.ext _ _ fun v ↦ ?_
  rw [VectorBundle.continuousLinearEquivAt_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.ulift_apply, VectorBundle.continuousLinearEquivAt_apply]
  exact congrArg Prod.snd (trivializationAt_ulift_apply (Fin (V.rank x) → 𝕜)
    (V.StratumFiber (V.rank x)) ⟨x, rfl⟩ ⟨⟨x, rfl⟩, v⟩)

/-- On `V.ulift`, the preferred fibre equivalence at `x` factors through
`ContinuousLinearEquiv.ulift`. -/
@[simp] theorem fiberContinuousLinearEquiv_ulift (x : X) :
    (V.ulift : FiniteRankBundle.{max w w'} 𝕜 X).fiberContinuousLinearEquiv x =
      (ContinuousLinearEquiv.ulift : ULift.{w'} (V.Fiber x) ≃L[𝕜] V.Fiber x).trans
        (V.fiberContinuousLinearEquiv x) := by
  refine DFunLike.ext _ _ fun v ↦ ?_
  rw [fiberContinuousLinearEquiv_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.ulift_apply, fiberContinuousLinearEquiv_apply]
  exact congrArg Prod.snd (trivializationAt_ulift_apply (Fin (V.rank x) → 𝕜)
    (V.StratumFiber (V.rank x)) ⟨x, rfl⟩ ⟨⟨x, rfl⟩, v⟩)

/-- The glued total space of `V.ulift` is homeomorphic over `X` to `TotalSpace Unit V.Fiber` via
`ULift.down` on fibres. -/
noncomputable def uliftTotalSpaceHomeomorph :
    TotalSpace Unit (V.ulift : FiniteRankBundle.{max w w'} 𝕜 X).Fiber ≃ₜ
      TotalSpace Unit V.Fiber :=
  (FiniteRankBundle.totalSpaceHomeomorph
      (V.ulift : FiniteRankBundle.{max w w'} 𝕜 X)).symm.trans
    ((Homeomorph.sigmaCongrRight fun n ↦
        TauCeti.uliftTotalSpaceHomeomorph (Fin n → 𝕜) (V.StratumFiber n)).trans
      (FiniteRankBundle.totalSpaceHomeomorph V))

@[simp] theorem uliftTotalSpaceHomeomorph_apply
    (p : TotalSpace Unit (V.ulift : FiniteRankBundle.{max w w'} 𝕜 X).Fiber) :
    V.uliftTotalSpaceHomeomorph p = ⟨p.proj, p.snd.down⟩ := by
  simp only [uliftTotalSpaceHomeomorph, Homeomorph.trans_apply, Homeomorph.sigmaCongrRight_apply,
    FiniteRankBundle.totalSpaceHomeomorph_symm_apply, TauCeti.uliftTotalSpaceHomeomorph_apply,
    FiniteRankBundle.totalSpaceHomeomorph_apply]

@[simp] theorem uliftTotalSpaceHomeomorph_symm_apply (p : TotalSpace Unit V.Fiber) :
    (V.uliftTotalSpaceHomeomorph : TotalSpace Unit
      (V.ulift : FiniteRankBundle.{max w w'} 𝕜 X).Fiber ≃ₜ _).symm p =
      ⟨p.proj, ULift.up p.snd⟩ := by
  simp only [uliftTotalSpaceHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
    Homeomorph.sigmaCongrRight_symm_apply, FiniteRankBundle.totalSpaceHomeomorph_symm_apply,
    TauCeti.uliftTotalSpaceHomeomorph_symm_apply, FiniteRankBundle.totalSpaceHomeomorph_apply]

end ULift

variable (𝕜 X) in
/-- Lift variable-rank vector bundles and their morphisms from fibre universe `w` to `max w w'`. -/
-- Expose the object assignment so evaluated morphisms act on `ULift (V.Fiber ·)`.
@[expose, implicit_reducible] noncomputable def uliftFunctor :
    FiniteRankBundle.{w} 𝕜 X ⥤ FiniteRankBundle.{max w w'} 𝕜 X where
  obj V := V.ulift
  map {V W} f :=
    { fiberMap x := (ContinuousLinearEquiv.ulift :
          ULift.{w'} (W.Fiber x) ≃L[𝕜] W.Fiber x).symm.toLinearMap.comp
        ((f.fiberMap x).comp (ContinuousLinearEquiv.ulift :
          ULift.{w'} (V.Fiber x) ≃L[𝕜] V.Fiber x).toLinearMap)
      continuous_totalSpaceMap := (W.uliftTotalSpaceHomeomorph.symm.continuous.comp
        (f.totalSpaceMap.continuous.comp V.uliftTotalSpaceHomeomorph.continuous)).congr
        fun p ↦ by
          simp only [Function.comp_apply, uliftTotalSpaceHomeomorph_apply,
            FiniteRankBundle.Hom.totalSpaceMap_mk, uliftTotalSpaceHomeomorph_symm_apply,
            LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
            ContinuousLinearEquiv.ulift_symm_apply]
          rw [ContinuousLinearEquiv.ulift_apply] }
  map_id _ := hom_ext fun _ ↦ LinearMap.ext fun v ↦ ULift.ext (by
    simp only [fiberMap_id, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv, LinearMap.id_apply,
      ContinuousLinearEquiv.ulift_symm_apply]
    rw [ContinuousLinearEquiv.ulift_apply])
  map_comp _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ ULift.ext (by
    simp only [fiberMap_comp, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply])

@[simp] theorem uliftFunctor_obj (V : FiniteRankBundle.{w} 𝕜 X) :
    (uliftFunctor.{w, w'} 𝕜 X).obj V =
      (V.ulift : FiniteRankBundle.{max w w'} 𝕜 X) := by rfl

variable {V W : FiniteRankBundle.{w} 𝕜 X}

@[simp] theorem fiberMap_uliftFunctor_map_apply (f : V ⟶ W) (x : X)
    (v : ((uliftFunctor.{w, w'} 𝕜 X).obj V).Fiber x) :
    ((uliftFunctor.{w, w'} 𝕜 X).map f).fiberMap x v = ULift.up (f.fiberMap x v.down) := by rfl

instance : (uliftFunctor.{w, w'} 𝕜 X).Additive where
  map_add {_ _ _ _} := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    simp only [fiberMap_add, LinearMap.add_apply, fiberMap_uliftFunctor_map_apply]
    exact (ULift.ext ULift.add_down).symm

end TauCeti.FiniteRankBundle
