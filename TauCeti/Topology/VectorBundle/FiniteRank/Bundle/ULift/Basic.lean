/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Equiv.ULift
public import TauCeti.Topology.Homeomorph.Sigma
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic
public import TauCeti.Topology.VectorBundle.ULift

/-!
# Universe lifting for variable-rank vector bundles

For `V : FiniteRankVectorBundle.{u, v, w} 𝕜 X`, `V.ulift` lifts every fibre to
`ULift.{w'} (V.Fiber x)` in `Type (max w w')`, equipped with the fibrewise equivalence
`uliftFiberEquiv` and glued total-space comparison `uliftTotalSpaceHomeomorph`. This defines
`uliftFunctor 𝕜 X : FiniteRankVectorBundle.{u, v, w} 𝕜 X ⥤`
`FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X`, which is unconditionally additive and fully faithful
in all universes `u, v, w, w'`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti.FiniteRankVectorBundle

open VariableRankBundle

universe u v w w'

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

section ULift
variable (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X)
/-- Lift the fibres of a variable-rank vector bundle from `Type w` to `Type (max w w')`. -/
-- Expose the rank and fibre projections so `V.ulift.Fiber` reduces to `ULift (V.Fiber ·)`.
@[expose, implicit_reducible] noncomputable def ulift :
    FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X :=
  { rank := V.rank, Fiber x := ULift.{w'} (V.Fiber x) }
@[simp] theorem rank_ulift :
    (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).rank = V.rank := by rfl
@[simp] theorem fiber_ulift (x : X) :
    (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber x =
      ULift.{w'} (V.Fiber x) := by rfl

/-- Continuous linear equivalence between the lifted fibre `(V.ulift).Fiber x` and `V.Fiber x`. -/
noncomputable def uliftFiberEquiv (x : X) :
    (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber x ≃L[𝕜] V.Fiber x :=
  ContinuousLinearEquiv.ulift
@[simp] theorem uliftFiberEquiv_apply (x : X)
    (v : (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber x) :
    uliftFiberEquiv.{u, v, w, w'} V x v = v.down := ContinuousLinearEquiv.ulift_apply v
@[simp] theorem uliftFiberEquiv_symm_apply (x : X) (v : V.Fiber x) :
    (uliftFiberEquiv.{u, v, w, w'} V x).symm v = ULift.up.{w'} v :=
  ContinuousLinearEquiv.ulift_symm_apply v

/-- On `V.ulift`, the preferred stratum chart equivalence at `x` factors through
`uliftFiberEquiv`. -/
@[simp] theorem preferredChartEquiv_ulift (x : X) :
    (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).preferredChartEquiv x =
      (uliftFiberEquiv.{u, v, w, w'} V x).trans (V.preferredChartEquiv x) := by
  refine DFunLike.ext _ _ fun v ↦ ?_
  rw [preferredChartEquiv_apply, ContinuousLinearEquiv.trans_apply, uliftFiberEquiv_apply,
    preferredChartEquiv_apply]
  exact congrArg Prod.snd (trivializationAt_ulift_apply (Fin (V.rank x) → 𝕜)
    (V.StratumFiber (V.rank x)) ⟨x, rfl⟩ ⟨⟨x, rfl⟩, v⟩)

/-- The glued total space of `V.ulift` is homeomorphic over `X` to `TotalSpace Unit V.Fiber` via
`ULift.down` on fibres. -/
noncomputable def uliftTotalSpaceHomeomorph :
    TotalSpace Unit (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber ≃ₜ
      TotalSpace Unit V.Fiber :=
  (VariableRankBundle.totalSpaceHomeomorph
      (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X)).symm.trans
    ((Homeomorph.sigmaCongrRight fun n ↦
        TauCeti.uliftTotalSpaceHomeomorph (Fin n → 𝕜) (V.StratumFiber n)).trans
      (VariableRankBundle.totalSpaceHomeomorph V))
@[simp] theorem uliftTotalSpaceHomeomorph_apply
    (p : TotalSpace Unit (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber) :
    V.uliftTotalSpaceHomeomorph p = ⟨p.proj, p.snd.down⟩ := by
  simp only [uliftTotalSpaceHomeomorph, Homeomorph.trans_apply, Homeomorph.sigmaCongrRight_apply,
    FiniteRankVectorBundle.totalSpaceHomeomorph_symm_apply, TauCeti.uliftTotalSpaceHomeomorph_apply,
    FiniteRankVectorBundle.totalSpaceHomeomorph_apply]
@[simp] theorem uliftTotalSpaceHomeomorph_symm_apply (p : TotalSpace Unit V.Fiber) :
    (V.uliftTotalSpaceHomeomorph : TotalSpace Unit
      (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X).Fiber ≃ₜ _).symm p =
      ⟨p.proj, ULift.up p.snd⟩ := by
  simp only [uliftTotalSpaceHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
    Homeomorph.sigmaCongrRight_symm_apply, FiniteRankVectorBundle.totalSpaceHomeomorph_symm_apply,
    TauCeti.uliftTotalSpaceHomeomorph_symm_apply, FiniteRankVectorBundle.totalSpaceHomeomorph_apply]
end ULift

variable (𝕜 X) in
/-- Lift variable-rank vector bundles and their morphisms from fibre universe `w` to `max w w'`. -/
-- Expose the object assignment so evaluated morphisms act on `ULift (V.Fiber ·)`.
@[expose, implicit_reducible] noncomputable def uliftFunctor :
    FiniteRankVectorBundle.{u, v, w} 𝕜 X ⥤ FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X where
  obj V := V.ulift
  map {V W} f :=
    { fiberMap x := (uliftFiberEquiv.{u, v, w, w'} W x).symm.toLinearMap.comp
        ((f.fiberMap x).comp (uliftFiberEquiv.{u, v, w, w'} V x).toLinearMap)
      continuous_totalSpaceMap := (W.uliftTotalSpaceHomeomorph.symm.continuous.comp
        (f.totalSpaceMap.continuous.comp V.uliftTotalSpaceHomeomorph.continuous)).congr
        fun _ ↦ by simp }
  map_id _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ ULift.ext (by simp)
  map_comp _ _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ ULift.ext (by simp)
@[simp] theorem uliftFunctor_obj (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) :
    (uliftFunctor.{u, v, w, w'} 𝕜 X).obj V =
      (V.ulift : FiniteRankVectorBundle.{u, v, max w w'} 𝕜 X) := by rfl
variable {V W : FiniteRankVectorBundle.{u, v, w} 𝕜 X}
@[simp] theorem fiberMap_uliftFunctor_map (f : V ⟶ W) (x : X)
    (v : ((uliftFunctor.{u, v, w, w'} 𝕜 X).obj V).Fiber x) :
    ((uliftFunctor.{u, v, w, w'} 𝕜 X).map f).fiberMap x v = ULift.up (f.fiberMap x v.down) := by rfl
instance : (uliftFunctor.{u, v, w, w'} 𝕜 X).Additive where
  map_add {_ _ _ _} := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    simp only [fiberMap_add, LinearMap.add_apply, fiberMap_uliftFunctor_map]
    exact (ULift.ext ULift.add_down).symm

private noncomputable def uliftPreimage
    (g : (uliftFunctor.{u, v, w, w'} 𝕜 X).obj V ⟶ (uliftFunctor.{u, v, w, w'} 𝕜 X).obj W) :
    V ⟶ W where
  fiberMap x := (uliftFiberEquiv.{u, v, w, w'} W x).toLinearMap.comp
    ((g.fiberMap x).comp (uliftFiberEquiv.{u, v, w, w'} V x).symm.toLinearMap)
  continuous_totalSpaceMap := (W.uliftTotalSpaceHomeomorph.continuous.comp
    (g.totalSpaceMap.continuous.comp V.uliftTotalSpaceHomeomorph.symm.continuous)).congr
    fun _ ↦ by simp
@[simp] private theorem fiberMap_uliftPreimage_apply
    (g : (uliftFunctor.{u, v, w, w'} 𝕜 X).obj V ⟶ (uliftFunctor.{u, v, w, w'} 𝕜 X).obj W) (x : X)
    (v : V.Fiber x) : (uliftPreimage g).fiberMap x v = (g.fiberMap x (ULift.up v)).down := by rfl

variable (𝕜 X) in
/-- `uliftFunctor 𝕜 X` is unconditionally fully faithful in all universes `u, v, w, w'`. -/
noncomputable def fullyFaithfulUliftFunctor : (uliftFunctor.{u, v, w, w'} 𝕜 X).FullyFaithful where
  preimage := uliftPreimage
  map_preimage _ := hom_ext fun _ ↦ LinearMap.ext fun v ↦ ULift.ext (by simp [ULift.up_down v])
  preimage_map _ := hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by simp
instance : (uliftFunctor.{u, v, w, w'} 𝕜 X).Full := (fullyFaithfulUliftFunctor 𝕜 X).full
instance : (uliftFunctor.{u, v, w, w'} 𝕜 X).Faithful := (fullyFaithfulUliftFunctor 𝕜 X).faithful

end TauCeti.FiniteRankVectorBundle
