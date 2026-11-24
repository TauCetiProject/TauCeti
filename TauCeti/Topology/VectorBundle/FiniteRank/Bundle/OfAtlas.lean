/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Category
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic
public import TauCeti.Topology.VectorBundle.Transport

/-!
# Reconstructing variable-rank vector bundles from small coordinate atlases

Under `[UnivLE.{v, w}]`, `FiniteRankAtlas.toBundle` reconstructs a `Type w`-fibred variable-rank
vector bundle `FiniteRankVectorBundle.{u, v, w} 𝕜 X` from a small coordinate atlas
`A : FiniteRankAtlas 𝕜 X`, together with its stratum fibre equivalences
`FiniteRankAtlas.toBundleStratumEquiv`, total-space homeomorphism
`FiniteRankAtlas.toBundleTotalSpaceHomeomorph`, functorial action
`FiniteRankAtlas.toBundleFunctor`, and preferred-chart identification
`FiniteRankVectorBundle.continuousLinearEquivAt_toBundle`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section
open Bundle CategoryTheory Topology
namespace TauCeti
open VariableRankBundle
universe u v w
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankAtlas
section ToBundle
variable (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}]
/-- Continuous linear equivalence between the shrunk coordinate fibre over `y.val` and the native
`n`-stratum coordinate fibre over `y`. -/
noncomputable def toBundleStratumEquiv (n : ℕ) (y : {x : X // A.rank x = n}) :
    Shrink.{w} (A.Fiber y.val) ≃L[𝕜] (A.charts n).Fiber y :=
  (Shrink.continuousLinearEquiv 𝕜 (A.Fiber y.val)).trans
    { (stratumFiberEquiv A y).symm with
      continuous_toFun := continuous_pi fun i ↦ continuous_apply (Fin.cast y.property.symm i)
      continuous_invFun := continuous_pi fun i ↦ continuous_apply (Fin.cast y.property i) }
@[simp] theorem toBundleStratumEquiv_rfl_apply (x : X) (u : Shrink.{w} (A.Fiber x)) :
    A.toBundleStratumEquiv (A.rank x) ⟨x, rfl⟩ u =
      Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) u := by rfl
@[simp] theorem toBundleStratumEquiv_rfl_symm_apply (x : X)
    (v : (A.charts (A.rank x)).Fiber ⟨x, rfl⟩) :
    (A.toBundleStratumEquiv (A.rank x) ⟨x, rfl⟩).symm v =
      (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).symm v := by rfl

/-- Realize a small coordinate atlas `A : FiniteRankAtlas 𝕜 X` as a variable-rank vector bundle
with fibres in `Type w` whenever `UnivLE.{v, w}` holds. -/
-- Expose the rank and fibre projections so `(A.toBundle).Fiber` reduces to `Shrink (A.Fiber ·)`.
@[expose, implicit_reducible] noncomputable def toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X :=
  let φ := toBundleStratumEquiv.{u, v, w} A
  let ts (n : ℕ) : TopologicalSpace
      (TotalSpace (Fin n → 𝕜) (fun y : {x : X // A.rank x = n} ↦ Shrink.{w} (A.Fiber y.val))) :=
    TopologicalSpace.induced
      (fun p ↦ (⟨p.proj, φ n p.proj p.snd⟩ : TotalSpace (Fin n → 𝕜) (A.charts n).Fiber))
      inferInstance
  { rank := A.rank, Fiber x := Shrink.{w} (A.Fiber x), topologicalSpaceStratumTotalSpace := ts
    fiberBundleStratum n := @fiberBundleOfHomeomorph _ (Fin n → 𝕜) (A.charts n).Fiber
      (fun y ↦ Shrink.{w} (A.Fiber y.val)) _ (ts n) _ _ _ _ _ (fun y ↦ (φ n y).toHomeomorph) ⟨rfl⟩
    vectorBundleStratum n := by
      let _ := ts n; exact vectorBundleOfContinuousLinearEquiv 𝕜 (φ n) ⟨rfl⟩ }
@[simp] theorem rank_toBundle :
    (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).rank = A.rank := by rfl
@[simp] theorem fiber_toBundle (x : X) :
    (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber x = Shrink.{w} (A.Fiber x) := by rfl

/-- The glued total space of `A.toBundle` is homeomorphic over `X` to `TotalSpace Unit A.Fiber` via
`Shrink.continuousLinearEquiv` on each fibre. -/
noncomputable def toBundleTotalSpaceHomeomorph :
    TotalSpace Unit (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber ≃ₜ
      TotalSpace Unit A.Fiber :=
  let V : FiniteRankVectorBundle.{u, v, w} 𝕜 X := A.toBundle
  (VariableRankBundle.totalSpaceHomeomorph V).symm.trans ((Homeomorph.sigmaCongrRight fun n ↦
    totalSpaceHomeomorphOfIsInducing (Fin n → 𝕜) (E' := V.StratumFiber n)
      (fun y ↦ (toBundleStratumEquiv.{u, v, w} A n y).toEquiv) ⟨rfl⟩).trans
    (VariableRankBundle.totalSpaceHomeomorph A))
@[simp] theorem toBundleTotalSpaceHomeomorph_apply
    (p : TotalSpace Unit (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber) :
    A.toBundleTotalSpaceHomeomorph p =
      ⟨p.proj, Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj) p.snd⟩ := by
  simp only [toBundleTotalSpaceHomeomorph, Homeomorph.trans_apply, Homeomorph.sigmaCongrRight_apply,
    FiniteRankVectorBundle.totalSpaceHomeomorph_symm_apply, totalSpaceHomeomorphOfIsInducing_apply]
  exact (totalSpaceHomeomorph_rfl_apply A p.proj _).trans
    (congrArg (TotalSpace.mk p.proj) (toBundleStratumEquiv_rfl_apply A p.proj p.snd))
@[simp] theorem toBundleTotalSpaceHomeomorph_symm_apply (q : TotalSpace Unit A.Fiber) :
    (A.toBundleTotalSpaceHomeomorph :
      TotalSpace Unit (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber ≃ₜ _).symm q =
      ⟨q.proj, (Shrink.continuousLinearEquiv 𝕜 (A.Fiber q.proj)).symm q.snd⟩ := by
  simp only [toBundleTotalSpaceHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
    Homeomorph.sigmaCongrRight_symm_apply, totalSpaceHomeomorph_symm_apply,
    totalSpaceHomeomorphOfIsInducing_symm_apply, FiniteRankVectorBundle.totalSpaceHomeomorph_apply]
  exact congrArg (TotalSpace.mk q.proj) (toBundleStratumEquiv_rfl_symm_apply A q.proj q.snd)
end ToBundle

section ToBundleFunctor
variable [UnivLE.{v, w}]
variable (𝕜 X) in
/-- Reconstruct variable-rank vector bundles in fibre universe `w` from small coordinate atlases
whenever `UnivLE.{v, w}` holds. -/
-- Expose the object assignment so evaluated morphisms act on `Shrink (A.Fiber ·)`.
@[expose, implicit_reducible] noncomputable def toBundleFunctor :
    FiniteRankAtlas 𝕜 X ⥤ FiniteRankVectorBundle.{u, v, w} 𝕜 X where
  obj A := A.toBundle
  map {A D} f :=
    { fiberMap x := (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm.toLinearMap.comp
        ((f.fiberMap x).comp (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).toLinearMap)
      continuous_totalSpaceMap := (D.toBundleTotalSpaceHomeomorph.symm.continuous.comp
        (f.totalSpaceMap.continuous.comp A.toBundleTotalSpaceHomeomorph.continuous)).congr
        fun _ ↦ by
          simp only [Function.comp_apply, toBundleTotalSpaceHomeomorph_apply,
            VariableRankBundle.Hom.totalSpaceMap_mk, toBundleTotalSpaceHomeomorph_symm_apply,
            LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] }
  map_id _ := VariableRankBundle.hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    simp only [VariableRankBundle.fiberMap_id, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv, LinearMap.id_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  map_comp _ _ := VariableRankBundle.hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    simp only [VariableRankBundle.fiberMap_comp, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply]
@[simp] theorem toBundleFunctor_obj (A : FiniteRankAtlas 𝕜 X) :
    (toBundleFunctor.{u, v, w} 𝕜 X).obj A = A.toBundle := by rfl
@[simp] theorem fiberMap_toBundleFunctor_map_apply {A D : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ D) (x : X) (u : (A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).Fiber x) :
    ((toBundleFunctor.{u, v, w} 𝕜 X).map f).fiberMap x u =
      (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm
        (f.fiberMap x (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) u)) := by rfl
instance : (toBundleFunctor.{u, v, w} 𝕜 X).Additive where
  map_add {_ _ _ _} := VariableRankBundle.hom_ext fun _ ↦ LinearMap.ext fun _ ↦ by
    simp only [VariableRankBundle.fiberMap_add, LinearMap.add_apply,
      fiberMap_toBundleFunctor_map_apply, map_add]
end ToBundleFunctor
end FiniteRankAtlas

namespace FiniteRankVectorBundle
/-- On `A.toBundle`, the preferred stratum chart equivalence at `x` is
`Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)`. -/
@[simp] theorem continuousLinearEquivAt_toBundle (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}]
    (x : X) :
    VectorBundle.continuousLinearEquivAt 𝕜 (Fin (A.rank x) → 𝕜)
      ((A.toBundle : FiniteRankVectorBundle.{u, v, w} 𝕜 X).StratumFiber (A.rank x)) ⟨x, rfl⟩ =
      Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) := by
  let C := A.charts (A.rank x); let V : FiniteRankVectorBundle.{u, v, w} 𝕜 X := A.toBundle
  refine DFunLike.ext _ _ fun v ↦ ?_; rw [VectorBundle.continuousLinearEquivAt_apply]
  have htriv := congrArg (fun (e : Trivialization (Fin (A.rank x) → 𝕜)
      (π (Fin (A.rank x) → 𝕜) (V.StratumFiber (A.rank x)))) ↦ (e ⟨⟨x, rfl⟩, v⟩).2)
    (trivializationAt_fiberBundleOfHomeomorph (F := Fin (A.rank x) → 𝕜) (E := C.Fiber)
      (E' := V.StratumFiber (A.rank x))
      (fun y ↦ (A.toBundleStratumEquiv (A.rank x) y).toHomeomorph) ⟨rfl⟩ ⟨x, rfl⟩)
  -- Evaluating `compHomeomorph` applies `localTriv (indexAt _)` to `A.toBundleStratumEquiv _ _ v`.
  have hcore := congrArg Prod.snd (C.toFiberBundleCore.localTriv_apply (C.indexAt ⟨x, rfl⟩)
    ⟨⟨x, rfl⟩, A.toBundleStratumEquiv (A.rank x) ⟨x, rfl⟩ v⟩)
  exact htriv.trans (hcore.trans ((C.toFiberBundleCore.coordChange_self _ _
    (C.mem_baseSet_at ⟨x, rfl⟩) _).trans (A.toBundleStratumEquiv_rfl_apply x v)))
end FiniteRankVectorBundle
end TauCeti
