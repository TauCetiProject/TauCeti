/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.TransferInstance
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic

/-!
# Reconstructing variable-rank vector bundles in a target universe via `Shrink`

While `FiniteRankAtlas.toBundle` (in `Bundle/Atlas.lean`) lands in `FiniteRankBundle.{max v w} 𝕜 X`
via `ULift`, under `[UnivLE.{v, w}]` `FiniteRankAtlas.toBundleShrink` reconstructs a
`Type w`-fibred variable-rank vector bundle `FiniteRankBundle.{w} 𝕜 X` directly from a small
coordinate atlas `A : FiniteRankAtlas 𝕜 X` via `Shrink.{w}`, together with its stratum fibre
equivalences `FiniteRankAtlas.toBundleShrinkStratumEquiv`, total-space homeomorphism
`FiniteRankAtlas.toBundleShrinkHomeomorph`, functorial action
`FiniteRankAtlas.toBundleShrinkFunctor`, and preferred-chart identification
`FiniteRankBundle.fiberContinuousLinearEquiv_toBundleShrink`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti

universe w u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

namespace FiniteRankAtlas

section ToBundleShrink

variable (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}]

/-- Continuous linear equivalence between the shrunk coordinate fibre over `y.val` and the native
`n`-stratum coordinate fibre over `y`. -/
noncomputable def toBundleShrinkStratumEquiv (n : ℕ) (y : {x : X // A.rank x = n}) :
    Shrink.{w} (A.Fiber y.val) ≃L[𝕜] (A.charts n).Fiber y :=
  (Shrink.continuousLinearEquiv 𝕜 (A.Fiber y.val)).trans
    { toFun := fun v i ↦ v (Fin.cast y.property.symm i)
      invFun := fun v i ↦ v (Fin.cast y.property i)
      left_inv := fun v ↦ funext fun i ↦ by simp
      right_inv := fun v ↦ funext fun i ↦ by simp
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_pi fun i ↦ continuous_apply (Fin.cast y.property.symm i)
      continuous_invFun := continuous_pi fun i ↦ continuous_apply (Fin.cast y.property i) }

@[simp] theorem toBundleShrinkStratumEquiv_rfl_apply (x : X) (u : Shrink.{w} (A.Fiber x)) :
    A.toBundleShrinkStratumEquiv (A.rank x) ⟨x, rfl⟩ u =
      Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) u := by rfl

@[simp] theorem toBundleShrinkStratumEquiv_rfl_symm_apply (x : X)
    (v : (A.charts (A.rank x)).Fiber ⟨x, rfl⟩) :
    (A.toBundleShrinkStratumEquiv (A.rank x) ⟨x, rfl⟩).symm v =
      (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).symm v := by rfl

/-- Realize a small coordinate atlas `A : FiniteRankAtlas 𝕜 X` as a variable-rank vector bundle
with fibres in `Type w` whenever `UnivLE.{v, w}` holds. -/
-- Expose the object definition so `(A.toBundleShrink).Fiber` and `rank` reduce directly.
@[expose, implicit_reducible] noncomputable def toBundleShrink : FiniteRankBundle.{w} 𝕜 X :=
  FiniteRankBundle.ofBundles 𝕜 A.rank (fun x ↦ Shrink.{w} (A.Fiber x))
    (fun n ↦ (A.charts n).Fiber) (toBundleShrinkStratumEquiv.{w} A)

@[simp] theorem rank_toBundleShrink :
    (A.toBundleShrink : FiniteRankBundle.{w} 𝕜 X).rank = A.rank := rfl

@[simp] theorem fiber_toBundleShrink (x : X) :
    (A.toBundleShrink : FiniteRankBundle.{w} 𝕜 X).Fiber x = Shrink.{w} (A.Fiber x) := by rfl

/-- The glued total space of `A.toBundleShrink` is homeomorphic over `X` to
`TotalSpace Unit A.Fiber` via `Shrink.continuousLinearEquiv` on each fibre. -/
noncomputable def toBundleShrinkHomeomorph :
    TotalSpace Unit (A.toBundleShrink : FiniteRankBundle.{w} 𝕜 X).Fiber ≃ₜ
      TotalSpace Unit A.Fiber :=
  (FiniteRankBundle.ofBundlesHomeomorph 𝕜 A.rank (fun x ↦ Shrink.{w} (A.Fiber x))
    (fun n ↦ (A.charts n).Fiber) (toBundleShrinkStratumEquiv.{w} A)).trans
    A.totalSpaceHomeomorph

@[simp] theorem toBundleShrinkHomeomorph_apply
    (p : TotalSpace Unit (A.toBundleShrink : FiniteRankBundle.{w} 𝕜 X).Fiber) :
    A.toBundleShrinkHomeomorph p =
      ⟨p.proj, Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj) p.snd⟩ := by
  rw [toBundleShrinkHomeomorph, Homeomorph.trans_apply,
    FiniteRankBundle.ofBundlesHomeomorph_apply, A.totalSpaceHomeomorph_apply]
  refine congrArg (TotalSpace.mk p.proj) (funext fun i ↦ ?_)
  dsimp only
  rw [Fin.cast_refl, id_eq]
  exact congrFun (A.toBundleShrinkStratumEquiv_rfl_apply p.proj p.snd) i

@[simp] theorem toBundleShrinkHomeomorph_symm_apply (q : TotalSpace Unit A.Fiber) :
    (A.toBundleShrinkHomeomorph :
      TotalSpace Unit (A.toBundleShrink : FiniteRankBundle.{w} 𝕜 X).Fiber ≃ₜ _).symm q =
      ⟨q.proj, (Shrink.continuousLinearEquiv 𝕜 (A.Fiber q.proj)).symm q.snd⟩ := by
  simp only [toBundleShrinkHomeomorph, Homeomorph.symm_trans_apply,
    A.totalSpaceHomeomorph_symm_apply]
  exact (FiniteRankBundle.ofBundlesHomeomorph_symm_apply 𝕜 A.rank _ _ _ (A.rank q.proj) _).trans
    (congrArg (TotalSpace.mk q.proj) (toBundleShrinkStratumEquiv_rfl_symm_apply A q.proj q.snd))

end ToBundleShrink

section ToBundleShrinkFunctor

variable [UnivLE.{v, w}]

variable (𝕜 X) in
/-- Reconstruct variable-rank vector bundles in fibre universe `w` from small coordinate atlases
whenever `UnivLE.{v, w}` holds. -/
-- Expose the object assignment so evaluated morphisms act on `Shrink (A.Fiber ·)`.
@[expose, implicit_reducible] noncomputable def toBundleShrinkFunctor :
    FiniteRankAtlas 𝕜 X ⥤ FiniteRankBundle.{w} 𝕜 X where
  obj A := A.toBundleShrink
  map {A D} f :=
    { fiberMap x := (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm.toLinearMap.comp
        ((f.fiberMap x).comp (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).toLinearMap)
      continuous_totalSpaceMap := (D.toBundleShrinkHomeomorph.symm.continuous.comp
        (f.totalSpaceMap.continuous.comp A.toBundleShrinkHomeomorph.continuous)).congr
        fun _ ↦ by
          simp only [Function.comp_apply, toBundleShrinkHomeomorph_apply,
            FiniteRankAtlas.Hom.totalSpaceMap_mk, toBundleShrinkHomeomorph_symm_apply]
          rfl }
  map_id A := FiniteRankBundle.hom_ext fun x ↦ LinearMap.ext fun v ↦
    (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).symm_apply_apply v
  map_comp {A B D} f g := FiniteRankBundle.hom_ext fun x ↦ LinearMap.ext fun v ↦
    congrArg (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm
      (congrArg (g.fiberMap x)
        ((Shrink.continuousLinearEquiv 𝕜 (B.Fiber x)).apply_symm_apply _).symm)

@[simp] theorem toBundleShrinkFunctor_obj (A : FiniteRankAtlas 𝕜 X) :
    (toBundleShrinkFunctor.{w} 𝕜 X).obj A = A.toBundleShrink := by rfl

@[simp] theorem fiberMap_toBundleShrinkFunctor_map_apply {A D : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ D) (x : X) (u : (A.toBundleShrink : FiniteRankBundle.{w} 𝕜 X).Fiber x) :
    ((toBundleShrinkFunctor.{w} 𝕜 X).map f).fiberMap x u =
      (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm
        (f.fiberMap x (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) u)) := rfl

instance : (toBundleShrinkFunctor.{w} 𝕜 X).Additive where
  map_add {_ _ _ _} := FiniteRankBundle.hom_ext fun _ ↦ LinearMap.ext fun _ ↦
    (Shrink.continuousLinearEquiv 𝕜 _).symm.map_add _ _

end ToBundleShrinkFunctor

end FiniteRankAtlas

namespace FiniteRankBundle

/-- On `A.toBundleShrink`, the preferred fibre equivalence at `x` is
`Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)`. -/
@[simp] theorem fiberContinuousLinearEquiv_toBundleShrink (A : FiniteRankAtlas 𝕜 X)
    [UnivLE.{v, w}] (x : X) :
    (A.toBundleShrink : FiniteRankBundle.{w} 𝕜 X).fiberContinuousLinearEquiv x =
      Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) := by
  let C := A.charts (A.rank x)
  refine DFunLike.ext _ _ fun v ↦ ?_
  rw [fiberContinuousLinearEquiv_apply]
  have htriv :
      (trivializationAt (Fin (A.rank x) → 𝕜)
          ((A.toBundleShrink : FiniteRankBundle.{w} 𝕜 X).StratumFiber (A.rank x)) ⟨x, rfl⟩
          ⟨⟨x, rfl⟩, v⟩).2 =
        (trivializationAt (Fin (A.rank x) → 𝕜) C.Fiber ⟨x, rfl⟩
          ⟨⟨x, rfl⟩, A.toBundleShrinkStratumEquiv (A.rank x) ⟨x, rfl⟩ v⟩).2 :=
    (letI := totalSpaceInduced (Fin (A.rank x) → 𝕜) (E := C.Fiber)
        fun y ↦ A.toBundleShrinkStratumEquiv (A.rank x) y;
      congrArg (fun e ↦ (e ⟨⟨x, rfl⟩, v⟩).2)
        (FiberBundle.trivializationAt_ofContinuousLinearEquiv (Fin (A.rank x) → 𝕜)
          (A.toBundleShrinkStratumEquiv (A.rank x))
          (isInducing_totalSpaceInduced (Fin (A.rank x) → 𝕜)
            fun y ↦ A.toBundleShrinkStratumEquiv (A.rank x) y) ⟨x, rfl⟩)).trans
      (letI := totalSpaceInduced (Fin (A.rank x) → 𝕜) (E := C.Fiber)
          fun y ↦ A.toBundleShrinkStratumEquiv (A.rank x) y;
        congrArg Prod.snd (Trivialization.compContinuousLinearEquiv_apply _ _ _ _))
  refine htriv.trans ?_
  rw [C.trivializationAt]
  exact (congrArg Prod.snd (C.localTriv_apply _)).trans
    ((C.coordChange_self _ _ (C.mem_baseSet_at ⟨x, rfl⟩) _).trans
      (A.toBundleShrinkStratumEquiv_rfl_apply x v))

end FiniteRankBundle

end TauCeti
