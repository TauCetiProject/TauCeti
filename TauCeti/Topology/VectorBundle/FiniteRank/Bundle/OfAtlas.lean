/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.TransferInstance
public import TauCeti.Topology.FiberBundle.TotalSpace
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Preadditive
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic

/-!
# Reconstructing variable-rank vector bundles in a target universe

Under `[UnivLE.{v, w}]`, `FiniteRankAtlas.toBundle` reconstructs a `Type w`-fibred variable-rank
vector bundle `FiniteRankBundle.{w} 𝕜 X` from a small coordinate atlas `A : FiniteRankAtlas 𝕜 X`
via `Shrink.{w}`, together with its stratum fibre equivalences
`FiniteRankAtlas.toBundleStratumEquiv`, total-space homeomorphism
`FiniteRankAtlas.toBundleHomeomorph`, functorial action `FiniteRankAtlas.toBundleFunctor`, and
preferred-chart identification `FiniteRankBundle.fiberContinuousLinearEquiv_toBundle`.

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

section ToBundle

variable (A : FiniteRankAtlas 𝕜 X) [UnivLE.{v, w}]

/-- Continuous linear equivalence between the shrunk coordinate fibre over `y.val` and the native
`n`-stratum coordinate fibre over `y`. -/
noncomputable def toBundleStratumEquiv (n : ℕ) (y : {x : X // A.rank x = n}) :
    Shrink.{w} (A.Fiber y.val) ≃L[𝕜] (A.charts n).Fiber y :=
  (Shrink.continuousLinearEquiv 𝕜 (A.Fiber y.val)).trans
    (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ 𝕜) (finCongr y.property))

@[simp] theorem toBundleStratumEquiv_rfl_apply (x : X) (u : Shrink.{w} (A.Fiber x)) :
    A.toBundleStratumEquiv (A.rank x) ⟨x, rfl⟩ u =
      Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) u := (rfl)

@[simp] theorem toBundleStratumEquiv_rfl_symm_apply (x : X)
    (v : (A.charts (A.rank x)).Fiber ⟨x, rfl⟩) :
    (A.toBundleStratumEquiv (A.rank x) ⟨x, rfl⟩).symm v =
      (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).symm v := (rfl)

/-- Realize a small coordinate atlas `A : FiniteRankAtlas 𝕜 X` as a variable-rank vector bundle
with fibres in `Type w` whenever `UnivLE.{v, w}` holds. -/
-- Expose the object definition so `(A.toBundle).Fiber` and `rank` reduce directly.
@[expose, implicit_reducible] noncomputable def toBundle : FiniteRankBundle.{w} 𝕜 X :=
  FiniteRankBundle.ofBundles 𝕜 A.rank (fun x ↦ Shrink.{w} (A.Fiber x))
    (fun n ↦ (A.charts n).Fiber) (toBundleStratumEquiv.{w} A)

@[simp] theorem rank_toBundle :
    (A.toBundle : FiniteRankBundle.{w} 𝕜 X).rank = A.rank := (rfl)

@[simp] theorem fiber_toBundle (x : X) :
    (A.toBundle : FiniteRankBundle.{w} 𝕜 X).Fiber x = Shrink.{w} (A.Fiber x) := (rfl)

/-- The glued total space of `A.toBundle` is homeomorphic over `X` to
`TotalSpace Unit A.Fiber` via `Shrink.continuousLinearEquiv` on each fibre. -/
noncomputable def toBundleHomeomorph :
    TotalSpace Unit (A.toBundle : FiniteRankBundle.{w} 𝕜 X).Fiber ≃ₜ
      TotalSpace Unit A.Fiber :=
  (FiniteRankBundle.ofBundlesHomeomorph 𝕜 A.rank (fun x ↦ Shrink.{w} (A.Fiber x))
    (fun n ↦ (A.charts n).Fiber) (toBundleStratumEquiv.{w} A)).trans
    A.totalSpaceHomeomorph

@[simp] theorem toBundleHomeomorph_apply
    (p : TotalSpace Unit (A.toBundle : FiniteRankBundle.{w} 𝕜 X).Fiber) :
    A.toBundleHomeomorph p =
      ⟨p.proj, Shrink.continuousLinearEquiv 𝕜 (A.Fiber p.proj) p.snd⟩ := by
  rw [toBundleHomeomorph, Homeomorph.trans_apply,
    FiniteRankBundle.ofBundlesHomeomorph_apply, A.totalSpaceHomeomorph_apply]
  refine congrArg (TotalSpace.mk p.proj) (funext fun i ↦ ?_)
  dsimp only
  rw [Fin.cast_refl, id_eq]
  exact congrFun (A.toBundleStratumEquiv_rfl_apply p.proj p.snd) i

@[simp] theorem toBundleHomeomorph_symm_apply (q : TotalSpace Unit A.Fiber) :
    (A.toBundleHomeomorph :
      TotalSpace Unit (A.toBundle : FiniteRankBundle.{w} 𝕜 X).Fiber ≃ₜ _).symm q =
      ⟨q.proj, (Shrink.continuousLinearEquiv 𝕜 (A.Fiber q.proj)).symm q.snd⟩ := by
  simp only [toBundleHomeomorph, Homeomorph.symm_trans_apply,
    A.totalSpaceHomeomorph_symm_apply]
  exact (FiniteRankBundle.ofBundlesHomeomorph_symm_apply 𝕜 A.rank _ _ _ (A.rank q.proj) _).trans
    (congrArg (TotalSpace.mk q.proj) (toBundleStratumEquiv_rfl_symm_apply A q.proj q.snd))

end ToBundle

section ToBundleFunctor

variable [UnivLE.{v, w}]

variable (𝕜 X) in
/-- Reconstruct variable-rank vector bundles in fibre universe `w` from small coordinate atlases
whenever `UnivLE.{v, w}` holds. -/
-- Expose the object assignment so evaluated morphisms act on `Shrink (A.Fiber ·)`.
@[expose, implicit_reducible] noncomputable def toBundleFunctor :
    FiniteRankAtlas 𝕜 X ⥤ FiniteRankBundle.{w} 𝕜 X where
  obj A := A.toBundle
  map {A D} f :=
    { fiberMap x := (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm.toLinearMap.comp
        ((f.fiberMap x).comp (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).toLinearMap)
      continuous_totalSpaceMap :=
        -- `rfl` unfolds `LinearMap.comp` across `fiber_toBundle`.
        continuous_totalSpace_conj A.toBundleHomeomorph.continuous
          D.toBundleHomeomorph.symm.continuous
          A.toBundleHomeomorph_apply D.toBundleHomeomorph_symm_apply
          (fun _ ↦ rfl) f.continuous_totalSpaceMap }
  map_id A := FiniteRankBundle.hom_ext fun x ↦ LinearMap.ext fun v ↦
    (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)).symm_apply_apply v
  map_comp {_ _ D} _ g := FiniteRankBundle.hom_ext fun x ↦ LinearMap.ext fun _ ↦
    congrArg (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm
      (congrArg (g.fiberMap x)
        ((Shrink.continuousLinearEquiv 𝕜 _).apply_symm_apply _).symm)

@[simp] theorem toBundleFunctor_obj (A : FiniteRankAtlas 𝕜 X) :
    (toBundleFunctor.{w} 𝕜 X).obj A = A.toBundle := (rfl)

@[simp] theorem fiberMap_toBundleFunctor_map_apply {A D : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ D) (x : X) (u : (A.toBundle : FiniteRankBundle.{w} 𝕜 X).Fiber x) :
    ((toBundleFunctor.{w} 𝕜 X).map f).fiberMap x u =
      (Shrink.continuousLinearEquiv 𝕜 (D.Fiber x)).symm
        (f.fiberMap x (Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) u)) := (rfl)

instance : (toBundleFunctor.{w} 𝕜 X).Additive where
  map_add {_ _ _ _} := FiniteRankBundle.hom_ext fun _ ↦ LinearMap.ext fun _ ↦
    (Shrink.continuousLinearEquiv 𝕜 _).symm.map_add _ _

end ToBundleFunctor

end FiniteRankAtlas

namespace FiniteRankBundle

/-- On `A.toBundle`, the preferred fibre equivalence at `x` is
`Shrink.continuousLinearEquiv 𝕜 (A.Fiber x)`. -/
@[simp] theorem fiberContinuousLinearEquiv_toBundle (A : FiniteRankAtlas 𝕜 X)
    [UnivLE.{v, w}] (x : X) :
    (A.toBundle : FiniteRankBundle.{w} 𝕜 X).fiberContinuousLinearEquiv x =
      Shrink.continuousLinearEquiv 𝕜 (A.Fiber x) := by
  let C := A.charts (A.rank x)
  refine DFunLike.ext _ _ fun v ↦ ?_
  rw [fiberContinuousLinearEquiv_apply]
  have htriv :
      (trivializationAt (Fin (A.rank x) → 𝕜)
          ((A.toBundle : FiniteRankBundle.{w} 𝕜 X).StratumFiber (A.rank x)) ⟨x, rfl⟩
          ⟨⟨x, rfl⟩, v⟩).2 =
        (trivializationAt (Fin (A.rank x) → 𝕜) C.Fiber ⟨x, rfl⟩
          ⟨⟨x, rfl⟩, A.toBundleStratumEquiv (A.rank x) ⟨x, rfl⟩ v⟩).2 :=
    (letI := totalSpaceInduced (Fin (A.rank x) → 𝕜) (E := C.Fiber)
        fun y ↦ A.toBundleStratumEquiv (A.rank x) y;
      congrArg (fun e ↦ (e ⟨⟨x, rfl⟩, v⟩).2)
        (FiberBundle.trivializationAt_ofContinuousLinearEquiv (Fin (A.rank x) → 𝕜)
          (A.toBundleStratumEquiv (A.rank x))
          (isInducing_totalSpaceInduced (Fin (A.rank x) → 𝕜)
            fun y ↦ A.toBundleStratumEquiv (A.rank x) y) ⟨x, rfl⟩)).trans
      (letI := totalSpaceInduced (Fin (A.rank x) → 𝕜) (E := C.Fiber)
          fun y ↦ A.toBundleStratumEquiv (A.rank x) y;
        congrArg Prod.snd (Trivialization.compContinuousLinearEquiv_apply _ _ _ _))
  refine htriv.trans ?_
  rw [C.trivializationAt]
  exact (congrArg Prod.snd (C.localTriv_apply _)).trans
    ((C.coordChange_self _ _ (C.mem_baseSet_at ⟨x, rfl⟩) _).trans
      (A.toBundleStratumEquiv_rfl_apply x v))

end FiniteRankBundle

end TauCeti
