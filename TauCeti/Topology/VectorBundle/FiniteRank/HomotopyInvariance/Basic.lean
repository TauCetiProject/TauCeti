/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.HomotopyInvariance

/-!
# Homotopy invariance and cylinder extension for finite-rank bundle cores

This module lifts total-space homotopy invariance and relative cylinder trivialization extension
from `TauCeti.Topology.VectorBundle.HomotopyInvariance` to the category
`TauCeti.FiniteRankBundleCore 𝕜 B` of point-indexed finite-rank coordinate cores.

Relative extensions from CW subcomplexes and consequences for the split Grothendieck group
`SplitK0 (FiniteRankBundleCore 𝕜 ·)` live in the sibling modules
`TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance.CW` and
`TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance.SplitK0`.

## Main results

* `TauCeti.FiniteRankBundleCore.exists_iso_cylinder` and
  `TauCeti.FiniteRankBundleCore.nonempty_iso_pullback_cylinderSlice`: cylinder transport as a
  categorical isomorphism `(A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅ A` equal to
  the identity over `X × {0}`, and isomorphism of slice pullbacks at arbitrary times `s, t : I`.
* `TauCeti.FiniteRankBundleCore.exists_iso_cylinder_of_isClosed`: relative extension of a partial
  cylinder isomorphism from `s × I` (`s ⊆ X` closed) to all of `X × I` for real or complex cores.
* `ContinuousMap.Homotopic.nonempty_iso_pullback`,
  `ContinuousMap.HomotopicRel.exists_iso_pullback`, and
  `TauCeti.FiniteRankBundleCore.nonempty_iso_trivial_of_contractibleSpace`: free and relative
  homotopy invariance of core pullbacks over paracompact R₁ bases, and triviality over contractible
  paracompact R₁ bases.

## Implementation notes

Total-space continuity criteria and constructors (`isoOfTotalSpaceContinuous`, `isoFiberEquiv`, and
`ofCoreEquiv` in `TauCeti.Topology.VectorBundle.FiniteRank.Basic`, together with
`pullbackIsoOfTotalSpaceContinuous` and `pullbackHomeomorphOfEq` in
`TauCeti.Topology.VectorBundle.FiniteRank.Pullback`) convert total-space bundle equivalences
obtained from `TauCeti.Topology.VectorBundle.HomotopyInvariance` directly into categorical
isomorphisms in `FiniteRankBundleCore 𝕜 B`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Theorem 1.6, Proposition 1.7, and Corollary 1.8.
* M. F. Atiyah, *K-Theory*, §1.4, Lemma 1.4.3 and Theorem 1.4.3.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore
open scoped ContinuousMap Topology unitInterval

namespace TauCeti.FiniteRankBundleCore

section Cylinder

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
  {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]

/-- **Categorical cylinder theorem for finite-rank bundle cores.** Over a paracompact R₁ base `X`,
every finite-rank core `A` over `X × I` is isomorphic to the cylinder pullback of its time-zero
slice `A.pullback (cylinderSlice X 0)` by an isomorphism equal to the identity on every fibre over
`X × {0}`. -/
theorem exists_iso_cylinder (A : FiniteRankBundleCore 𝕜 (X × I)) :
    ∃ e : (A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅ A,
      ∀ x : X, e.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  obtain ⟨Φ, hΦ₁, hΦ₂, hΦ0⟩ := exists_continuousLinearEquiv_cylinder
    (𝕜 := 𝕜) (F := Fin A.rank → 𝕜) (E := A.core.Fiber)
  let eZ : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜) ((fun q : X × I ↦ (q.1, (0 : I))) *ᵖ A.core.Fiber) :=
    pullbackHomeomorphOfEq A ((cylinderSlice X 0).comp ContinuousMap.fst)
      (fun q ↦ (q.1, 0)) (funext fun q ↦ by simp)
  refine ⟨isoOfTotalSpaceContinuous (fun q ↦ ofCoreEquiv A A (q.1, 0) q (Φ q))
      ((hΦ₁.comp eZ.continuous).congr fun p ↦ by
        dsimp only [Function.comp_apply, eZ]
        rw [pullbackHomeomorphOfEq_apply]
        exact congrArg (TotalSpace.mk' _ _) (ofCoreEquiv_apply _ _ _ _ _ _).symm)
      ((eZ.symm.continuous.comp hΦ₂).congr fun p ↦ by
        dsimp only [Function.comp_apply, eZ]
        rw [pullbackHomeomorphOfEq_symm_apply]
        exact congrArg (TotalSpace.mk _) (ofCoreEquiv_symm_apply _ _ _ _ _ _).symm),
    fun x ↦ ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_⟩
  rw [fiberMap_isoOfTotalSpaceContinuous_hom]
  simp [hΦ0 x]
  rfl

/-- Over a paracompact R₁ base `X`, the slice pullbacks of a finite-rank core over `X × I` at any
two times `s, t : I` are isomorphic. -/
theorem nonempty_iso_pullback_cylinderSlice (A : FiniteRankBundleCore 𝕜 (X × I)) (s t : I) :
    Nonempty (A.pullback (cylinderSlice X s) ≅ A.pullback (cylinderSlice X t)) := by
  obtain ⟨e, -⟩ := exists_iso_cylinder A
  have eₛ : A.pullback (cylinderSlice X 0) ≅ A.pullback (cylinderSlice X s) := by
    simpa only [pullbackFunctor_obj, pullback_cylinderSlice_pullback_fst] using
      (pullbackFunctor (cylinderSlice X s)).mapIso e
  have eₜ : A.pullback (cylinderSlice X 0) ≅ A.pullback (cylinderSlice X t) := by
    simpa only [pullbackFunctor_obj, pullback_cylinderSlice_pullback_fst] using
      (pullbackFunctor (cylinderSlice X t)).mapIso e
  exact ⟨eₛ.symm ≪≫ eₜ⟩

end Cylinder

section RelativeCylinder

universe u v

variable {𝕜 : Type v} [RCLike 𝕜]
  {X : Type u} [TopologicalSpace X]

/-- **Relative categorical cylinder theorem for finite-rank bundle cores.** Let `X` be paracompact
and R₁, let `s ⊆ X` be closed, and let `A` be a real or complex finite-rank core over `X × I`.
Every partial cylinder isomorphism `e₀` over `s × I` equal to the identity on `s × {0}` extends to
a global cylinder isomorphism `e` over `X × I` equal to the identity on `X × {0}` whose restriction
along `cylinderSetIncl s` is `e₀`. -/
theorem exists_iso_cylinder_of_isClosed [R1Space X] [ParacompactSpace X] {s : Set X}
    (hs : IsClosed s) (A : FiniteRankBundleCore 𝕜 (X × I))
    (e₀ : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).pullback
        (cylinderSetIncl s) ≅ A.pullback (cylinderSetIncl s))
    (he₀ : ∀ x : s, e₀.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ∃ e : (A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅ A,
      (∀ x : X, e.hom.fiberMap (x, 0) = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) ∧
      (pullbackFunctor (cylinderSetIncl s)).mapIso e = e₀ := by
  let Φ₀ : ∀ q : s × I, A.core.Fiber (q.1.val, 0) ≃L[𝕜] A.core.Fiber (q.1.val, q.2) :=
    isoFiberEquiv e₀
  let eS₀ : (((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).pullback
      (cylinderSetIncl s)).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜) ((fun q : s × I ↦ (q.1.val, (0 : I))) *ᵖ A.core.Fiber) :=
    pullbackHomeomorphOfEq A (((cylinderSlice X 0).comp ContinuousMap.fst).comp (cylinderSetIncl s))
      (fun q ↦ (q.1.val, 0)) (funext fun q ↦ by simp)
  let eS₁ : (A.pullback (cylinderSetIncl s)).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜) ((fun q : s × I ↦ (q.1.val, q.2)) *ᵖ A.core.Fiber) :=
    pullbackHomeomorphOfEq A (cylinderSetIncl s) (fun q ↦ (q.1.val, q.2)) (coe_cylinderSetIncl s)
  have hΦ₀ : Continuous fun v : TotalSpace (Fin A.rank → 𝕜)
      ((fun q : s × I ↦ (q.1.val, (0 : I))) *ᵖ A.core.Fiber) ↦
      TotalSpace.mk' (Fin A.rank → 𝕜) (E := (fun q : s × I ↦ (q.1.val, q.2)) *ᵖ A.core.Fiber)
        v.proj (Φ₀ v.proj v.snd) :=
    (eS₁.continuous.comp (e₀.hom.continuous_totalSpaceMap.comp eS₀.symm.continuous)).congr
      fun ⟨x, w⟩ ↦ by
        dsimp only [Function.comp_apply, eS₀, eS₁, Φ₀]
        rw [pullbackHomeomorphOfEq_symm_apply]
        dsimp only
        refine (congrArg _ (CoordinateHom.totalSpaceMap_mk e₀.hom x w)).trans ?_
        rw [pullbackHomeomorphOfEq_apply]
        exact congrArg (TotalSpace.mk' _ _) (isoFiberEquiv_apply e₀ x w).symm
  have hΦ₀0 (x : s) : Φ₀ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (A.core.Fiber (x.val, 0)) :=
    DFunLike.ext _ _ fun (v : Fin A.rank → 𝕜) ↦
      (isoFiberEquiv_apply e₀ (x, 0) v).trans
        (congrArg (fun L : (Fin A.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜) ↦ L v) (he₀ x))
  obtain ⟨Φ, hfwd, hinv, h0, hs'⟩ := exists_continuousLinearEquiv_cylinder_of_isClosed_of_continuous
    (𝕜 := 𝕜) (F := Fin A.rank → 𝕜) (E := A.core.Fiber) hs Φ₀ hΦ₀ hΦ₀0
  let eZ : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜) ((fun q : X × I ↦ (q.1, (0 : I))) *ᵖ A.core.Fiber) :=
    pullbackHomeomorphOfEq A ((cylinderSlice X 0).comp ContinuousMap.fst)
      (fun q ↦ (q.1, 0)) (funext fun q ↦ by simp)
  refine ⟨isoOfTotalSpaceContinuous (fun q ↦ ofCoreEquiv A A (q.1, 0) q (Φ q))
      ((hfwd.comp eZ.continuous).congr fun p ↦ by
        dsimp only [Function.comp_apply, eZ]
        rw [pullbackHomeomorphOfEq_apply]
        exact congrArg (TotalSpace.mk' _ _) (ofCoreEquiv_apply _ _ _ _ _ _).symm)
      ((eZ.symm.continuous.comp hinv).congr fun p ↦ by
        dsimp only [Function.comp_apply, eZ]
        rw [pullbackHomeomorphOfEq_symm_apply]
        exact congrArg (TotalSpace.mk _) (ofCoreEquiv_symm_apply _ _ _ _ _ _).symm),
    fun x ↦ ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_,
    Iso.ext (hom_ext fun ⟨x, t⟩ ↦ ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_)⟩
  · rw [fiberMap_isoOfTotalSpaceContinuous_hom]
    simp [h0 x]
    rfl
  · rw [Functor.mapIso_hom, pullbackFunctor_map, fiberMap_pullbackMap, cylinderSetIncl_apply,
      fiberMap_isoOfTotalSpaceContinuous_hom]
    simp only [ContinuousLinearEquiv.coe_coe, ofCoreEquiv_apply, hs' x t]
    exact isoFiberEquiv_apply e₀ (x, t) v

end RelativeCylinder

section Homotopy

universe u v w

section Free

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
  {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {Y : Type w} [TopologicalSpace Y]

/-- **Homotopy invariance of finite-rank bundle cores.** Over a paracompact R₁ base `X`, homotopic
maps `f₀ f₁ : C(X, Y)` induce isomorphic pullbacks `A.pullback f₀ ≅ A.pullback f₁` for every
finite-rank core `A` over `Y`. -/
theorem _root_.ContinuousMap.Homotopic.nonempty_iso_pullback {f₀ f₁ : C(X, Y)}
    (h : f₀.Homotopic f₁) (A : FiniteRankBundleCore 𝕜 Y) :
    Nonempty (A.pullback f₀ ≅ A.pullback f₁) := by
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ :=
    h.exists_continuousLinearEquiv_pullback (𝕜 := 𝕜) (F := Fin A.rank → 𝕜) (E := A.core.Fiber)
  exact ⟨pullbackIsoOfTotalSpaceContinuous A A f₀ f₁
    (fun x ↦ ofCoreEquiv A A (f₀ x) (f₁ x) (Φ x))
    (hΦ₁.congr fun _ ↦ congrArg (TotalSpace.mk' _ _) (ofCoreEquiv_apply _ _ _ _ _ _).symm)
    (hΦ₂.congr fun _ ↦ congrArg (TotalSpace.mk' _ _) (ofCoreEquiv_symm_apply _ _ _ _ _ _).symm)⟩

/-- **Finite-rank bundle cores over contractible paracompact R₁ bases are trivial.** -/
theorem nonempty_iso_trivial_of_contractibleSpace [ContractibleSpace X]
    (A : FiniteRankBundleCore 𝕜 X) :
    Nonempty (A ≅ trivial 𝕜 X A.rank) := by
  obtain ⟨y, hy⟩ := id_nullhomotopic X
  obtain ⟨e⟩ := hy.nonempty_iso_pullback A
  rw [pullback_id, pullback_const] at e
  exact ⟨e⟩

end Free

section Relative

variable {𝕜 : Type v} [RCLike 𝕜]
  {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {Y : Type w} [TopologicalSpace Y]

/-- **Relative homotopy invariance of finite-rank bundle cores.** Over a paracompact R₁ base `X`,
if `s ⊆ X` is closed and `f₀ f₁ : C(X, Y)` are homotopic relative to `s`, then for every real or
complex finite-rank core `A` over `Y` there is an isomorphism `A.pullback f₀ ≅ A.pullback f₁`
whose fibre map over every point of `s` is the identity on `Fin A.rank → 𝕜`. -/
theorem _root_.ContinuousMap.HomotopicRel.exists_iso_pullback {s : Set X}
    {f₀ f₁ : C(X, Y)} (h : f₀.HomotopicRel f₁ s) (hs : IsClosed s)
    (A : FiniteRankBundleCore 𝕜 Y) :
    ∃ e : A.pullback f₀ ≅ A.pullback f₁,
      ∀ x ∈ s, e.hom.fiberMap x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  obtain ⟨Φ, hΦ₁, hΦ₂, hΦs⟩ := h.exists_continuousLinearEquiv_pullback
    (𝕜 := 𝕜) (F := Fin A.rank → 𝕜) (E := A.core.Fiber) hs
  refine ⟨pullbackIsoOfTotalSpaceContinuous A A f₀ f₁
      (fun x ↦ ofCoreEquiv A A (f₀ x) (f₁ x) (Φ x))
      (hΦ₁.congr fun _ ↦ congrArg (TotalSpace.mk' _ _) (ofCoreEquiv_apply _ _ _ _ _ _).symm)
      (hΦ₂.congr fun _ ↦ congrArg (TotalSpace.mk' _ _) (ofCoreEquiv_symm_apply _ _ _ _ _ _).symm),
    fun x hx ↦ ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_⟩
  rw [fiberMap_pullbackIsoOfTotalSpaceContinuous_hom]
  simp only [ContinuousLinearEquiv.coe_coe, ofCoreEquiv_apply]
  let sndCoord (p : TotalSpace (Fin A.rank → 𝕜) A.core.Fiber) : Fin A.rank → 𝕜 := p.snd
  exact congrArg sndCoord (hΦs x hx v)

end Relative

end Homotopy

end TauCeti.FiniteRankBundleCore
