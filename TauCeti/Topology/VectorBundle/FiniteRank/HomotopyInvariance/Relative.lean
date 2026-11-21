/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance.Basic
public import TauCeti.Topology.VectorBundle.HomotopyInvariance.Relative

/-!
# Relative homotopy invariance and cylinder extension for finite-rank bundle cores

This module lifts relative cylinder trivialization extension and relative homotopy invariance from
`TauCeti.Topology.VectorBundle.HomotopyInvariance.Relative` to the category
`TauCeti.FiniteRankBundleCore 𝕜 B` of point-indexed finite-rank coordinate cores.

Relative extensions from CW subcomplexes live in
`TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance.CW`.

## Main results

* `TauCeti.FiniteRankBundleCore.exists_iso_cylinder_of_isClosed`: relative extension of a partial
  cylinder isomorphism from `s × I` (`s ⊆ X` closed) to all of `X × I` for real or complex cores.
* `ContinuousMap.HomotopicRel.exists_iso_pullback`: relative homotopy invariance of core pullbacks
  over paracompact R₁ bases.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Proposition 1.7.
* M. F. Atiyah, *K-Theory*, §1.4, Lemma 1.4.3.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore
open scoped ContinuousMap Topology unitInterval

namespace TauCeti.FiniteRankBundleCore

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
      TotalSpace (Fin A.rank → 𝕜)
        ((((cylinderZero X).comp (cylinderSetIncl s) : s × I → X × I)) *ᵖ A.core.Fiber) :=
    pullbackHomeomorphOfEq A (((cylinderSlice X 0).comp ContinuousMap.fst).comp (cylinderSetIncl s))
      (((cylinderZero X).comp (cylinderSetIncl s) : s × I → X × I))
      (congrArg (fun f : C(X × I, X × I) ↦ (f.comp (cylinderSetIncl s) : s × I → X × I))
        (cylinderSlice_zero_comp_fst X))
  let eS₁ : (A.pullback (cylinderSetIncl s)).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜) ((cylinderSetIncl s : s × I → X × I) *ᵖ A.core.Fiber) :=
    pullbackHomeomorph A (cylinderSetIncl s)
  have hΦ₀ : Continuous fun v : TotalSpace (Fin A.rank → 𝕜)
      ((((cylinderZero X).comp (cylinderSetIncl s) : s × I → X × I)) *ᵖ A.core.Fiber) ↦
      TotalSpace.mk' (Fin A.rank → 𝕜) (E := (cylinderSetIncl s : s × I → X × I) *ᵖ A.core.Fiber)
        v.proj (Φ₀ v.proj v.snd) :=
    (eS₁.continuous.comp (e₀.hom.continuous_totalSpaceMap.comp eS₀.symm.continuous)).congr
      fun ⟨x, w⟩ ↦ by
        dsimp only [Function.comp_apply, eS₀, eS₁, Φ₀]
        rw [pullbackHomeomorphOfEq_symm_apply]
        dsimp only
        refine (congrArg _ (CoordinateHom.totalSpaceMap_mk e₀.hom x w)).trans ?_
        rw [pullbackHomeomorph_apply]
        exact congrArg (TotalSpace.mk' _ _) (isoFiberEquiv_apply e₀ x w).symm
  have hΦ₀0 (x : s) : Φ₀ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (A.core.Fiber (x.val, 0)) :=
    DFunLike.ext _ _ fun (v : Fin A.rank → 𝕜) ↦
      (isoFiberEquiv_apply e₀ (x, 0) v).trans
        (congrArg (fun L : (Fin A.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜) ↦ L v) (he₀ x))
  obtain ⟨Φ, hfwd, hinv, h0, hs'⟩ := exists_continuousLinearEquiv_cylinder_of_isClosed_of_continuous
    (𝕜 := 𝕜) (F := Fin A.rank → 𝕜) (E := A.core.Fiber) hs Φ₀ hΦ₀ hΦ₀0
  let eZ : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜) ((cylinderZero X : X × I → X × I) *ᵖ A.core.Fiber) :=
    pullbackHomeomorphOfEq A ((cylinderSlice X 0).comp ContinuousMap.fst)
      (cylinderZero X) (congrArg DFunLike.coe (cylinderSlice_zero_comp_fst X))
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

section RelativeHomotopy

universe u v w

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

end RelativeHomotopy

end TauCeti.FiniteRankBundleCore
