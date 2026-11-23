/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
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
  let eZ : (A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅
      A.pullback (cylinderZero X) :=
    eqToIso (by rw [pullback_comp, cylinderSlice_zero_comp_fst])
  let e₀' : (A.pullback (cylinderZero X)).pullback (cylinderSetIncl s) ≅
      A.pullback (cylinderSetIncl s) :=
    ((pullbackFunctor (cylinderSetIncl s)).mapIso eZ).symm ≪≫ e₀
  let Φ₀ : s × I → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin A.rank → 𝕜) := isoFiberEquiv e₀'
  let Φ₀' : ∀ q : s × I, A.core.Fiber (q.1.val, 0) ≃L[𝕜] A.core.Fiber (q.1.val, q.2) := Φ₀
  let eS₀ : (A.pullback ((cylinderZero X).comp (cylinderSetIncl s))).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜)
        ((((cylinderZero X).comp (cylinderSetIncl s) : s × I → X × I)) *ᵖ A.core.Fiber) :=
    pullbackHomeomorph A ((cylinderZero X).comp (cylinderSetIncl s))
  let eS₁ : (A.pullback (cylinderSetIncl s)).core.TotalSpace ≃ₜ
      TotalSpace (Fin A.rank → 𝕜) ((cylinderSetIncl s : s × I → X × I) *ᵖ A.core.Fiber) :=
    pullbackHomeomorph A (cylinderSetIncl s)
  have hΦ₀ : Continuous fun v : TotalSpace (Fin A.rank → 𝕜)
      ((((cylinderZero X).comp (cylinderSetIncl s) : s × I → X × I)) *ᵖ A.core.Fiber) ↦
      TotalSpace.mk' (Fin A.rank → 𝕜) (E := (cylinderSetIncl s : s × I → X × I) *ᵖ A.core.Fiber)
        v.proj (Φ₀' v.proj v.snd) :=
    (eS₁.continuous.comp (e₀'.hom.continuous_totalSpaceMap.comp eS₀.symm.continuous)).congr
      fun ⟨x, w⟩ ↦ by
        dsimp only [Function.comp_apply, eS₀, eS₁, Φ₀', Φ₀]
        rw [pullbackHomeomorph_symm_apply]
        dsimp only
        refine (congrArg _ (CoordinateHom.totalSpaceMap_mk e₀'.hom x w)).trans ?_
        rw [pullbackHomeomorph_apply]
        exact congrArg (TotalSpace.mk' _ _) (isoFiberEquiv_apply e₀' x w).symm
  have hΦ₀0_fin (x : s) : Φ₀ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (Fin A.rank → 𝕜) := by
    ext v i
    simp only [Φ₀, isoFiberEquiv_apply, e₀', Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
      fiberMap_comp, ContinuousLinearMap.comp_apply, he₀ x, fiberMap_pullbackMap,
      cylinderSetIncl_apply]
    change eZ.inv.fiberMap (x.val, 0) v i = v i
    dsimp only [eZ]
    rw [eqToIso.inv, fiberMap_eqToHom_apply]
    rfl
  have hΦ₀0 (x : s) : Φ₀' (x, 0) = ContinuousLinearEquiv.refl 𝕜 (A.core.Fiber (x.val, 0)) :=
    ContinuousLinearEquiv.ext (funext fun v ↦
      congrArg (fun e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin A.rank → 𝕜) ↦ e v) (hΦ₀0_fin x))
  obtain ⟨Φ, hfwd, hinv, h0, hs'⟩ := exists_continuousLinearEquiv_cylinder_of_isClosed_of_continuous
    (𝕜 := 𝕜) (F := Fin A.rank → 𝕜) (E := A.core.Fiber) hs Φ₀' hΦ₀ hΦ₀0
  let Ψ : X × I → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin A.rank → 𝕜) := Φ
  have hΨ₁ : Continuous fun p : (A.pullback (cylinderZero X)).core.TotalSpace ↦
      (⟨p.proj, Ψ p.proj p.snd⟩ : A.core.TotalSpace) :=
    (hfwd.comp (A.pullbackHomeomorph (cylinderZero X)).continuous).congr fun p ↦ by
      rw [Function.comp_apply, A.pullbackHomeomorph_apply]; rfl
  have hΨ₂ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, (Ψ p.proj).symm p.snd⟩ : (A.pullback (cylinderZero X)).core.TotalSpace) :=
    ((A.pullbackHomeomorph (cylinderZero X)).symm.continuous.comp hinv).congr fun p ↦ by
      rw [Function.comp_apply]; exact A.pullbackHomeomorph_symm_apply _ _
  have hΨ0 (x : X) : Ψ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (Fin A.rank → 𝕜) :=
    ContinuousLinearEquiv.ext (funext fun v ↦
      congrArg (fun e : A.core.Fiber (x, 0) ≃L[𝕜] A.core.Fiber (x, 0) ↦ e v) (h0 x))
  have hΨs (x : s) (t : I) (w : Fin A.rank → 𝕜) :
      (Ψ (x.val, t)) w = e₀.hom.fiberMap (x, t) (eZ.inv.fiberMap (x.val, t) w) := by
    have h1 : (Ψ (x.val, t)) w = Φ₀ (x, t) w :=
      congrArg (fun e : A.core.Fiber (x.val, 0) ≃L[𝕜] A.core.Fiber (x.val, t) ↦ e w) (hs' x t)
    refine h1.trans ?_
    dsimp only [Φ₀]
    rw [isoFiberEquiv_apply]
    simp only [e₀', Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, fiberMap_comp,
      fiberMap_pullbackMap, cylinderSetIncl_apply, ContinuousLinearMap.comp_apply]
  refine ⟨eZ.trans (isoOfTotalSpaceContinuous Ψ hΨ₁ hΨ₂),
    fun x ↦ ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_,
    Iso.ext (hom_ext fun ⟨x, t⟩ ↦ ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_)⟩
  · simp only [Iso.trans_hom, fiberMap_comp, ContinuousLinearMap.comp_apply,
      fiberMap_isoOfTotalSpaceContinuous_hom, hΨ0 x, ContinuousLinearEquiv.coe_coe]
    ext i
    change eZ.hom.fiberMap (x, 0) v i = v i
    dsimp only [eZ]
    rw [eqToIso.hom, fiberMap_eqToHom_apply]
    rfl
  · simp only [Functor.mapIso_hom, fiberMap_pullbackMap, cylinderSetIncl_apply,
      Iso.trans_hom, fiberMap_comp, ContinuousLinearMap.comp_apply,
      fiberMap_isoOfTotalSpaceContinuous_hom, ContinuousLinearEquiv.coe_coe, hΨs x t]
    have hinv_hom : eZ.inv.fiberMap (x.val, t) (eZ.hom.fiberMap (x.val, t) v) = v := by
      have h := congrArg (fun k : ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst) ⟶
          ((A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst) ↦ k.fiberMap (x.val, t) v)
        eZ.hom_inv_id
      simpa only [fiberMap_comp, fiberMap_id, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
    rw [hinv_hom]

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
  let Ψ : X → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin A.rank → 𝕜) := Φ
  have hΨ₁ : Continuous fun v : TotalSpace (Fin A.rank → 𝕜) ((f₀ : X → Y) *ᵖ A.core.Fiber) ↦
      TotalSpace.mk' (Fin A.rank → 𝕜) (E := (f₁ : X → Y) *ᵖ A.core.Fiber)
        v.proj (Ψ v.proj v.snd) :=
    hΦ₁.congr fun _ ↦ rfl
  have hΨ₂ : Continuous fun v : TotalSpace (Fin A.rank → 𝕜) ((f₁ : X → Y) *ᵖ A.core.Fiber) ↦
      TotalSpace.mk' (Fin A.rank → 𝕜) (E := (f₀ : X → Y) *ᵖ A.core.Fiber)
        v.proj ((Ψ v.proj).symm v.snd) :=
    hΦ₂.congr fun _ ↦ rfl
  refine ⟨pullbackIsoOfTotalSpaceContinuous A A f₀ f₁ Ψ hΨ₁ hΨ₂,
    fun x hx ↦ ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_⟩
  rw [fiberMap_pullbackIsoOfTotalSpaceContinuous_hom]
  let sndCoord (p : TotalSpace (Fin A.rank → 𝕜) A.core.Fiber) : Fin A.rank → 𝕜 := p.snd
  exact congrArg sndCoord (hΦs x hx v)

end RelativeHomotopy

end TauCeti.FiniteRankBundleCore
