/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Topology.Homotopy.Cylinder.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.HomotopyInvariance.Basic

/-!
# Homotopy invariance for finite-rank bundle cores

This module lifts total-space homotopy invariance from
`TauCeti.Topology.VectorBundle.HomotopyInvariance.Basic` to the category
`TauCeti.FiniteRankBundleCore 𝕜 B` of point-indexed finite-rank coordinate cores.

Relative extensions from closed subsets and CW subcomplexes live in the sibling modules
`TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance.Relative` and
`TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance.CW`; consequences for the split
Grothendieck group `SplitK0 (FiniteRankBundleCore 𝕜 ·)` live in
`TauCeti.Topology.VectorBundle.FiniteRank.HomotopyInvariance.SplitK0`.

## Main results

* `TauCeti.FiniteRankBundleCore.pullback_cylinderSlice_pullback_fst`: pulling back
  `A.pullback ContinuousMap.fst` along any time-`t` cylinder slice recovers `A`.
* `TauCeti.FiniteRankBundleCore.exists_iso_cylinder` and
  `TauCeti.FiniteRankBundleCore.nonempty_iso_pullback_cylinderSlice`: cylinder transport as a
  categorical isomorphism `(A.pullback (cylinderSlice X 0)).pullback ContinuousMap.fst ≅ A` equal to
  the identity over `X × {0}`, and isomorphism of slice pullbacks at arbitrary times `s, t : I`.
* `ContinuousMap.Homotopic.nonempty_iso_pullback` and
  `TauCeti.FiniteRankBundleCore.nonempty_iso_trivial_of_contractibleSpace`: free homotopy
  invariance of core pullbacks over paracompact R₁ bases, and triviality over contractible
  paracompact R₁ bases.

## Implementation notes

Total-space continuity criteria and constructors (`isoOfTotalSpaceContinuous` and `ofCoreEquiv` in
`TauCeti.Topology.VectorBundle.FiniteRank.Basic`, together with `pullbackIsoOfTotalSpaceContinuous`
and `pullbackHomeomorphOfEq` in `TauCeti.Topology.VectorBundle.FiniteRank.Pullback`) convert
total-space bundle equivalences obtained from
`TauCeti.Topology.VectorBundle.HomotopyInvariance.Basic` directly into categorical isomorphisms in
`FiniteRankBundleCore 𝕜 B`.

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

/-- Pulling back `A.pullback ContinuousMap.fst` along any time-`t` cylinder slice recovers `A`. -/
theorem pullback_cylinderSlice_pullback_fst {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {X : Type u} [TopologicalSpace X] (A : FiniteRankBundleCore 𝕜 X) (t : I) :
    (A.pullback ContinuousMap.fst).pullback (cylinderSlice X t) = A := by
  rw [pullback_comp, fst_comp_cylinderSlice, pullback_id]

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
      TotalSpace (Fin A.rank → 𝕜) ((cylinderZero X : X × I → X × I) *ᵖ A.core.Fiber) :=
    pullbackHomeomorphOfEq A ((cylinderSlice X 0).comp ContinuousMap.fst)
      (cylinderZero X) (congrArg DFunLike.coe (cylinderSlice_zero_comp_fst X))
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

section Homotopy

universe u v w

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

end Homotopy

end TauCeti.FiniteRankBundleCore
