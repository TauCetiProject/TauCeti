/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Compact

/-!
# Resolvents of the inverse of an injective bounded operator

Let `T : X →L[𝕜] X` be an injective continuous linear operator. Its inverse
`A = ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse` is a partial linear map with domain the range of `T`,
characterized by `T (A x) = x`. Unbounded operators often arise this way: the Dirichlet
realization of an elliptic operator is the inverse of the solution operator of its Dirichlet
problem.

This file computes the resolvent of such an inverse. For `x = T z` in the domain,
`lambda • x - A x = -(1 - lambda • T) z`, so `lambda • I - A` factors through `1 - lambda • T`:

* `lambda` lies in the resolvent set of `A` exactly when `1 - lambda • T` is invertible
  (`ContinuousLinearMap.mem_resolventSet_inverse_toPMap_top_iff`), and then
  `R(lambda, A) = -T (1 - lambda • T)⁻¹`
  (`ContinuousLinearMap.resolvent_inverse_toPMap_top`). In particular `0` is a resolvent point
  and `R(0, A) = -T`.
* Over a field, a nonzero `lambda` lies in the spectrum of `A` exactly when `lambda⁻¹` lies in
  the spectrum of `T` (`ContinuousLinearMap.mem_spectrum_inverse_toPMap_top_iff`).
* If `T` is compact, `A` has compact resolvent, and on a Banach space the spectrum of `A`
  consists of the inverses of the nonzero eigenvalues of `T`, by the Fredholm alternative for
  compact operators (`ContinuousLinearMap.mem_spectrum_inverse_toPMap_top_iff_hasEigenvalue`).

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Chapter III, §6.1 and §6.8.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
-/

public section

noncomputable section

namespace ContinuousLinearMap

section Inverse

variable {𝕜 X : Type*} [CommRing 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
  [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
variable {T : X →L[𝕜] X} {lambda : 𝕜}

section Domain

omit [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]

/-- The domain of the inverse of `T` is the range of `T`. -/
theorem mem_domain_inverse_toPMap_top_iff (T : X →L[𝕜] X) {x : X} :
    x ∈ ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.domain ↔ ∃ y, T y = x := by
  rw [LinearPMap.inverse_domain, LinearMap.mem_range]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨⟨y, Submodule.mem_top⟩, hy⟩⟩

/-- `T y` lies in the domain of the inverse of `T`. -/
@[simp]
theorem apply_mem_domain_inverse_toPMap_top (T : X →L[𝕜] X) (y : X) :
    T y ∈ ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.domain :=
  (mem_domain_inverse_toPMap_top_iff T).2 ⟨y, rfl⟩

private theorem ker_toPMap_top_eq_bot (hT : Function.Injective T) :
    ((T : X →ₗ[𝕜] X).toPMap ⊤).ker = ⊥ := by
  rw [LinearMap.toPMap_ker, LinearMap.ker_eq_bot.2 hT, inf_bot_eq]

/-- The inverse of an injective `T` sends `T y` back to `y`. -/
@[simp]
theorem inverse_toPMap_top_apply (T : X →L[𝕜] X) (hT : Function.Injective T) (y : X) :
    ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse ⟨T y, apply_mem_domain_inverse_toPMap_top T y⟩ = y :=
  LinearPMap.inverse_apply_eq (ker_toPMap_top_eq_bot hT) (x := ⟨y, Submodule.mem_top⟩) rfl

/-- `T` is a left inverse of the inverse of `T`: `T (A x) = x` on the domain of `A`. -/
@[simp]
theorem apply_inverse_toPMap_top (T : X →L[𝕜] X) (hT : Function.Injective T)
    (x : ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.domain) :
    T (((T : X →ₗ[𝕜] X).toPMap ⊤).inverse x) = x := by
  obtain ⟨_, hx⟩ := x
  obtain ⟨y, rfl⟩ := (mem_domain_inverse_toPMap_top_iff T).1 hx
  rw [inverse_toPMap_top_apply T hT]

/-- The graph of the inverse of an injective `T` consists of the pairs `(T z, z)`. -/
theorem mem_graph_inverse_toPMap_top_iff (T : X →L[𝕜] X) (hT : Function.Injective T)
    {x : X × X} : x ∈ ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.graph ↔ T x.2 = x.1 := by
  rw [LinearPMap.inverse_graph (ker_toPMap_top_eq_bot hT), Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hTz⟩ := (LinearPMap.mem_graph_iff _).1 hy
    simp only [LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
      ← hz, ← hTz]
    exact (LinearMap.toPMap_apply _ _ z).symm
  · intro h
    refine ⟨(x.2, x.1), (LinearPMap.mem_graph_iff _).2 ⟨⟨x.2, Submodule.mem_top⟩, rfl, h⟩, rfl⟩

end Domain

/-- **The resolvent of the inverse.** If `U` is a two-sided inverse of `1 - lambda • T`, then
`-T U` inverts `lambda • I - A` for the inverse `A` of `T`. -/
theorem isResolventAt_inverse_toPMap_top (T : X →L[𝕜] X) (hT : Function.Injective T)
    {U : X →L[𝕜] X} (hU₁ : (1 - lambda • T) * U = 1) (hU₂ : U * (1 - lambda • T) = 1) :
    LinearPMap.IsResolventAt ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse lambda (-(T * U)) := by
  have hmem (y : X) : (-(T * U)) y ∈ ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.domain := by
    rw [neg_apply, mul_apply_eq_comp, ← map_neg]
    exact apply_mem_domain_inverse_toPMap_top T _
  refine ⟨hmem, fun y => ?_, fun x => ?_⟩
  · have hA : ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse ⟨(-(T * U)) y, hmem y⟩ = -U y := by
      simp_rw [neg_apply, mul_apply_eq_comp, ← map_neg]
      exact inverse_toPMap_top_apply T hT _
    have hy := congr($hU₁ y)
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply] at hy
    rw [hA, neg_apply, mul_apply_eq_comp, smul_neg, sub_neg_eq_add, neg_add_eq_sub, hy]
  · obtain ⟨_, hx⟩ := x
    obtain ⟨z, rfl⟩ := (mem_domain_inverse_toPMap_top_iff T).1 hx
    have hz := congr($hU₂ z)
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply] at hz
    rw [inverse_toPMap_top_apply T hT, neg_apply, mul_apply_eq_comp, ← neg_sub, map_neg, map_neg,
      neg_neg]
    exact congr(T $hz)

/-- An inverse of `lambda • I - A` for the inverse `A` of `T` gives the inverse `1 - lambda R` of
`1 - lambda • T`. -/
private theorem isUnit_one_sub_smul_of_isResolventAt (hT : Function.Injective T)
    {R : X →L[𝕜] X}
    (hR : LinearPMap.IsResolventAt ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse lambda R) :
    IsUnit (1 - lambda • T) := by
  -- `R y = lambda • T (R y) - T y`: apply `T` to `(lambda • I - A) (R y) = y`.
  have hR₁ (y : X) : R y = lambda • T (R y) - T y := by
    have h := congr(T $(hR.smul_sub_apply y))
    rw [map_sub, apply_inverse_toPMap_top T hT, map_smul] at h
    rw [← h, sub_sub_cancel]
  -- `R (y - lambda • T y) = -T y`: apply `R` to `(lambda • I - A) (T y) = lambda • T y - y`.
  have hR₂ (y : X) : R (y - lambda • T y) = -T y := by
    have h := hR.apply_smul_sub ⟨T y, apply_mem_domain_inverse_toPMap_top T y⟩
    rw [inverse_toPMap_top_apply T hT] at h
    rw [← neg_sub, map_neg, h]
  refine ⟨⟨1 - lambda • T, 1 - lambda • R, ext fun y => ?_, ext fun y => ?_⟩, rfl⟩
  · simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply, map_sub, map_smul]
    linear_combination (norm := module) (-lambda) • hR₁ y
  · simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply]
    rw [hR₂, smul_neg]
    abel

/-- **The resolvent set of the inverse.** `lambda` lies in the resolvent set of the inverse of an
injective `T` exactly when `1 - lambda • T` is invertible. -/
theorem mem_resolventSet_inverse_toPMap_top_iff (T : X →L[𝕜] X) (hT : Function.Injective T)
    (lambda : 𝕜) :
    lambda ∈ ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.resolventSet ↔ IsUnit (1 - lambda • T) := by
  refine ⟨fun h => ?_, fun hU => ?_⟩
  · obtain ⟨_, hR⟩ := LinearPMap.mem_resolventSet_iff.1 h
    exact isUnit_one_sub_smul_of_isResolventAt hT hR
  exact (isResolventAt_inverse_toPMap_top T hT hU.mul_val_inv hU.val_inv_mul).mem_resolventSet

/-- **The resolvent of the inverse** is `R(lambda) = -T (1 - lambda • T)⁻¹`. -/
theorem resolvent_inverse_toPMap_top (T : X →L[𝕜] X) (hT : Function.Injective T)
    (hU : IsUnit (1 - lambda • T)) :
    ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.resolvent lambda = -(T * ↑hU.unit⁻¹) :=
  LinearPMap.resolvent_eq_of_isResolventAt
    (isResolventAt_inverse_toPMap_top T hT hU.mul_val_inv hU.val_inv_mul)

/-- `0` is a resolvent point of the inverse of an injective `T`. -/
theorem zero_mem_resolventSet_inverse_toPMap_top (T : X →L[𝕜] X) (hT : Function.Injective T) :
    (0 : 𝕜) ∈ ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.resolventSet :=
  (mem_resolventSet_inverse_toPMap_top_iff T hT 0).2 (by simp)

/-- The resolvent of the inverse of `T` at `0` is `-T`. -/
@[simp]
theorem resolvent_inverse_toPMap_top_zero (T : X →L[𝕜] X) (hT : Function.Injective T) :
    ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.resolvent 0 = -T :=
  LinearPMap.resolvent_eq_of_isResolventAt <| by
    simpa using isResolventAt_inverse_toPMap_top (lambda := (0 : 𝕜)) (U := 1) T hT (by simp)
      (by simp)

/-- **The inverse of an injective compact operator has compact resolvent.** -/
theorem hasCompactResolvent_inverse_toPMap_top (T : X →L[𝕜] X) (hT : Function.Injective T)
    (hc : IsCompactOperator T) : ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.HasCompactResolvent := by
  refine LinearPMap.HasCompactResolvent.of_isCompactOperator_resolvent
    (zero_mem_resolventSet_inverse_toPMap_top T hT) ?_
  rw [resolvent_inverse_toPMap_top_zero T hT, FunLike.coe_neg]
  exact hc.neg

end Inverse

section Field

variable {𝕜 X : Type*} [Field 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
  [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]

/-- **The spectrum of the inverse.** A nonzero `lambda` lies in the spectrum of the inverse of an
injective `T` exactly when `lambda⁻¹` lies in the spectrum of `T`. -/
theorem mem_spectrum_inverse_toPMap_top_iff (T : X →L[𝕜] X) (hT : Function.Injective T)
    {lambda : 𝕜} (hlambda : lambda ≠ 0) :
    lambda ∈ ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.spectrum ↔ lambda⁻¹ ∈ spectrum 𝕜 T := by
  rw [LinearPMap.mem_spectrum_iff, mem_resolventSet_inverse_toPMap_top_iff T hT, spectrum.mem_iff,
    not_iff_not]
  have h : 1 - lambda • T = lambda • (algebraMap 𝕜 (X →L[𝕜] X) lambda⁻¹ - T) := by
    rw [smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul, mul_inv_cancel₀ hlambda, one_smul]
  rw [h, ← Units.smul_mk0 hlambda, isUnit_smul_iff]

end Field

section Compact

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

/-- **The spectrum of the inverse of a compact operator.** On a Banach space, a nonzero
`lambda` lies in the spectrum of the inverse of an injective compact operator `T` exactly when
`lambda⁻¹` is an eigenvalue of `T`. -/
theorem mem_spectrum_inverse_toPMap_top_iff_hasEigenvalue (T : X →L[𝕜] X)
    (hT : Function.Injective T) (hc : IsCompactOperator T) {lambda : 𝕜} (hlambda : lambda ≠ 0) :
    lambda ∈ ((T : X →ₗ[𝕜] X).toPMap ⊤).inverse.spectrum ↔
      Module.End.HasEigenvalue (T : Module.End 𝕜 X) lambda⁻¹ := by
  rw [mem_spectrum_inverse_toPMap_top_iff T hT hlambda,
    hc.hasEigenvalue_iff_mem_spectrum (inv_ne_zero hlambda)]

end Compact

end ContinuousLinearMap
