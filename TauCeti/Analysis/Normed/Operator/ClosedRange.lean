/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# The a priori estimate of a closed-range operator

A continuous linear map `T : E →L[𝕜] F` between Banach spaces with closed range fails to be
bounded below only in the direction of its kernel. When that kernel is complemented, this file
makes the failure quantitative, in the classical form

`‖x‖ ≤ C * ‖T x‖ + ‖P x‖`,

where `P` is a continuous projection of `E` onto `ker T`. When `ker T` is finite-dimensional, as
for a Fredholm operator, `P x` lies in a finite-dimensional space, and over a proper normed field,
such as `ℝ` or `ℂ`, the finite-rank projection `P` is a compact operator.

## Main declarations

* `ContinuousLinearMap.exists_norm_le_mul_norm_of_mem`: a closed-range operator is bounded below
  on any topological complement of its kernel.
* `ContinuousLinearMap.exists_norm_le_mul_norm_add_norm_projectionL`: the a priori estimate
  against the projection onto the kernel determined by a chosen complement.
* `ContinuousLinearMap.exists_projection_norm_le`: the same estimate with the
  complement discharged, so that the only data left is a continuous projection with range the
  kernel.

`TauCeti.Analysis.Fredholm.Proper` uses the estimate below to prove
that a map with Fredholm derivative is proper near a point (Smale, *An infinite dimensional version
of Sard's theorem*, Amer. J. Math. 87 (1965)); local properness is in turn what makes the critical
values of such a map locally closed, and hence what upgrades Sard--Smale from a density statement
to a residuality statement.
-/

public section

namespace ContinuousLinearMap

open Submodule

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {X₁ : Submodule 𝕜 E}

variable [CompleteSpace E] [CompleteSpace F]

/-- **A closed-range operator is bounded below off its kernel.** On any topological complement
`X₁` of `ker T` there is a constant `C > 0` with `‖x‖ ≤ C * ‖T x‖` for every `x ∈ X₁`. -/
theorem exists_norm_le_mul_norm_of_mem (T : E →L[𝕜] F)
    (hclosed : IsClosed (T.range : Set F)) (h : IsTopCompl (T.ker) X₁) :
    ∃ C > 0, ∀ x ∈ X₁, ‖x‖ ≤ C * ‖T x‖ := by
  have : CompleteSpace X₁ := h.isClosed'.completeSpace_coe
  have hinj : Function.Injective (T ∘L X₁.subtypeL) :=
    LinearMap.injective_domRestrict_iff.mpr h.isCompl.disjoint.symm
  have hrange : (T ∘L X₁.subtypeL).range = T.range := by
    simpa only [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      Submodule.toLinearMap_subtypeL, Submodule.range_subtype] using
      (map_eq_range_iff.mpr h.isCompl.codisjoint.symm : X₁.map T.toLinearMap = T.range)
  have hclosed_restrict : IsClosed (Set.range (T ∘L X₁.subtypeL)) := by
    have hc : IsClosed ((T ∘L X₁.subtypeL).range : Set F) := hrange.symm ▸ hclosed
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using hc
  -- The open mapping theorem, applied to the restriction of `T` to `X₁`.
  obtain ⟨K, hK⟩ :=
    (T ∘L X₁.subtypeL).antilipschitz_of_injective_of_isClosed_range hinj hclosed_restrict
  refine ⟨K + 1, by positivity, fun x hx => ?_⟩
  have hx' := hK.le_mul_dist (⟨x, hx⟩ : X₁) 0
  simp only [ContinuousLinearMap.comp_apply, coe_subtypeL, coe_subtype, map_zero,
    dist_eq_norm, sub_zero] at hx'
  calc ‖x‖ ≤ (K : ℝ) * ‖T x‖ := hx'
    _ ≤ ((K : ℝ) + 1) * ‖T x‖ := by gcongr; exact le_add_of_nonneg_right zero_le_one

/-- **The a priori estimate of a closed-range operator**, stated against the projection onto the
kernel along a chosen topological complement: there is a `C > 0` with
`‖x‖ ≤ C * ‖T x‖ + ‖P x‖` for all `x`, where `P` is that projection. -/
theorem exists_norm_le_mul_norm_add_norm_projectionL
    (T : E →L[𝕜] F) (hclosed : IsClosed (T.range : Set F)) (h : IsTopCompl (T.ker) X₁) :
    ∃ C > 0, ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖(T.ker).projectionL X₁ h x‖ := by
  obtain ⟨C, hC, hbound⟩ := T.exists_norm_le_mul_norm_of_mem hclosed h
  refine ⟨C, hC, fun x => ?_⟩
  have hsum : (T.ker).projectionL X₁ h x + X₁.projectionL (T.ker) h.symm x = x :=
    projectionL_add_projectionL_eq_self h x
  have hq := hbound (X₁.projectionL (T.ker) h.symm x)
    (X₁.projectionOntoL (T.ker) h.symm x).2
  have hTx : T (X₁.projectionL (T.ker) h.symm x) = T x := by
    have hker : T ((T.ker).projectionL X₁ h x) = 0 :=
      LinearMap.mem_ker.mp (projectionL_apply_mem h x)
    rw [projectionL_eq_self_sub_projectionL h, map_sub, hker, sub_zero]
  rw [hTx] at hq
  calc ‖x‖ = ‖(T.ker).projectionL X₁ h x + X₁.projectionL (T.ker) h.symm x‖ := by rw [hsum]
    _ ≤ ‖(T.ker).projectionL X₁ h x‖ + ‖X₁.projectionL (T.ker) h.symm x‖ := norm_add_le _ _
    _ ≤ ‖(T.ker).projectionL X₁ h x‖ + C * ‖T x‖ := by gcongr
    _ = C * ‖T x‖ + ‖(T.ker).projectionL X₁ h x‖ := add_comm _ _

/-- **The a priori estimate of a closed-range operator with complemented kernel**, with the
complement discharged: there is a continuous projection `P` of `E` onto `ker T` and a constant
`C > 0` with
`‖x‖ ≤ C * ‖T x‖ + ‖P x‖`.

When `ker T` is finite-dimensional, `P x` lies in the finite-dimensional space `ker T`, and over
a proper normed field the finite-rank projection `P` is compact. This says that a Fredholm
operator is bounded below "up to a compact error". -/
theorem exists_projection_norm_le (T : E →L[𝕜] F)
    (hclosed : IsClosed (T.range : Set F)) (hcompl : T.ker.ClosedComplemented) :
    ∃ (P : E →L[𝕜] E) (C : ℝ), 0 < C ∧ IsIdempotentElem P ∧ P.range = T.ker ∧
      ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖P x‖ := by
  obtain ⟨X₁, h⟩ := hcompl.exists_isTopCompl
  obtain ⟨C, hC, hbound⟩ := T.exists_norm_le_mul_norm_add_norm_projectionL hclosed h
  exact ⟨(T.ker).projectionL X₁ h, C, hC, isIdempotentElem_projectionL h,
    range_projectionL h, hbound⟩

end ContinuousLinearMap
