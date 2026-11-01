/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-!
# Stability and uniformity of coercive bilinear forms

Coercivity of a real continuous bilinear form is stable under perturbation in operator norm.
The estimate keeps track of the loss in the coercivity constant and does not require symmetry
or finite dimension. In finite dimension, coercivity is equivalent to strict positivity on
nonzero diagonal arguments. A compact family of such forms has a common coercivity constant.

For symmetric forms these results describe the open positive-definite cone, the model fibre
of the bundle of Riemannian metrics. The compact-family estimate is useful when comparing
metrics in local bundle coordinates: it gives a uniform margin for perturbing a metric.
-/

public section

open Set Metric Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A quadratic lower bound on the unit sphere extends to every vector by homogeneity. -/
theorem le_apply_self_of_forall_norm_eq_one (B : E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ}
    (h : ∀ v, ‖v‖ = 1 → c ≤ B v v) (v : E) :
    c * ‖v‖ * ‖v‖ ≤ B v v := by
  by_cases hv : v = 0
  · simp [hv]
  · have hunit := h ((‖v‖⁻¹ : ℝ) • v) (norm_smul_inv_norm hv)
    have hscale : B v v = ‖v‖ * ‖v‖ * B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) := by
      simp [map_smul, smul_eq_mul, field]
    rw [hscale]
    nlinarith [mul_le_mul_of_nonneg_left hunit (mul_self_nonneg ‖v‖)]

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Perturbing a bilinear form loses at most the operator norm of the perturbation from its
quadratic lower bound. No symmetry is needed. -/
theorem sub_norm_mul_norm_le_apply_self (B A : E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ}
    (hB : ∀ v, c * ‖v‖ * ‖v‖ ≤ B v v) (v : E) :
    (c - ‖A - B‖) * ‖v‖ * ‖v‖ ≤ A v v := by
  have h := (A - B).le_opNorm₂ v v
  have habs : |A v v - B v v| ≤ ‖A - B‖ * ‖v‖ * ‖v‖ := by
    simpa only [sub_apply, Real.norm_eq_abs] using h
  have := (abs_le.mp habs).1
  nlinarith [hB v]

end ContinuousLinearMap

namespace IsCoercive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {B : E →L[ℝ] E →L[ℝ] ℝ}

/-- A coercive form is strictly positive on nonzero diagonal arguments. -/
theorem apply_self_pos (hB : IsCoercive B) {v : E} (hv : v ≠ 0) : 0 < B v v := by
  obtain ⟨c, hc, h⟩ := hB
  exact (mul_pos (mul_pos hc (norm_pos_iff.mpr hv)) (norm_pos_iff.mpr hv)).trans_le (h v)

end IsCoercive

namespace IsCoercive

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  {B : E →L[ℝ] E →L[ℝ] ℝ}

/-- Every coercive form has an operator-norm neighbourhood with a common positive quadratic
lower bound, half of a coercivity constant for the original form. -/
theorem exists_pos_forall_norm_sub_lt (hB : IsCoercive B) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : E →L[ℝ] E →L[ℝ] ℝ, ‖A - B‖ < c →
      ∀ v, c * ‖v‖ * ‖v‖ ≤ A v v := by
  obtain ⟨d, hd, h⟩ := hB
  refine ⟨d / 2, half_pos hd, fun A hA v ↦ ?_⟩
  have hbound := B.sub_norm_mul_norm_le_apply_self A h v
  have hnonneg := mul_self_nonneg ‖v‖
  nlinarith

end IsCoercive

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Coercive real bilinear forms form an open set in the operator-norm topology, even in
infinite dimension. -/
theorem isOpen_setOf_isCoercive : IsOpen {B : E →L[ℝ] E →L[ℝ] ℝ | IsCoercive B} := by
  -- Fix the inner operator-space instances so the metric topology reduces to the hom topology.
  let : SeminormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toSeminormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  apply Metric.isOpen_iff.mpr
  intro B hB
  obtain ⟨c, hc, h⟩ := hB.exists_pos_forall_norm_sub_lt
  exact ⟨c, hc, fun A hA ↦ ⟨c, hc, h A (by simpa only [mem_ball, dist_eq_norm] using hA)⟩⟩

end TauCeti

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In finite dimension, positivity on nonzero diagonal arguments is equivalent to coercivity.
Symmetry is not required. -/
theorem isCoercive_iff_apply_self_pos [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    IsCoercive B ↔ ∀ v, v ≠ 0 → 0 < B v v := by
  refine ⟨fun h v hv ↦ h.apply_self_pos hv, fun h ↦ ?_⟩
  obtain ⟨c, hc, hbound⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    (B.continuous.clm_apply continuous_id).continuousOn
    (fun v hv ↦ h v (by
      have := mem_sphere_zero_iff_norm.mp hv
      intro hv0
      simp [hv0] at this))
  exact ⟨c, hc, B.le_apply_self_of_forall_norm_eq_one
    (fun v hv ↦ hbound v (mem_sphere_zero_iff_norm.mpr hv))⟩

end ContinuousLinearMap

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strictly positive diagonal forms form an open set in finite dimension. Restriction to the
symmetric subspace gives the open cone of positive-definite symmetric forms. -/
theorem isOpen_setOf_apply_self_pos [FiniteDimensional ℝ E] :
    IsOpen {B : E →L[ℝ] E →L[ℝ] ℝ | ∀ v, v ≠ 0 → 0 < B v v} := by
  simpa only [← ContinuousLinearMap.isCoercive_iff_apply_self_pos] using
    (isOpen_setOf_isCoercive (E := E))

end TauCeti

namespace IsCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous compact family of strictly positive diagonal forms in finite dimension has a
common positive coercivity constant. The parameter set may be empty. -/
theorem exists_pos_forall_le_apply_self [FiniteDimensional ℝ E]
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    {B : P → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContinuousOn B K)
    (hpos : ∀ p ∈ K, ∀ v, v ≠ 0 → 0 < B p v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, ∀ v, c * ‖v‖ * ‖v‖ ≤ B p v v := by
  have hcont : ContinuousOn (fun q : P × E ↦ B q.1 q.2 q.2) (K ×ˢ sphere (0 : E) 1) :=
    ((hB.comp continuous_fst.continuousOn
      (fun q (h : q ∈ K ×ˢ sphere (0 : E) 1) ↦ h.1)).clm_apply
      continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn
  obtain ⟨c, hc, hbound⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_forall_le'
    hcont (fun q hq ↦ hpos q.1 hq.1 q.2 (by
      have := mem_sphere_zero_iff_norm.mp hq.2
      intro hv
      simp [hv] at this))
  exact ⟨c, hc, fun p hp ↦ (B p).le_apply_self_of_forall_norm_eq_one
    (fun v hv ↦ hbound (p, v) ⟨hp, mem_sphere_zero_iff_norm.mpr hv⟩)⟩

end IsCompact
