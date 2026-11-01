/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Stability and uniformity of coercive bilinear forms

Coercivity of a real continuous bilinear form is stable under perturbation in operator norm.
The estimate keeps track of the loss in the coercivity constant and does not require symmetry
or finite dimension. In finite dimension, coercivity is equivalent to strict positivity on
nonzero diagonal arguments, using `IsCompact.exists_pos_forall_mul_norm_sq_le` for the converse.

For symmetric forms these results describe the open positive-definite cone, the model fibre
of the bundle of Riemannian metrics. For finite-dimensional openness and compact-family bounds,
see `TauCeti.isOpen_setOf_forall_bilinear_apply_self_pos` and
`IsCompact.exists_pos_forall_mul_norm_sq_le`.
-/

public section

open Set Metric Topology

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
  obtain ⟨c, hc, hbound⟩ := (isCompact_singleton (x := ())).exists_pos_forall_mul_norm_sq_le
    (b := fun _ ↦ B) continuousOn_const fun _ _ ↦ h
  exact ⟨c, hc, fun v ↦ by simpa only [sq, mul_assoc] using hbound () rfl v⟩

end ContinuousLinearMap
