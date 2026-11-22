/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Clipped logarithmic envelopes for functions vanishing at infinity

For a continuous function `f : C₀(α, E)` vanishing at infinity and a threshold `δ > 0`, the clipped
logarithmic envelope `ZeroAtInftyContinuousMap.logMaxDiv f δ x = Real.log (max ‖f x‖ δ / δ)` is
continuous, nonnegative, and compactly supported, and satisfies
`Real.log δ + logMaxDiv f δ x = Real.log (max ‖f x‖ δ)`.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {α E : Type*} [TopologicalSpace α] [SeminormedAddCommGroup E]

/-- The clipped logarithmic envelope `x ↦ Real.log (max ‖f x‖ δ / δ)` of `f : C₀(α, E)` above
threshold `δ > 0`. It is continuous, nonnegative, and compactly supported. -/
noncomputable def logMaxDiv (f : C₀(α, E)) (δ : ℝ) (x : α) : ℝ :=
  Real.log (max ‖f x‖ δ / δ)

/-- For `δ > 0`, `logMaxDiv f δ` is continuous. -/
@[fun_prop]
theorem continuous_logMaxDiv (f : C₀(α, E)) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (logMaxDiv f δ) :=
  Continuous.log (((map_continuous f).norm.max continuous_const).div_const δ) fun _ ↦
    (div_pos (hδ.trans_le (le_max_right _ _)) hδ).ne'

/-- For `δ > 0`, `logMaxDiv f δ` has compact support because `‖f x‖ < δ` outside a compact set. -/
theorem hasCompactSupport_logMaxDiv [R1Space α] (f : C₀(α, E)) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (logMaxDiv f δ) := by
  obtain ⟨K, hK, hKsub⟩ := Filter.mem_cocompact.1
    ((tendsto_zero_iff_norm_tendsto_zero.1 (zero_at_infty f)).eventually
      (Metric.ball_mem_nhds 0 hδ))
  refine HasCompactSupport.of_support_subset_isCompact hK fun x hx ↦ ?_
  by_contra hxK
  have hlt : ‖f x‖ < δ := by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hKsub hxK
  exact hx (by simp [logMaxDiv, max_eq_right hlt.le, div_self hδ.ne'])

/-- For `δ > 0`, `logMaxDiv f δ` is everywhere nonnegative. -/
theorem logMaxDiv_nonneg (f : C₀(α, E)) {δ : ℝ} (hδ : 0 < δ) (x : α) :
    0 ≤ logMaxDiv f δ x :=
  Real.log_nonneg ((one_le_div hδ).2 (le_max_right _ _))

/-- Splitting `Real.log (max ‖f x‖ δ)` into `Real.log δ + logMaxDiv f δ x`. -/
theorem log_add_logMaxDiv (f : C₀(α, E)) {δ : ℝ} (hδ : 0 < δ) (x : α) :
    Real.log δ + logMaxDiv f δ x = Real.log (max ‖f x‖ δ) := by
  rw [logMaxDiv, Real.log_div (hδ.trans_le (le_max_right _ _)).ne' hδ.ne']
  ring

end ZeroAtInftyContinuousMap
