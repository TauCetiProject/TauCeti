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
continuous and nonnegative, and when `[R1Space α]` holds it has compact support
(`ZeroAtInftyContinuousMap.hasCompactSupport_logMaxDiv`), and satisfies
`Real.log δ + logMaxDiv f δ x = Real.log (max ‖f x‖ δ)`.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {α E : Type*} [TopologicalSpace α] [SeminormedAddCommGroup E]

/-- The clipped logarithmic envelope `x ↦ Real.log (max ‖f x‖ δ / δ)` of `f : C₀(α, E)` above
threshold `δ > 0`. It is continuous and nonnegative, and compactly supported when `[R1Space α]`
holds (`ZeroAtInftyContinuousMap.hasCompactSupport_logMaxDiv`). -/
noncomputable def logMaxDiv (f : C₀(α, E)) (δ : ℝ) (x : α) : ℝ :=
  Real.log (max ‖f x‖ δ / δ)

/-- Defining formula for `logMaxDiv`. -/
theorem logMaxDiv_def (f : C₀(α, E)) (δ : ℝ) (x : α) :
    logMaxDiv f δ x = Real.log (max ‖f x‖ δ / δ) :=
  (rfl)

/-- For `δ > 0`, `logMaxDiv f δ x = 0` exactly when `‖f x‖ ≤ δ`. -/
@[simp]
theorem logMaxDiv_eq_zero_iff (f : C₀(α, E)) {δ : ℝ} (hδ : 0 < δ) (x : α) :
    logMaxDiv f δ x = 0 ↔ ‖f x‖ ≤ δ := by
  have hpos : 0 < max ‖f x‖ δ / δ := div_pos (hδ.trans_le (le_max_right _ _)) hδ
  rw [logMaxDiv_def, Real.log_eq_zero]
  simp [hpos.ne', (by linarith : max ‖f x‖ δ / δ ≠ -1), div_eq_one_iff_eq hδ.ne']

/-- For `δ > 0`, `logMaxDiv f δ` is continuous. -/
@[fun_prop]
theorem continuous_logMaxDiv (f : C₀(α, E)) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (logMaxDiv f δ) :=
  Continuous.log (((map_continuous f).norm.max continuous_const).div_const δ) fun _ ↦
    (div_pos (hδ.trans_le (le_max_right _ _)) hδ).ne'

/-- For `δ > 0` and `[R1Space α]`, `logMaxDiv f δ` has compact support because `‖f x‖ < δ` outside
a compact set. -/
theorem hasCompactSupport_logMaxDiv [R1Space α] (f : C₀(α, E)) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (logMaxDiv f δ) := by
  obtain ⟨K, hK, hKlt⟩ := f.exists_isCompact_norm_lt hδ
  refine HasCompactSupport.of_support_subset_isCompact hK fun x hx ↦ ?_
  by_contra hxK
  exact hx ((logMaxDiv_eq_zero_iff f hδ x).2 (hKlt x hxK).le)

/-- For `δ > 0`, `logMaxDiv f δ` is everywhere nonnegative. -/
theorem logMaxDiv_nonneg (f : C₀(α, E)) {δ : ℝ} (hδ : 0 < δ) (x : α) :
    0 ≤ logMaxDiv f δ x :=
  Real.log_nonneg ((one_le_div hδ).2 (le_max_right _ _))

/-- Splitting `Real.log (max ‖f x‖ δ)` into `Real.log δ + logMaxDiv f δ x`. -/
theorem log_add_logMaxDiv (f : C₀(α, E)) {δ : ℝ} (hδ : 0 < δ) (x : α) :
    Real.log δ + logMaxDiv f δ x = Real.log (max ‖f x‖ δ) := by
  rw [logMaxDiv_def, Real.log_div (hδ.trans_le (le_max_right _ _)).ne' hδ.ne']
  ring

end ZeroAtInftyContinuousMap
