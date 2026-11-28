/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Clipped logarithmic envelopes

For a function `f : α → E` into a normed type and a threshold `δ > 0`, the clipped logarithmic
envelope `TauCeti.logMaxDiv f δ x = Real.log (max ‖f x‖ δ / δ)` is everywhere nonnegative
(`TauCeti.logMaxDiv_nonneg`), satisfies `Real.log δ + logMaxDiv f δ x = Real.log (max ‖f x‖ δ)`
(`TauCeti.log_add_logMaxDiv`), vanishes exactly where `‖f x‖ ≤ δ` (`TauCeti.logMaxDiv_eq_zero_iff`),
and is continuous when `f` is continuous (`TauCeti.continuous_logMaxDiv`).
-/

public section

namespace TauCeti

variable {α E : Type*}

/-- The clipped logarithmic envelope `x ↦ Real.log (max ‖f x‖ δ / δ)` of `f : α → E` above
threshold `δ > 0`. -/
noncomputable def logMaxDiv [Norm E] (f : α → E) (δ : ℝ) (x : α) : ℝ :=
  Real.log (max ‖f x‖ δ / δ)

/-- Defining formula for `TauCeti.logMaxDiv`. -/
theorem logMaxDiv_def [Norm E] (f : α → E) (δ : ℝ) (x : α) :
    logMaxDiv f δ x = Real.log (max ‖f x‖ δ / δ) := (rfl)

/-- For `δ > 0`, `TauCeti.logMaxDiv f δ x = 0` exactly when `‖f x‖ ≤ δ`. -/
@[simp] theorem logMaxDiv_eq_zero_iff [Norm E] (f : α → E) {δ : ℝ} (hδ : 0 < δ) (x : α) :
    logMaxDiv f δ x = 0 ↔ ‖f x‖ ≤ δ := by
  have hpos : 0 < max ‖f x‖ δ / δ := div_pos (hδ.trans_le (le_max_right _ _)) hδ
  rw [logMaxDiv_def, Real.log_eq_zero]
  simp [hpos.ne', (by linarith : max ‖f x‖ δ / δ ≠ -1), div_eq_one_iff_eq hδ.ne']

/-- For `δ > 0`, `TauCeti.logMaxDiv f δ` is continuous whenever `f` is continuous. -/
@[fun_prop]
theorem continuous_logMaxDiv [TopologicalSpace α] [SeminormedAddCommGroup E] {f : α → E}
    (hf : Continuous f) {δ : ℝ} (hδ : 0 < δ) : Continuous (logMaxDiv f δ) :=
  Continuous.log ((hf.norm.max continuous_const).div_const δ) fun _ ↦
    (div_pos (hδ.trans_le (le_max_right _ _)) hδ).ne'

/-- For `δ > 0`, `TauCeti.logMaxDiv f δ` is everywhere nonnegative. -/
theorem logMaxDiv_nonneg [Norm E] (f : α → E) {δ : ℝ} (hδ : 0 < δ) (x : α) :
    0 ≤ logMaxDiv f δ x :=
  Real.log_nonneg ((one_le_div hδ).2 (le_max_right _ _))

/-- Splitting `Real.log (max ‖f x‖ δ)` into `Real.log δ + TauCeti.logMaxDiv f δ x`. -/
theorem log_add_logMaxDiv [Norm E] (f : α → E) {δ : ℝ} (hδ : 0 < δ) (x : α) :
    Real.log δ + logMaxDiv f δ x = Real.log (max ‖f x‖ δ) := by
  rw [logMaxDiv_def, Real.log_div (hδ.trans_le (le_max_right _ _)).ne' hδ.ne']; ring

end TauCeti
