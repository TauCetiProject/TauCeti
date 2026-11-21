/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

import TauCeti.NumberTheory.ExplicitBounds.BigOStar.Integral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Basic

/-!
# Checks for explicit absolute errors

These examples distinguish two-sided absolute errors from one-sided bounds, relative errors,
and bounds that silently replace the displayed error by its absolute value.
-/

open TauCeti

example : BigOStar Real.pi 3 0.1416 := by
  rw [bigOStar_real_iff]
  constructor <;> linarith [Real.pi_gt_d4, Real.pi_lt_d4]

example : ¬ BigOStar Real.pi 3 0.1415 := by
  rw [bigOStar_real_iff]
  rintro ⟨_, h⟩
  linarith [Real.pi_gt_d4]

example : ¬ BigOStar Real.pi 4 0 := by
  rw [bigOStar_zero_iff]
  linarith [Real.pi_lt_d4]

example : ¬ BigOStar (1 : ℝ) 1 (-1) := by simp

example : BigOStar Complex.I 0 1 := by
  simp [bigOStar_iff]

example : BigOStar (1 : ℝ) 0 1 := by
  norm_num [bigOStar_iff]

example : BigOStarOn (fun _ : ℝ ↦ Complex.I) (fun _ ↦ 0) (fun _ ↦ 1) Set.univ := by
  rw [bigOStarOn_iff]
  intro x _
  simp [bigOStar_iff]

example {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f g : α → ℂ} {h : α → ℝ} {s : Set α} (H : BigOStarOn f g h s)
    (hs : MeasurableSet s) (hf : MeasureTheory.IntegrableOn f s μ)
    (hg : MeasureTheory.IntegrableOn g s μ) (hh : MeasureTheory.IntegrableOn h s μ) :
    ‖∫ x in s, f x ∂μ‖ ≤ ‖∫ x in s, g x ∂μ‖ + ∫ x in s, h x ∂μ :=
  (H.integral hs hf hg hh).norm_le
