/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Complex conjugation is nowhere complex differentiable

Complex conjugation is real differentiable (Mathlib's `Complex.differentiable_conj`), but its real
derivative `conjCLE` is not complex linear: it sends `1` to `1` and `I` to `-I`. Hence conjugation,
and the reflection `z ↦ -conj z` across the imaginary axis, are complex differentiable at no point.
-/

public section

open scoped ComplexConjugate

namespace Complex

/-- Complex conjugation is not complex differentiable at any point. -/
theorem not_differentiableAt_conj (z : ℂ) : ¬ DifferentiableAt ℂ (fun w : ℂ ↦ conj w) z := by
  intro hd
  -- The complex derivative, viewed as a real-linear map, must be the real derivative `conjCLE`.
  have hL := (hd.hasFDerivAt.restrictScalars ℝ).unique conjCLE.hasFDerivAt
  have h1 : fderiv ℂ (fun w : ℂ ↦ conj w) z 1 = 1 := by
    simpa using congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L 1) hL
  have hI : fderiv ℂ (fun w : ℂ ↦ conj w) z I = -I := by
    simpa using congrArg (fun L : ℂ →L[ℝ] ℂ ↦ L I) hL
  have hlin : fderiv ℂ (fun w : ℂ ↦ conj w) z I = I * fderiv ℂ (fun w : ℂ ↦ conj w) z 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [hI, h1, mul_one] at hlin
  have him := congrArg im hlin
  norm_num at him

/-- The reflection `z ↦ -conj z` is not complex differentiable at any point. -/
theorem not_differentiableAt_neg_conj (z : ℂ) :
    ¬ DifferentiableAt ℂ (fun w : ℂ ↦ -conj w) z := fun hd ↦
  not_differentiableAt_conj z (by simpa using hd.neg)

end Complex
