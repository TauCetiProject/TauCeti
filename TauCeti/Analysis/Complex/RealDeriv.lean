/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.RealDeriv
public import TauCeti.Analysis.Complex.Determinant

/-!
# Real derivatives of complex differentiable maps

The real derivative of a map `f : ℂ → ℂ` complex differentiable at `z` is multiplication by the
complex derivative, `fderiv ℝ f z w = deriv f z * w`
(`DifferentiableAt.complexToReal_fderiv_apply`), so its determinant is `‖deriv f z‖ ^ 2`
(`DifferentiableAt.det_complexToReal_fderiv`).

Complex conjugation is real differentiable (Mathlib's `Complex.differentiable_conj`), but its real
derivative `conjCLE` is not complex linear: it sends `1` to `1` and `I` to `-I`. Hence conjugation,
and the reflection `z ↦ -conj z` across the imaginary axis, are complex differentiable at no point.
-/

public section

open scoped ComplexConjugate

namespace DifferentiableAt

variable {f : ℂ → ℂ} {z : ℂ}

/-- The real derivative of a map complex differentiable at `z` is multiplication by its complex
derivative. -/
theorem complexToReal_fderiv_apply (hf : DifferentiableAt ℂ f z) (w : ℂ) :
    fderiv ℝ f z w = deriv f z * w := by
  rw [hf.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars',
    hf.hasDerivAt.hasFDerivAt.fderiv]
  simp [mul_comm]

/-- **The Jacobian of a complex differentiable map.** The real derivative of a map complex
differentiable at `z` has determinant `‖deriv f z‖ ^ 2`. -/
theorem det_complexToReal_fderiv (hf : DifferentiableAt ℂ f z) :
    (fderiv ℝ f z).det = ‖deriv f z‖ ^ 2 := by
  rw [hf.fderiv_restrictScalars ℝ, hf.hasDerivAt.hasFDerivAt.fderiv,
    ← ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    ContinuousLinearMap.det_restrictScalars_smulRight_one]

end DifferentiableAt

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
