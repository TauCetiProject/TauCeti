/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.RealDeriv
public import TauCeti.Analysis.Complex.Determinant
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Complex.Coordinates

/-!
# Real derivatives of complex differentiable maps

The real derivative of a map `f : ℂ → ℂ` complex differentiable at `z` is multiplication by the
complex derivative, `fderiv ℝ f z w = w • deriv f z`
(`DifferentiableAt.fderiv_restrictScalars_eq_smul_deriv`), so its determinant is
`‖deriv f z‖ ^ 2` (`DifferentiableAt.det_complexToReal_fderiv`). For `deriv f z = a + b i`, a
real-linear map `D` precomposed with it satisfies the Cauchy–Riemann combination identity
`D (f' 1) + A D (f' i) = a (D 1 + A D i) + b (D i - A D 1)`
(`DifferentiableAt.comp_fderiv_apply_one_add_apply_I`).

Complex conjugation is real differentiable (Mathlib's `Complex.differentiable_conj`), but its real
derivative `conjCLE` is not complex linear: it sends `1` to `1` and `I` to `-I`. Hence conjugation,
and the reflection `z ↦ -conj z` across the imaginary axis, are complex differentiable at no point.
The real derivative is computed by `Complex.fderiv_conj` and `Complex.fderiv_conj_apply`.
-/

public section

open scoped ComplexConjugate

namespace DifferentiableAt

variable {f : ℂ → ℂ} {z : ℂ}

/-- **The Jacobian of a complex differentiable map.** The real derivative of a map complex
differentiable at `z` has determinant `‖deriv f z‖ ^ 2`. -/
theorem det_complexToReal_fderiv (hf : DifferentiableAt ℂ f z) :
    (fderiv ℝ f z).det = ‖deriv f z‖ ^ 2 := by
  rw [hf.fderiv_restrictScalars ℝ, hf.hasDerivAt.hasFDerivAt.fderiv,
    ← ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    ContinuousLinearMap.det_restrictScalars_smulRight_one]

/-- **The Cauchy–Riemann combination along a complex derivative.** For `f` complex differentiable
at `z` with `deriv f z = a + b i`, a real-linear map `D` precomposed with the real derivative of
`f` satisfies `D (f' 1) + A D (f' i) = a (D 1 + A D i) + b (D i - A D 1)`. -/
theorem comp_fderiv_apply_one_add_apply_I {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] (hf : DifferentiableAt ℂ f z) (D : ℂ →L[ℝ] F) (A : F →L[ℝ] F) :
    (D ∘L fderiv ℝ f z) 1 + A ((D ∘L fderiv ℝ f z) Complex.I) =
      (deriv f z).re • (D 1 + A (D Complex.I)) + (deriv f z).im • (D Complex.I - A (D 1)) := by
  rw [← ContinuousLinearMap.apply_mul_one_add_apply_mul_I]
  simp [hf.fderiv_restrictScalars_eq_smul_deriv ℝ, mul_comm]

end DifferentiableAt

namespace Complex

/-- The real derivative of conjugation at any point is the real-linear map `conjCLE`. -/
@[simp]
theorem fderiv_conj (z : ℂ) : fderiv ℝ conj z = (conjCLE : ℂ →L[ℝ] ℂ) := by
  have hconj : (conj : ℂ → ℂ) = conjCLE := funext fun x => (conjCLE_apply x).symm
  rw [hconj, conjCLE.fderiv]

/-- Applied form of `Complex.fderiv_conj`: `fderiv ℝ conj z w = conj w`. -/
theorem fderiv_conj_apply (z w : ℂ) : fderiv ℝ conj z w = conj w := by
  rw [fderiv_conj, ContinuousLinearEquiv.coe_coe, conjCLE_apply]

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
