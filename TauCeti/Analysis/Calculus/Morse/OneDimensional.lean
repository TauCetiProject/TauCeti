/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Nondegenerate critical points of functions of one real variable

A function `f : ℝ → ℝ` is a function on the one-dimensional real inner product space `ℝ`, so the
general Morse-theoretic notions apply to it. This file reads them off the first and second
derivatives of `f`. The Hessian operator of `f` at `t` is multiplication by `f''(t)`
(`TauCeti.hessianOperator_real`); `t` is a nondegenerate critical point exactly when `f'(t) = 0`
and `f''(t) ≠ 0` (`TauCeti.isNondegenerateCriticalPoint_real_iff`); and the Morse index there is
`1` when `f''(t) < 0` and `0` when `0 < f''(t)`.

These are the facts needed to apply the theory of linearized trajectory operators, which is stated
on finite-dimensional inner product spaces, to the negative-gradient flow of an explicit function
of one variable.

## Main declarations

* `TauCeti.hessianOperator_real`: the Hessian operator is multiplication by `f''(t)`.
* `TauCeti.isNondegenerateCriticalPoint_real_iff`: nondegenerate critical points of a function of
  one variable.
* `TauCeti.IsNondegenerateCriticalPoint.morseIndex_real_of_neg` and
  `TauCeti.IsNondegenerateCriticalPoint.morseIndex_real_of_pos`: the Morse index is `1` at a local
  maximum and `0` at a local minimum.
-/

public section

namespace TauCeti

variable {f : ℝ → ℝ} {t : ℝ}

/-- The Hessian operator of a function of one real variable is multiplication by its second
derivative. -/
theorem hessianOperator_real (f : ℝ → ℝ) (t : ℝ) :
    hessianOperator f t = iteratedDeriv 2 f t • ContinuousLinearMap.id ℝ ℝ := by
  refine ContinuousLinearMap.ext_ring ?_
  have h := inner_hessianOperator_left f t 1 1
  rw [fderiv_fderiv_apply_eq_smul_iteratedDeriv] at h
  simpa using h

/-- The Hessian quadratic form of a function of one real variable is `v ↦ f''(t) v²`. -/
theorem hessianQuadraticForm_real_apply (f : ℝ → ℝ) (t v : ℝ) :
    hessianQuadraticForm f t v = iteratedDeriv 2 f t * v ^ 2 := by
  rw [hessianQuadraticForm_apply, fderiv_fderiv_apply_eq_smul_iteratedDeriv, smul_eq_mul]
  ring

/-- **Nondegenerate critical points of a function of one variable.** A point at which `f` is
twice continuously differentiable is a nondegenerate critical point exactly when the first
derivative vanishes there and the second does not. -/
theorem isNondegenerateCriticalPoint_real_iff (hf : ContDiffAt ℝ 2 f t) :
    IsNondegenerateCriticalPoint f t ↔ deriv f t = 0 ∧ iteratedDeriv 2 f t ≠ 0 := by
  have h0 : ContinuousLinearMap.toSpanSingleton ℝ (deriv f t) = 0 ↔ deriv f t = 0 :=
    ⟨fun h ↦ by simpa using congrArg (· 1) h, fun h ↦ by simp [h]⟩
  rw [isNondegenerateCriticalPoint_iff_separatingLeft, ← toSpanSingleton_deriv, h0]
  simp only [hf, true_and]
  refine and_congr_right fun _ ↦ ⟨fun h h0 ↦ one_ne_zero (h 1 fun w ↦ ?_), fun h v hv ↦ ?_⟩
  · rw [ContinuousLinearMap.toBilinForm_apply, fderiv_fderiv_apply_eq_smul_iteratedDeriv, h0,
      smul_zero]
  · have := hv 1
    simp only [ContinuousLinearMap.toBilinForm_apply, fderiv_fderiv_apply_eq_smul_iteratedDeriv,
      smul_eq_mul, mul_one] at this
    exact (mul_eq_zero.1 this).resolve_right h

/-- At a nondegenerate critical point with negative second derivative, a local maximum, the Morse
index of a function of one variable is `1`. -/
theorem IsNondegenerateCriticalPoint.morseIndex_real_of_neg (h : IsNondegenerateCriticalPoint f t)
    (hneg : iteratedDeriv 2 f t < 0) : morseIndex f t = 1 := by
  have := (h.neg_hessianQuadraticForm_posDef_iff_morseIndex_eq_finrank).1 fun v hv ↦ by
    rw [neg_apply, hessianQuadraticForm_real_apply]
    nlinarith [pow_pos (abs_pos.2 hv) 2, sq_abs v]
  simpa using this

/-- At a nondegenerate critical point with positive second derivative, a local minimum, the Morse
index of a function of one variable is `0`. -/
theorem IsNondegenerateCriticalPoint.morseIndex_real_of_pos (h : IsNondegenerateCriticalPoint f t)
    (hpos : 0 < iteratedDeriv 2 f t) : morseIndex f t = 0 :=
  h.hessianQuadraticForm_posDef_iff_morseIndex_eq_zero.1 fun v hv ↦ by
    rw [hessianQuadraticForm_real_apply]
    nlinarith [pow_pos (abs_pos.2 hv) 2, sq_abs v]

end TauCeti

end
