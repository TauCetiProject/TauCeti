/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.HermiteBiehler.Basic
public import TauCeti.Examples.Analysis.ODE.DiracSystem.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Check: the reflection in the equation of `E`, for a purely imaginary constant potential

For the constant potential `q = ic` with `c` real, at the spectral parameter `z = 0`, the
fundamental matrix of the Dirac system is
`M(t, 0) = [[cosh ct, -sinh ct], [-sinh ct, cosh ct]]`
(`TauCeti.Examples.DiracSystem.diracFundamentalMatrix_I_mul_const_zero`), so
the Hermite–Biehler function is `E(t, 0) = A - iC = cosh ct + i sinh ct`
(`diracHermiteBiehler_I_mul_const_zero`).

It solves `E(t, 0) = 1 + ∫₀ᵗ q E#(s, 0) ds`, where at `z = 0` the reflection is
`E#(s, 0) = conj E(s, 0) = A + iC` (`diracHermiteBiehler_I_mul_const_zero_eq_one_add_integral`).
The reflection is needed: the equation `∂ₜE = -izE + qE` without `#` is solved at `z = 0` by
`e^{ict}` (`exp_I_mul_eq_one_add_integral`), which is not `E(t, 0)` for `ct ≠ 0`
(`diracHermiteBiehler_I_mul_const_zero_ne_exp`: `|e^{ict}| = 1` while
`|cosh ct + i sinh ct|² = cosh² ct + sinh² ct > 1`), and `E(·, 0)` does not solve it for `c ≠ 0`
(`not_forall_diracHermiteBiehler_I_mul_const_zero_eq_one_add_integral`).

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
-/

public section

open MeasureTheory Set Matrix Complex intervalIntegral ComplexConjugate

namespace TauCeti.Examples.DiracSystem

/-- **`E` for `q = ic` at `z = 0`.** `E(t, 0) = cosh ct + i sinh ct`. -/
theorem diracHermiteBiehler_I_mul_const_zero (c t : ℝ) :
    diracHermiteBiehler (fun _ ↦ I * c) t 0 = Real.cosh (c * t) + I * Real.sinh (c * t) := by
  simp [diracHermiteBiehler_def, diracFundamentalMatrix_I_mul_const_zero]

/-- At `z = 0` the reflection `E#(t, 0) = conj E(t, 0)` is the second factor `A + iC` of the
integral equation of `E`. -/
theorem conj_diracHermiteBiehler_I_mul_const_zero (c t : ℝ) :
    conj (diracHermiteBiehler (fun _ ↦ I * c) t 0) =
      diracFundamentalMatrix (fun _ ↦ I * c) t 0 0 0 +
        I * diracFundamentalMatrix (fun _ ↦ I * c) t 0 1 0 := by
  simp [diracHermiteBiehler_I_mul_const_zero, diracFundamentalMatrix_I_mul_const_zero,
    -ofReal_cosh, -ofReal_sinh]

/-- **The equation with the reflection.** `E(t, 0) = 1 + ∫₀ᵗ ic conj E(s, 0) ds`, the equation
`∂ₜE = -izE + qE#` at `z = 0`. -/
theorem diracHermiteBiehler_I_mul_const_zero_eq_one_add_integral (c t : ℝ) :
    diracHermiteBiehler (fun _ ↦ I * c) t 0 =
      1 + ∫ s in (0 : ℝ)..t, I * c * conj (diracHermiteBiehler (fun _ ↦ I * c) s 0) := by
  rw [diracHermiteBiehler_eq_one_add_integral (continuousOn_const.integrableOn_uIcc) 0]
  congr 1
  refine integral_congr fun s _ ↦ ?_
  simp only [mul_zero, zero_mul, zero_add, conj_diracHermiteBiehler_I_mul_const_zero]

/-- **The equation without the reflection.** `y(t) = e^{ict}` solves `y(t) = 1 + ∫₀ᵗ ic y(s) ds`,
the equation `∂ₜE = -izE + qE` at `z = 0`. -/
theorem exp_I_mul_eq_one_add_integral (c t : ℝ) :
    exp (I * c * t) = 1 + ∫ s in (0 : ℝ)..t, I * c * exp (I * c * s) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hIc : I * (c : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hc)
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hIc, mul_div_cancel₀ _ hIc]
  simp

/-- **The two equations differ.** For `ct ≠ 0`, `E(t, 0) = cosh ct + i sinh ct` is not
`e^{ict}`. -/
theorem diracHermiteBiehler_I_mul_const_zero_ne_exp {c t : ℝ} (hct : c * t ≠ 0) :
    diracHermiteBiehler (fun _ ↦ I * c) t 0 ≠ exp (I * c * t) := by
  intro h
  have h1 : ‖exp (I * c * t)‖ = 1 := by
    rw [show I * (c : ℂ) * t = ((c * t : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]
  have h2 : normSq (diracHermiteBiehler (fun _ ↦ I * c) t 0) =
      Real.cosh (c * t) ^ 2 + Real.sinh (c * t) ^ 2 := by
    rw [diracHermiteBiehler_I_mul_const_zero, mul_comm I, normSq_add_mul_I]
  have hsinh : Real.sinh (c * t) ≠ 0 := Real.sinh_ne_zero.mpr hct
  rw [h, normSq_eq_norm_sq, h1, Real.cosh_sq] at h2
  nlinarith [sq_pos_of_ne_zero hsinh]

/-- **`E` does not solve the equation without the reflection.** For `c ≠ 0`, `E(·, 0)` does not
satisfy `E(t, 0) = 1 + ∫₀ᵗ ic E(s, 0) ds` for every `t`. -/
theorem not_forall_diracHermiteBiehler_I_mul_const_zero_eq_one_add_integral {c : ℝ} (hc : c ≠ 0) :
    ¬ ∀ t : ℝ, diracHermiteBiehler (fun _ ↦ I * c) t 0 =
      1 + ∫ s in (0 : ℝ)..t, I * c * diracHermiteBiehler (fun _ ↦ I * c) s 0 := by
  -- Comparing derivatives at `t = 1` would give `c sinh c + ic cosh c = ic cosh c - c sinh c`.
  intro h
  set E : ℝ → ℂ := fun t ↦ diracHermiteBiehler (fun _ ↦ I * c) t 0
  have hEf : E = fun t ↦ (Real.cosh (c * t) : ℂ) + I * Real.sinh (c * t) := by
    funext t; exact diracHermiteBiehler_I_mul_const_zero c t
  have hcont : Continuous fun s ↦ I * c * E s := by rw [hEf]; fun_prop
  -- derivative of the right side: `ic E(1)`
  have hR : HasDerivAt (fun t ↦ 1 + ∫ s in (0 : ℝ)..t, I * c * E s) (I * c * E 1) 1 :=
    (integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).const_add 1
  -- derivative of the left side: `c sinh c + ic cosh c`
  have hL : HasDerivAt E ((c * Real.sinh c : ℝ) + I * (c * Real.cosh c : ℝ)) 1 := by
    rw [hEf]
    have hlin : HasDerivAt (fun t : ℝ ↦ c * t) c 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).const_mul c
    have hcosh := ((Real.hasDerivAt_cosh (c * 1)).comp 1 hlin).ofReal_comp
    have hsinh := ((Real.hasDerivAt_sinh (c * 1)).comp 1 hlin).ofReal_comp
    convert hcosh.add (hsinh.const_mul I) using 1
    · ext t
      simp
    · simp only [mul_one]
      push_cast
      ring
  have heq := hL.unique (hR.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ h t))
  rw [hEf] at heq
  have hre : c * Real.sinh c = -(c * Real.sinh c) := by
    simpa [-ofReal_cosh, -ofReal_sinh] using congrArg re heq
  have hs : Real.sinh c ≠ 0 := Real.sinh_ne_zero.mpr hc
  have : c * Real.sinh c = 0 := by linarith
  exact (mul_ne_zero hc hs) this

end TauCeti.Examples.DiracSystem
