/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.PaleyWiener

/-!
# Checks for Paley–Wiener functions

* *The indicator density.* For `φ = 1_{[-t, t]}` the Paley–Wiener function is `2 sin(tz)/z`
  (`TauCeti.paleyWienerFunction_one`), and Plancherel's identity
  `‖F‖²_{L²(ℝ)} = 2π ‖φ‖²_{L²(-t, t)} = 2π · 2t` becomes the classical integral
  `∫_ℝ (sin(tx)/x)² dx = πt` (`integral_sin_mul_div_sq`).
* *The trivial interval.* `PW_0 = {0}` (`TauCeti.paleyWienerFunction_zero_left`).
* *The kernel on the real line.* For real `λ` the reproducing kernel at `λ` is
  `k_t(λ, λ) = t/π` (`paleyWienerKernel_ofReal_self`), so `‖k_t(λ, ·)‖²_{L²(ℝ)} = t/π`
  (`integral_norm_paleyWienerKernel_ofReal_sq`).
-/

public section

open MeasureTheory Complex
open scoped ComplexConjugate Real

namespace TauCeti.Examples.PaleyWiener

/-- **The indicator density.** Plancherel's identity for the Paley–Wiener function `2 sin(tz)/z`
of `φ = 1_{[-t, t]}` gives `∫_ℝ (sin(tx)/x)² dx = πt`. -/
theorem integral_sin_mul_div_sq {t : ℝ} (ht : 0 ≤ t) :
    ∫ x : ℝ, (Real.sin (t * x) / x) ^ 2 = π * t := by
  have h := integral_norm_paleyWienerFunction_sq ht (φ := 1) (memLp_const 1)
  simp only [Pi.one_apply, norm_one, one_pow, intervalIntegral.integral_const, sub_neg_eq_add,
    smul_eq_mul, mul_one] at h
  have hae : (fun x : ℝ ↦ ‖paleyWienerFunction t 1 x‖ ^ 2) =ᵐ[volume]
      fun x ↦ 4 * (Real.sin (t * x) / x) ^ 2 := by
    filter_upwards [Measure.ae_ne volume 0] with x hx
    rw [paleyWienerFunction_one t (ofReal_ne_zero.2 hx), ← ofReal_mul, ← ofReal_sin,
      ← ofReal_ofNat, ← ofReal_mul, ← ofReal_div, norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [integral_congr_ae hae, integral_const_mul] at h
  linarith

/-- For real `λ` the reproducing kernel of `PW_t` at `λ` is `k_t(λ, λ) = t/π`. -/
theorem paleyWienerKernel_ofReal_self (t x : ℝ) : paleyWienerKernel t x x = t / π := by
  simpa using paleyWienerKernel_conj_self t x

/-- For real `λ` the reproducing kernel `k_t(λ, ·)` of `PW_t` has `‖k_t(λ, ·)‖²_{L²(ℝ)} = t/π`:
the reproducing property applied to the kernel itself. -/
theorem integral_norm_paleyWienerKernel_ofReal_sq {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    ∫ y : ℝ, ‖paleyWienerKernel t x y‖ ^ 2 = t / π := by
  have hψ : MemLp (fun s : ℝ ↦ cexp (I * s * (-conj (x : ℂ))) / (2 * π)) 2
      (volume.restrict (Set.Ioc (-t) t)) := by
    refine MemLp.of_bound (by fun_prop) (1 / (2 * π))
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s _ ↦ ?_)
    rw [norm_div, conj_ofReal, norm_exp]
    simp
  have h := paleyWienerFunction_eq_integral_mul_conj_paleyWienerKernel ht hψ x
  simp_rw [← paleyWienerKernel_def, Complex.mul_conj', ← ofReal_pow] at h
  rw [paleyWienerKernel_ofReal_self, integral_complex_ofReal] at h
  exact_mod_cast h.symm

end TauCeti.Examples.PaleyWiener
