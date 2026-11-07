/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.PoincareLogSobolev
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian

/-!
# Sharpness of the Gaussian logarithmic Sobolev constant

For the standard Gaussian and `f x = exp (a * x / 2)`, this file computes both the entropy
of `f²` and twice its gradient energy. Both are `(a² / 2) exp (a² / 2)`. Consequently no
logarithmic Sobolev inequality can hold for the standard Gaussian with constant less than `1`.
This is the sharpness check, not a proof of the Gaussian logarithmic Sobolev inequality.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ContDiff

namespace TauCeti.Probability

private theorem gaussian_exp_integral (a : ℝ) :
    ∫ x : ℝ, exp (a * x) ∂gaussianReal 0 1 = exp (a ^ 2 / 2) := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) a
  simpa [mgf] using h

private theorem gaussian_x_exp_integral (a : ℝ) :
    ∫ x : ℝ, x * exp (a * x) ∂gaussianReal 0 1 = a * exp (a ^ 2 / 2) := by
  have ha : a ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by
    simp
  have h := deriv_mgf ha
  rw [mgf_fun_id_gaussianReal] at h
  have hd : HasDerivAt (fun t : ℝ => exp (0 * t + (1 : ℝ≥0) * t ^ 2 / 2))
      (a * exp (a ^ 2 / 2)) a := by
    convert ((hasDerivAt_id a).pow 2 |>.div_const 2).exp using 1 <;> simp; ring
  rw [hd.deriv] at h
  exact h.symm

private theorem gaussian_x_exp_integrable (a : ℝ) :
    Integrable (fun x : ℝ => x * exp (a * x)) (gaussianReal 0 1) := by
  have ha : a ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by
    simp
  simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet ha 1

private theorem exp_half_sq (a x : ℝ) : exp (a * x / 2) ^ 2 = exp (a * x) := by
  rw [pow_two, ← exp_add]
  congr 1
  ring

/-- The entropy of the squared exponential test under the standard Gaussian. -/
theorem entropy_exp_half_sq_gaussianReal (a : ℝ) :
    (gaussianReal 0 1).entropy (fun x => exp (a * x / 2) ^ 2) =
      (a ^ 2 / 2) * exp (a ^ 2 / 2) := by
  simp_rw [exp_half_sq]
  rw [Measure.entropy_def, gaussian_exp_integral, Real.log_exp]
  have hint : (∫ x : ℝ, exp (a * x) * log (exp (a * x)) ∂gaussianReal 0 1) =
      a * ∫ x : ℝ, x * exp (a * x) ∂gaussianReal 0 1 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.log_exp]
    ring
  rw [hint, gaussian_x_exp_integral]
  ring

private theorem deriv_exp_half (a x : ℝ) :
    deriv (fun y : ℝ => exp (a * y / 2)) x = (a / 2) * exp (a * x / 2) := by
  have h : HasDerivAt (fun y : ℝ => exp ((a / 2) * y))
      ((a / 2) * exp ((a / 2) * x)) x := by
    simpa [mul_comm] using ((hasDerivAt_id x).const_mul (a / 2)).exp
  have hfun : (fun y : ℝ => exp (a * y / 2)) = fun y => exp ((a / 2) * y) := by
    funext y
    congr 1
    ring
  rw [hfun]
  convert h.deriv using 1
  congr 2
  ring

private theorem norm_fderiv_exp_half (a x : ℝ) :
    ‖fderiv ℝ (fun y : ℝ => exp (a * y / 2)) x‖ =
      |a / 2| * exp (a * x / 2) := by
  rw [← norm_deriv_eq_norm_fderiv, deriv_exp_half, Real.norm_eq_abs, abs_mul,
    abs_of_pos (exp_pos _)]

/-- The gradient energy of the exponential test under the standard Gaussian. -/
theorem integral_sq_norm_fderiv_exp_half_gaussianReal (a : ℝ) :
    (∫ x : ℝ, ‖fderiv ℝ (fun y : ℝ => exp (a * y / 2)) x‖ ^ 2 ∂gaussianReal 0 1) =
      (a ^ 2 / 4) * exp (a ^ 2 / 2) := by
  have heq : (fun x : ℝ => ‖fderiv ℝ (fun y : ℝ => exp (a * y / 2)) x‖ ^ 2) =
      fun x => (a ^ 2 / 4) * exp (a * x) := by
    funext x
    rw [norm_fderiv_exp_half, mul_pow, sq_abs, exp_half_sq]
    ring
  rw [heq, integral_const_mul, gaussian_exp_integral]

/-- The exponential test attains equality in the logarithmic Sobolev bound at constant `1`. -/
theorem entropy_exp_half_sq_eq_two_energy_gaussianReal (a : ℝ) :
    (gaussianReal 0 1).entropy (fun x => exp (a * x / 2) ^ 2) =
      2 * ∫ x : ℝ, ‖fderiv ℝ (fun y : ℝ => exp (a * y / 2)) x‖ ^ 2 ∂gaussianReal 0 1 := by
  rw [entropy_exp_half_sq_gaussianReal, integral_sq_norm_fderiv_exp_half_gaussianReal]
  ring

/-- Any logarithmic Sobolev constant for the standard Gaussian is at least `1`. -/
theorem one_le_of_logSobolevInequality_gaussianReal {C : ℝ}
    (hC : (gaussianReal 0 1).LogSobolevInequality C) : 1 ≤ C := by
  let f : ℝ → ℝ := fun x => exp (1 * x / 2)
  have hf : ContDiff ℝ ∞ f := by dsimp [f]; fun_prop
  have hsg : HasSubgaussianMGF (fun x : ℝ => x) 1 (gaussianReal 0 1) := by
    refine ⟨integrable_exp_mul_gaussianReal, ?_⟩
    intro t
    simp [mgf_fun_id_gaussianReal]
  have hdf : MemLp (fun x => ‖fderiv ℝ f x‖) 2 (gaussianReal 0 1) := by
    have h : MemLp (fun x : ℝ => |(1 : ℝ) / 2| * exp ((1 / 2) * x)) 2
        (gaussianReal 0 1) := by
      simpa using (hsg.memLp_exp_mul (1 / 2) 2).const_mul |(1 : ℝ) / 2|
    convert h using 1
    funext x
    dsimp [f]
    rw [norm_fderiv_exp_half]
    congr 2
    ring
  have hf2 : Integrable (fun x => f x ^ 2) (gaussianReal 0 1) := by
    simp_rw [f, exp_half_sq]
    exact integrable_exp_mul_gaussianReal 1
  have hf2log : Integrable (fun x => f x ^ 2 * log (f x ^ 2)) (gaussianReal 0 1) := by
    have h := gaussian_x_exp_integrable 1
    convert h using 1
    funext x
    have hsq : exp (x / 2) ^ 2 = exp x := by
      rw [pow_two, ← exp_add]
      congr 1
      ring
    simp only [f, one_mul]
    rw [hsq, log_exp]
    ring
  have h := hC.apply f hf hdf hf2 hf2log
  dsimp [f] at h
  rw [entropy_exp_half_sq_gaussianReal, integral_sq_norm_fderiv_exp_half_gaussianReal] at h
  have hexp : 0 < exp ((1 : ℝ) ^ 2 / 2) := exp_pos _
  nlinarith

/-- No constant smaller than `1` satisfies the standard Gaussian logarithmic Sobolev inequality. -/
theorem not_logSobolevInequality_gaussianReal {C : ℝ} (hC : C < 1) :
    ¬ (gaussianReal 0 1).LogSobolevInequality C := by
  intro h
  exact (not_le_of_gt hC) (one_le_of_logSobolevInequality_gaussianReal h)

end TauCeti.Probability
