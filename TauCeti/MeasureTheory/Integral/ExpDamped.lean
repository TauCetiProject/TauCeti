/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Vanishing exponential damping of a half-line integral

Damping an integrand on the half-line `u ≥ -log x` by `exp (-u (sigma - 1))` and normalizing by
`x ^ (1 - sigma)`, the reciprocal of the damping at the left endpoint, leaves the integral of
an integrable function unchanged in the limit `sigma → 1⁺`: the damping factor is bounded on
the half-line uniformly in `sigma ∈ (1, 2]`, so dominated convergence applies.

This is the Abelian step of a Tauberian argument, where a Dirichlet series is tested on a vertical
line `Re s = sigma` inside its half-plane of convergence and the line is pushed to the boundary;
`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary` uses it for the simple-pole
term of the Wiener--Ikehara identity.

## Main results

* `TauCeti.tendsto_integral_exp_mul`: the normalized damped integral converges to the undamped
  one as `sigma` decreases to `1`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped Topology

variable {f : ℝ → ℂ} {x : ℝ}

/-- On the half-line `u ≥ -log x` the damping factor `exp (-u (sigma - 1))` stays below a bound
depending only on `x`, uniformly for `sigma ∈ (1, 2]`. -/
private lemma exp_neg_mul_sub_one_le {u sigma : ℝ} (hu : -Real.log x ≤ u) (h1 : 1 < sigma)
    (h2 : sigma ≤ 2) : Real.exp (-u * (sigma - 1)) ≤ Real.exp (max 0 (Real.log x)) := by
  refine Real.exp_le_exp.mpr ?_
  have hu' : -u ≤ Real.log x := by linarith
  rcases le_or_gt (-u) 0 with h | h
  · have hle : -u * (sigma - 1) ≤ 0 := by nlinarith
    exact hle.trans (le_max_left _ _)
  · have hle : -u * (sigma - 1) ≤ -u := by nlinarith
    exact hle.trans (hu'.trans (le_max_right _ _))

/-- As `sigma` decreases to `1`, the normalized one-sided Laplace transform of a function
integrable on the half-line `u ≥ -log x` converges to its undamped integral. -/
theorem tendsto_integral_exp_mul (hx : 0 < x) (hf : IntegrableOn f (Ici (-Real.log x))) :
    Tendsto (fun sigma : ℝ ↦ ((x ^ (1 - sigma) : ℝ) : ℂ) *
        ∫ u in Ici (-Real.log x), (Real.exp (-u * (sigma - 1)) : ℂ) * f u)
      (𝓝[>] 1) (𝓝 (∫ u in Ici (-Real.log x), f u)) := by
  have hrpow : Tendsto (fun sigma : ℝ ↦ ((x ^ (1 - sigma) : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 1) := by
    have hcont : Continuous fun sigma : ℝ ↦ ((x ^ (1 - sigma) : ℝ) : ℂ) := by
      simp only [Real.rpow_def_of_pos hx]
      fun_prop
    simpa using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hint : Tendsto (fun sigma : ℝ ↦ ∫ u in Ici (-Real.log x),
      (Real.exp (-u * (sigma - 1)) : ℂ) * f u) (𝓝[>] 1)
      (𝓝 (∫ u in Ici (-Real.log x), f u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u ↦ Real.exp (max 0 (Real.log x)) * ‖f u‖)
      (.of_forall fun sigma ↦ (Continuous.aestronglyMeasurable (by fun_prop)).mul hf.1) ?_
      (hf.norm.const_mul _) (.of_forall fun u ↦ ?_)
    · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with sigma hsigma
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (exp_neg_mul_sub_one_le hu hsigma.1 hsigma.2)
        (norm_nonneg _)
    · have hone : Tendsto (fun sigma : ℝ ↦ ((Real.exp (-u * (sigma - 1)) : ℝ) : ℂ)) (𝓝[>] 1)
          (𝓝 1) := by
        have hcont : Continuous fun sigma : ℝ ↦ ((Real.exp (-u * (sigma - 1)) : ℝ) : ℂ) := by
          fun_prop
        simpa using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
      simpa using hone.mul_const (f u)
  simpa using hrpow.mul hint

end TauCeti
