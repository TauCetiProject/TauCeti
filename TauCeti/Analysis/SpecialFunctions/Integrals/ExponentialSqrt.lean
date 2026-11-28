/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponential tails with a square-root exponent

The tail of `exp (-c √v)` is an exponential times a linear factor in `√v`.
With `v = log t`, this evaluates the tail of a majorant for the error term in the classical
prime number theorem.
-/

public section

open Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti

/-- The tail of the square-root exponential at a nonnegative cutoff. -/
theorem integral_Ioi_exp_neg_mul_sqrt {c V : ℝ} (hc : 0 < c) (hV : 0 ≤ V) :
    (∫ v in Ioi V, exp (-c * √v)) = 2 / c ^ 2 * (1 + c * √V) * exp (-c * √V) := by
  have hsub := integral_comp_rpow_Ioi_of_pos' (p := 2) (g := fun v ↦ exp (-c * √v))
    two_pos hV
  norm_num [← sqrt_eq_rpow, rpow_two, sqrt_sq_eq_abs, smul_eq_mul] at hsub
  have hsub' : (∫ u in Ioi (√V), 2 * u * exp (-c * u)) = ∫ v in Ioi V, exp (-c * √v) := by
    refine Eq.trans (b := ∫ u in Ioi (√V), 2 * u * exp (-(c * |u|))) ?_ ?_
    · exact setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ by
        rw [abs_of_nonneg ((sqrt_nonneg V).trans hu.le), neg_mul]
    · simpa only [neg_mul] using hsub
  rw [← hsub']
  let F (u : ℝ) := -(2 / c ^ 2) * (1 + c * u) * exp (-c * u)
  have hd (u : ℝ) (_hu : u ∈ Ici (√V)) : HasDerivAt F (2 * u * exp (-c * u)) u := by
    convert (((hasDerivAt_id u).const_mul c).const_add 1 |>.const_mul (-(2 / c ^ 2))).mul
      (((hasDerivAt_id u).const_mul (-c)).exp) using 1
    · rfl
    · simp only [id_eq]
      field_simp
      ring
  have ht : Tendsto F atTop (𝓝 0) := by
    have h₁ : Tendsto (fun u : ℝ ↦ exp (-c * u)) atTop (𝓝 0) := by
      simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc
    have h₂ : Tendsto (fun u : ℝ ↦ u * exp (-c * u)) atTop (𝓝 0) := by
      simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
    simpa only [mul_add, add_mul, one_mul, mul_assoc, mul_zero, add_zero, F] using
      (h₁.add (h₂.const_mul c)).const_mul (-(2 / c ^ 2))
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun u hu ↦ by
    have := (sqrt_nonneg V).trans hu.le
    positivity) ht]
  simp [F]

end TauCeti
