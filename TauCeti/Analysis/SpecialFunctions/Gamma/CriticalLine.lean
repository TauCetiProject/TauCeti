/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Gamma on the critical line

The reflection formula gives the exact norm of the Gamma function on `re z = 1 / 2`,
and hence an exponential bound valid at every height, including zero.

Adapted from [PNTCriticalLine], the critical-line norm and decay proofs in the
PrimeNumberTheoremAnd project by Robby Sneiderman.

## References

* [PNTCriticalLine](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/8111fab50b1fd6ea52c5e885e9c36571b4374a79/PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/CriticalLineDecay.lean)
-/

public section

namespace Complex

/-- The exact squared norm of the Gamma function on the line `re z = 1 / 2`. -/
theorem norm_Gamma_sq_of_re_eq_one_half {z : ℂ} (hz : z.re = 1 / 2) :
    ‖Gamma z‖ ^ 2 = Real.pi / Real.cosh (Real.pi * z.im) := by
  have hconj : starRingEnd ℂ z = 1 - z := by
    apply Complex.ext <;> simp [hz]; ring
  have harg : (Real.pi : ℂ) * z = Real.pi / 2 + (Real.pi * z.im : ℝ) * I := by
    apply Complex.ext <;> simp [hz]; ring
  have hsin : sin (Real.pi * z) = (Real.cosh (Real.pi * z.im) : ℂ) := by
    rw [harg]
    simp [sin_add, cos_mul_I, ofReal_cosh]
  have h := Gamma_mul_Gamma_one_sub z
  rw [← hconj, Gamma_conj, mul_conj, normSq_eq_norm_sq, hsin] at h
  exact ofReal_injective (by simpa only [ofReal_div] using h)

/-- A sharp exponential decay bound for the Gamma function on `re z = 1 / 2`,
valid at every height. -/
theorem norm_Gamma_le_exp_of_re_eq_one_half {z : ℂ} (hz : z.re = 1 / 2) :
    ‖Gamma z‖ ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |z.im| / 2)) := by
  have hcosh : Real.exp (Real.pi * |z.im|) / 2 ≤ Real.cosh (Real.pi * z.im) := by
    rw [Real.cosh_eq]
    have h := Real.exp_abs_le (Real.pi * z.im)
    rw [abs_mul, abs_of_pos Real.pi_pos] at h
    linarith
  have hsq : (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |z.im| / 2))) ^ 2 =
      2 * Real.pi / Real.exp (Real.pi * |z.im|) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), sq, ← Real.exp_add,
      show -(Real.pi * |z.im| / 2) + -(Real.pi * |z.im| / 2) =
        -(Real.pi * |z.im|) by ring, Real.exp_neg]
    ring
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [norm_Gamma_sq_of_re_eq_one_half hz, hsq]
  calc
    Real.pi / Real.cosh (Real.pi * z.im) ≤
        Real.pi / (Real.exp (Real.pi * |z.im|) / 2) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hcosh
    _ = 2 * Real.pi / Real.exp (Real.pi * |z.im|) := by ring

end Complex
