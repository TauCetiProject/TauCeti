/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrals of powers of the positive part

Integrating a positive natural power of `max x 0` increases its degree by one. This formula
also applies when either endpoint is negative, and permits successive integration of
piecewise polynomials expressed using truncated powers.
-/

public section

open MeasureTheory Set

namespace TauCeti.intervalIntegral

open _root_.intervalIntegral

/-- The integral of a positive natural power of the positive part, with arbitrary oriented
endpoints. The positive-exponent hypothesis is needed on the negative half-line. -/
@[simp]
theorem integral_max_zero_pow {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    (∫ x in a..b, max x 0 ^ n) =
      (max b 0 ^ (n + 1) - max a 0 ^ (n + 1)) / (n + 1) := by
  -- Reduce to integrals from `0`, where the integrand is either `x ^ n` or zero.
  have hint (b : ℝ) : IntervalIntegrable (fun x : ℝ ↦ max x 0 ^ n) volume 0 b :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hzero (b : ℝ) : (∫ x in 0..b, max x 0 ^ n) = max b 0 ^ (n + 1) / (n + 1) := by
    rcases le_total 0 b with hb | hb
    · rw [max_eq_left hb, integral_congr_Ioo_of_le hb (g := (· ^ n)) fun x hx ↦ by
        rw [max_eq_left hx.1.le]]
      simp
    · rw [max_eq_right hb, integral_symm, integral_congr_Ioo_of_le hb (g := fun _ ↦ 0)
        fun x hx ↦ by rw [max_eq_right hx.2.le, zero_pow hn.ne']]
      simp
  rw [← integral_interval_sub_left (hint b) (hint a), hzero, hzero, sub_div]

/-- Integrating a reflected, translated positive-part power gives the difference of
the truncated powers at the oriented endpoints. -/
theorem integral_max_sub_zero_pow {n : ℕ} (hn : 0 < n) (c a b : ℝ) :
    (∫ x in a..b, max (c - x) 0 ^ n) =
      (max (c - a) 0 ^ (n + 1) - max (c - b) 0 ^ (n + 1)) / (n + 1) := by
  rw [integral_comp_sub_left (fun x : ℝ ↦ max x 0 ^ n), integral_max_zero_pow hn]

end TauCeti.intervalIntegral
