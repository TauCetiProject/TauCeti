/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic decay at exponentially large arguments

Decay faster than every inverse power of the logarithm becomes power decay at all arguments
whose logarithms are bounded below by a positive power of the reference scale, even with a
fixed additive loss in that lower bound.

Any fixed multiple of a power of `log x` is eventually at most any positive power of `x`
(`TauCeti.eventually_mul_log_pow_le_rpow`), the inequality form of Mathlib's
`isLittleO_log_rpow_rpow_atTop`.
-/

public section

open Filter Real

namespace TauCeti

/-- A fixed multiple of `(log x) ^ k` is eventually at most any positive power of `x`. -/
theorem eventually_mul_log_pow_le_rpow (c : ℝ) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, c * log x ^ k ≤ x ^ δ := by
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hδ).const_mul_left c).bound zero_lt_one]
    with x hx₀ hx
  rw [one_mul, norm_of_nonneg (rpow_nonneg hx₀ δ), rpow_natCast] at hx
  exact (le_norm_self _).trans hx

/-- An inverse-logarithmic power bound with exponent `B` gives an upper bound `x^r` at all
positive arguments `y` with `log y ≥ x^δ - 1`, provided `r ≥ -δ B / 2` and `δ > 0`. -/
theorem eventually_abs_le_rpow_of_log_rpow_decay {f : ℝ → ℝ} {B : ℕ} {δ r : ℝ} (hδ : 0 < δ)
    (hBr : -(δ / 2) * (B : ℝ) ≤ r) (hf : ∀ᶠ y : ℝ in atTop, |f y| ≤ log y ^ (-(B : ℝ))) :
    ∀ᶠ x : ℝ in atTop, ∀ y > 0, x ^ δ - 1 ≤ log y → |f y| ≤ x ^ r := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp hf
  let A' := max A 1
  have hA' : 0 < A' := zero_lt_one.trans_le (le_max_right ..)
  have hp : ∀ᶠ x : ℝ in atTop, log A' + 1 ≤ x ^ δ :=
    (tendsto_rpow_atTop hδ).eventually_ge_atTop _
  have hq : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (δ / 2) :=
    (tendsto_rpow_atTop (by positivity : 0 < δ / 2)).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (1 : ℝ), hp, hq] with x hx hp hq
  intro y hy hxy
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hAy : A' ≤ y := (log_le_log_iff hA' hy).mp (by linarith)
  have hxlog : x ^ (δ / 2) ≤ log y := by
    have he : x ^ δ = (x ^ (δ / 2)) ^ 2 := by
      rw [← rpow_mul_natCast hx₀, (by push_cast; ring : δ / 2 * (2 : ℕ) = δ)]
    rw [he] at hxy
    nlinarith only [hxy, hq, mul_nonneg (sub_nonneg.mpr hq)
      (by linarith only [hq] : 0 ≤ x ^ (δ / 2) + 1)]
  calc
    |f y| ≤ log y ^ (-(B : ℝ)) := hA y ((le_max_left ..).trans hAy)
    _ ≤ (x ^ (δ / 2)) ^ (-(B : ℝ)) :=
      rpow_le_rpow_of_nonpos (by positivity) hxlog (neg_nonpos.mpr (Nat.cast_nonneg B))
    _ ≤ x ^ r := by
      rw [← rpow_mul hx₀, mul_neg, ← neg_mul]
      exact rpow_le_rpow_of_exponent_le hx hBr

end TauCeti
