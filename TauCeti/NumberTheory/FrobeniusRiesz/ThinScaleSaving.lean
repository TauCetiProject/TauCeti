/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A uniform saving at thin scales

If the logarithm of the conductor is bounded by a power `α < 1` of the logarithm
of the cutoff, the mixed exponential from a first Riesz error gives a uniform
saving at exponent `1 - α`. A possible exceptional-zero contribution with a
fixed gap from one is absorbed at the same scale. The exponential rate of the
saving does not depend on that gap; the threshold does.

The mixed error has the shape of the character prime number theorem of
Iwaniec–Kowalski, *Analytic Number Theory*, Theorem 5.27, after Riesz smoothing.
-/

public section

open Filter Real
open scoped Topology

namespace TauCeti

-- The denominator is positive on the domain of the conductor bound.
private theorem mixed_rate_le {V ℓ α c : ℝ} (hV : 1 ≤ V) (hℓ : 0 ≤ ℓ) (hℓV : ℓ ≤ V ^ α)
    (hα : 1 / 2 ≤ α) (hc : 0 ≤ c) :
    (c / 2) * V ^ (1 - α) ≤ c * V / (√V + ℓ) := by
  have hV₀ := zero_lt_one.trans_le hV
  have hden : 0 < √V + ℓ := add_pos_of_pos_of_nonneg (sqrt_pos.mpr hV₀) hℓ
  have hden' : √V + ℓ ≤ 2 * V ^ α := by
    rw [sqrt_eq_rpow]
    linarith [rpow_le_rpow_of_exponent_le hV hα]
  apply (le_div_iff₀ hden).mpr
  calc
    _ ≤ (c / 2) * V ^ (1 - α) * (2 * V ^ α) := by gcongr
    _ = c * (V ^ (1 - α) * V ^ α) := by ring
    _ = _ := by rw [← rpow_add hV₀, sub_add_cancel, rpow_one]

/-- Uniformly for `0 ≤ ℓ ≤ V ^ α`, a polynomial in `ℓ` times the mixed
exponential, plus a fixed exponentially decreasing error, is eventually at most
`exp (-(c / 4) * V ^ (1 - α))`. The rate is independent of the rate `d` of the
second error. In applications `V = log y` and `ℓ = log q`. -/
theorem eventually_riesz_error_profile_le {α c d : ℝ}
    (hα : 1 / 2 ≤ α) (hα₁ : α < 1) (hc : 0 < c) (hd : 0 < d)
    (C D : ℝ) (k : ℕ) :
    ∀ᶠ V : ℝ in atTop, ∀ ℓ : ℝ, 0 ≤ ℓ → ℓ ≤ V ^ α →
      C * (1 + ℓ) ^ k * exp (-c * V / (√V + ℓ)) + D * exp (-d * V) ≤
        exp (-(c / 4) * V ^ (1 - α)) := by
  let p := 1 - α
  have hp : 0 < p := sub_pos.mpr hα₁
  let M := max C 0 * 2 ^ k + max D 0
  have hdecay := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ) / p)
    (c / 4) (by positivity)).comp (tendsto_rpow_atTop hp)).const_mul M
  rw [mul_zero] at hdecay
  have hsmall := hdecay.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hgap0 := (tendsto_rpow_neg_atTop (show α > 0 by linarith)).const_mul (c / 2)
  rw [mul_zero] at hgap0
  have hgap := hgap0.eventually (gt_mem_nhds hd)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall, hgap] with V hV hsmall hgap ℓ hℓ hℓV
  have hV₀ : 0 < V := zero_lt_one.trans_le hV
  have hgap' : (c / 2) * V ^ p ≤ d * V := by
    have hh := mul_le_mul_of_nonneg_right hgap.le hV₀.le
    rw [mul_assoc, ← rpow_add_one hV₀.ne', neg_add_eq_sub] at hh
    exact hh
  have hrate := mixed_rate_le hV hℓ hℓV hα hc.le
  have hcoef : (1 + ℓ) ^ k ≤ 2 ^ k * V ^ k := by
    rw [← mul_pow]
    have hα₂ : α ≤ 1 := hα₁.le
    have hαV : V ^ α ≤ V := by simpa using rpow_le_rpow_of_exponent_le hV hα₂
    gcongr
    linarith
  have hsmall' : M * (V ^ k * exp (-(c / 4) * V ^ p)) ≤ 1 := by
    have hk : (V ^ p) ^ ((k : ℝ) / p) = V ^ k := by
      rw [← rpow_mul hV₀.le, show p * ((k : ℝ) / p) = k by field_simp, rpow_natCast]
    simpa only [Function.comp_apply, hk] using hsmall.le
  have hfirst : C * (1 + ℓ) ^ k * exp (-c * V / (√V + ℓ)) ≤
      max C 0 * (2 ^ k * V ^ k) * exp (-(c / 2) * V ^ p) := by
    rw [neg_mul, neg_div]
    gcongr
    · exact le_max_left _ _
    · linarith only [hrate]
  have hsecond : D * exp (-d * V) ≤ max D 0 * V ^ k * exp (-(c / 2) * V ^ p) := by
    have hpow : 1 ≤ V ^ k := one_le_pow₀ hV
    have hD : D ≤ max D 0 * V ^ k :=
      (le_max_left _ _).trans (le_mul_of_one_le_right (le_max_right _ _) hpow)
    exact mul_le_mul hD (exp_le_exp.mpr (by linarith only [hgap']))
      (exp_pos _).le (by positivity)
  calc
    _ ≤ M * V ^ k * exp (-(c / 2) * V ^ p) := by dsimp [M]; linarith only [hfirst, hsecond]
    _ = (M * (V ^ k * exp (-(c / 4) * V ^ p))) * exp (-(c / 4) * V ^ p) := by
      rw [← mul_assoc M, mul_assoc (M * V ^ k), ← exp_add]
      congr 2
      ring
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hsmall' (exp_pos _).le

-- The real exceptional term, normalized by the cutoff, has a linear exponential rate.
private theorem exceptional_riesz_term_le {y β δ : ℝ} (hy : 1 ≤ y) (hδ : 0 < δ)
    (hβ : 1 / 2 ≤ β) (hgap : β ≤ 1 - δ) :
    y ^ β / (β * (1 - β)) ≤ y * ((2 / δ) * exp (-δ * log y)) := by
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  have hβδ : 0 < β * (1 - β) := mul_pos (by linarith) (by linarith)
  have hβ₁ : β ≤ 1 := by linarith
  have hnum : y ^ β ≤ y * exp (-δ * log y) := by
    rw [rpow_def_of_pos hy₀, ← exp_log hy₀, ← exp_add, log_exp]
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hgap) (log_nonneg hy)]
  have hrec : (β * (1 - β))⁻¹ ≤ 2 / δ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hβδ hδ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hβ) (sub_nonneg.mpr hβ₁)]
  rw [div_eq_mul_inv]
  calc
    _ ≤ (y * exp (-δ * log y)) * (2 / δ) := by gcongr
    _ = _ := by ring

/-- On the thin scale `log q ≤ (log y)^α`, absorb the conductor-dependent bound
for the first Riesz error and the exceptional-zero term into one unit-constant
estimate. The exceptional term may be omitted (set `e = 0`). The rate `c / 4`
is independent of the lower bound `δ` on the exceptional-zero gap. -/
theorem eventually_riesz_error_with_exception_le {α c δ : ℝ}
    (hα : 1 / 2 ≤ α) (hα₁ : α < 1) (hc : 0 < c) (hδ : 0 < δ) (C : ℝ) :
    ∀ᶠ y : ℝ in atTop, ∀ q : ℕ, log q ≤ (log y) ^ α →
      ∀ β e : ℝ, 1 / 2 ≤ β → β ≤ 1 - δ → e ≤ 1 →
        C * y * log (3 * q) ^ 5 * exp (-c * log y / (√(log y) + log q)) +
          e * (y ^ β / (β * (1 - β))) ≤ y * exp (-(c / 4) * (log y) ^ (1 - α)) := by
  have hs := tendsto_log_atTop.eventually
    (eventually_riesz_error_profile_le hα hα₁ hc hδ (max C 0 * 2 ^ 5) (2 / δ) 5)
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with y hs hy q hqV β e hβ hgap he
  have hlog := log_natCast_nonneg q
  have hq' : log (3 * (q : ℝ)) ≤ 2 * (1 + log q) := by
    rcases eq_or_ne q 0 with rfl | hq
    · simp
    rw [log_mul (by norm_num : (3 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hq)]
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hlog' : 0 ≤ log (3 * (q : ℝ)) := by exact_mod_cast log_natCast_nonneg (3 * q)
  have hmain : C * y * log (3 * q) ^ 5 * exp (-c * log y / (√(log y) + log q)) ≤
      y * ((max C 0 * 2 ^ 5) * (1 + log q) ^ 5 * exp (-c * log y / (√(log y) + log q))) := by
    calc
      _ ≤ max C 0 * y * (2 * (1 + log q)) ^ 5 * exp (-c * log y / (√(log y) + log q)) := by
        gcongr
        exact le_max_left _ _
      _ = _ := by rw [mul_pow]; ring
  have hterm : 0 ≤ y ^ β / (β * (1 - β)) := by
    have : 0 ≤ β := by linarith
    have : 0 ≤ 1 - β := by linarith
    positivity
  have hE := (mul_le_of_le_one_left hterm he).trans (exceptional_riesz_term_le hy hδ hβ hgap)
  exact (add_le_add hmain hE).trans (by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hs _ hlog hqV) (zero_le_one.trans hy))

end TauCeti
