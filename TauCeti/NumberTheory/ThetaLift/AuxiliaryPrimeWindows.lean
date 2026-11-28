/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import TauCeti.Analysis.SpecialFunctions.Exp.StretchedDecay

/-!
# Logarithmic prime windows for cyclic hosts

The two auxiliary primes of a cyclic host are chosen at a common scale `Y`. Their
logarithms have sizes `Y^(ε/5)` and `Y^(ε/5) * log² Y`, respectively. These windows
make the primes larger than the polynomial thresholds for the wild-kernel estimate,
while keeping their product below the exponential threshold of that estimate.
The same upper bounds control the conductor after adjoining a dyadic layer.

The prime-window scales come from Levent Alpöge's `UpperTheory.Top.GChi` in
[`Development/AutomorphicArithmetic/CharacterBoxes/Supply.lean`][supply].

[supply]: https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/Supply.lean
-/

public section

open Filter Real
open scoped Topology

namespace TauCeti

private theorem eventually_auxiliary_prime_windows_log_budget {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in atTop, Y ^ (ε / 5) * (1 + log Y ^ 2) ≤ Y ^ (ε / 4) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by positivity : 0 < ε / 20)).bound
    (show 0 < (1 / 2 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), h,
    (tendsto_rpow_atTop (by positivity : 0 < ε / 20)).eventually_ge_atTop 2] with Y hY hlog hpow
  simp only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (log Y)),
    abs_of_nonneg (rpow_nonneg (by positivity : 0 ≤ Y) _)] at hlog
  calc
    _ ≤ Y ^ (ε / 5) * Y ^ (ε / 20) := by gcongr; linarith
    _ = _ := by rw [← Real.rpow_add (by positivity : 0 < Y)]; congr 1; ring

private theorem eventually_auxiliary_prime_windows_log_lower {ε J : ℝ} (hε : 0 < ε) (hJ : 0 < J) :
    ∀ᶠ x : ℝ in atTop, ∀ Y ≥ x ^ (1 / J),
      x ^ (ε / (6 * J)) ≤ Y ^ (ε / 5) / 2 ∧
      x ^ (ε / (5 * J)) ≤ Y ^ (ε / 5) * log Y ^ 2 / 2 := by
  have hYt : Tendsto (fun x : ℝ ↦ x ^ (1 / J)) atTop atTop := tendsto_rpow_atTop (by positivity)
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.mp (tendsto_log_atTop.eventually_ge_atTop (2 : ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hYt.eventually_ge_atTop y₀,
    (tendsto_rpow_atTop (by positivity : 0 < ε / (30 * J))).eventually_ge_atTop 2]
    with x hx hxy hlarge Y hY
  have hx₀ : 0 < x := by positivity
  have hY₀ : 0 ≤ Y := (rpow_nonneg hx₀.le _).trans hY
  have hscale : x ^ (ε / (5 * J)) ≤ Y ^ (ε / 5) := by
    calc
      _ = (x ^ (1 / J)) ^ (ε / 5) := by
        rw [← Real.rpow_mul hx₀.le]
        congr 1
        ring
      _ ≤ _ := rpow_le_rpow (rpow_nonneg hx₀.le _) hY (by positivity)
  have hsplit : x ^ (ε / (5 * J)) = x ^ (ε / (6 * J)) * x ^ (ε / (30 * J)) := by
    rw [← Real.rpow_add hx₀]
    congr 1
    ring
  have hlog : 2 ≤ log Y := hy₀ Y (hxy.trans hY)
  constructor
  · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      _ ≤ x ^ (ε / (6 * J)) * x ^ (ε / (30 * J)) := by gcongr
      _ = _ := hsplit.symm
      _ ≤ _ := hscale
  · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    refine (mul_le_mul_of_nonneg_right hscale (by norm_num)).trans ?_
    exact mul_le_mul_of_nonneg_left (by nlinarith) (rpow_nonneg hY₀ _)

private theorem eventually_auxiliary_prime_windows_lt_min {ε J : ℝ} (hε : 0 < ε) (hJ : 0 < J)
    (r C : ℝ) : ∀ᶠ x : ℝ in atTop, ∀ q d : ℕ,
      x ^ (ε / (6 * J)) ≤ log (q : ℝ) → x ^ (ε / (6 * J)) ≤ log (d : ℝ) →
      2 * x ^ r + C < min (q : ℝ) (d : ℝ) := by
  let a := ε / (6 * J)
  let R := max r 0
  let B := 3 + |C|
  have hB : 0 < B := by dsimp [B]; positivity
  have h := (isLittleO_exp_neg_mul_rpow_rpow_atTop one_pos (by positivity : 0 < a) (-R)).bound
    (one_div_pos.mpr hB)
  filter_upwards [eventually_ge_atTop (1 : ℝ), h] with x hx hsmall q d hq hd
  have hx₀ : 0 < x := by positivity
  have hcompare : B * x ^ R ≤ exp (x ^ a) := by
    apply (div_le_div_iff_of_pos_left zero_lt_one (exp_pos _) (by positivity)).mp
    rw [Real.norm_of_nonneg (exp_pos _).le, Real.norm_of_nonneg (rpow_nonneg hx₀.le _)] at hsmall
    simpa only [neg_mul, one_mul, exp_neg, Real.rpow_neg hx₀.le,
      inv_eq_one_div, one_div_mul_one_div] using hsmall
  have hpoly : 2 * x ^ r + C < B * x ^ R := by
    have hR := one_le_rpow hx (show 0 ≤ R from le_max_right ..)
    have hr := rpow_le_rpow_of_exponent_le hx (show r ≤ R from le_max_left ..)
    dsimp only [B]
    nlinarith [le_abs_self C, mul_nonneg (abs_nonneg C) (sub_nonneg.mpr hR)]
  have hexp (n : ℕ) (hn : x ^ a ≤ log (n : ℝ)) : exp (x ^ a) ≤ n := by
    have hpos : 0 < (n : ℝ) := (Nat.cast_nonneg n).lt_of_ne' fun he ↦ by
      rw [he, log_zero] at hn
      exact (rpow_pos_of_pos hx₀ _).not_ge hn
    simpa only [exp_log hpos] using Real.exp_le_exp.mpr hn
  exact hpoly.trans_le (hcompare.trans (le_min (hexp q hq) (hexp d hd)))

/-- Uniform bounds for the two auxiliary-prime windows. If `Y ≥ x^(1/J)`, then both primes
exceed `2 * x^r + C` and their logarithms satisfy the two lower bounds needed for the host.
The sum of the logarithms is at most `Y^(ε/4)`. When also `Y ≤ x`, the second logarithm is at
most `x^(ε/4)` and the product fits the conductor budget at `x`. Primality is not used. -/
theorem eventually_auxiliary_prime_window_bounds {ε J : ℝ} (hε : 0 < ε) (hJ : 0 < J) (r C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ Y ≥ x ^ (1 / J), ∀ q d : ℕ,
      log (q : ℝ) ∈ Set.Icc (Y ^ (ε / 5) / 2) (Y ^ (ε / 5)) →
      log (d : ℝ) ∈ Set.Icc (Y ^ (ε / 5) * log Y ^ 2 / 2) (Y ^ (ε / 5) * log Y ^ 2) →
      2 * x ^ r + C < min (q : ℝ) (d : ℝ) ∧
      x ^ (ε / (6 * J)) ≤ log (q : ℝ) ∧ x ^ (ε / (5 * J)) ≤ log (d : ℝ) ∧
      log (q : ℝ) + log (d : ℝ) ≤ Y ^ (ε / 4) ∧
      (Y ≤ x → log (d : ℝ) ≤ x ^ (ε / 4) ∧
        log (q : ℝ) + log (d : ℝ) ≤ x ^ (ε / 5) * (1 + log x ^ 2)) := by
  obtain ⟨z, hz⟩ := eventually_atTop.mp (eventually_auxiliary_prime_windows_log_budget hε)
  have hYt : Tendsto (fun x : ℝ ↦ x ^ (1 / J)) atTop atTop := tendsto_rpow_atTop (by positivity)
  filter_upwards [hYt.eventually_ge_atTop (max 1 z), eventually_ge_atTop (1 : ℝ),
    eventually_auxiliary_prime_windows_log_lower hε hJ,
    eventually_auxiliary_prime_windows_lt_min hε hJ r C]
    with x hxz hx hlo hpoly Y hY q d hq hd
  have hY₁ : 1 ≤ Y := (le_max_left ..).trans (hxz.trans hY)
  obtain ⟨hqlo, hdlo⟩ := hlo Y hY
  have hq' := hqlo.trans hq.1
  have hd' := hdlo.trans hd.1
  have he : ε / (6 * J) ≤ ε / (5 * J) := by
    exact div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
  have hdq := (rpow_le_rpow_of_exponent_le hx he).trans hd'
  have hupper : log (q : ℝ) + log (d : ℝ) ≤ Y ^ (ε / 5) * (1 + log Y ^ 2) := by
    linarith only [hq.2, hd.2]
  have hsum := hupper.trans (hz Y ((le_max_right ..).trans (hxz.trans hY)))
  refine ⟨hpoly q d hq' hdq, hq', hd', hsum, fun hYx ↦ ⟨?_, ?_⟩⟩
  · exact (le_add_of_nonneg_left (log_natCast_nonneg q)).trans
      (hsum.trans (rpow_le_rpow (by positivity) hYx (by positivity)))
  · have hlog := Real.log_le_log (by positivity : 0 < Y) hYx
    exact hupper.trans (by gcongr; exact log_nonneg hY₁)

/-- A conductor dividing the positive modulus `lcm D f * q * d`, where `f` is fixed and the
layer level `D` is polynomially bounded in `x`, lies beneath the thin-scale conductor cutoff.
The input on `log q + log d` is supplied by the auxiliary-prime windows at `Y ≤ x`. -/
theorem eventually_log_cyclic_host_conductor_le {ε : ℝ} (hε : 0 ≤ ε) (f : ℕ) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ D q d N : ℕ, 0 < D.lcm f * q * d → N ∣ D.lcm f * q * d →
      (D : ℝ) ≤ x ^ A → log (q : ℝ) + log (d : ℝ) ≤ x ^ (ε / 5) * (1 + log x ^ 2) →
      log (N : ℝ) ≤ 2 * x ^ (ε / 5) * log x ^ 2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), tendsto_log_atTop.eventually_ge_atTop
    (2 + |A| + log (f : ℝ))] with x hx hlog D q d N hpos hN hD hqd
  have hx₀ : 0 < x := by positivity
  obtain ⟨hprod, hd₀⟩ := Nat.mul_ne_zero_iff.mp hpos.ne'
  obtain ⟨hlcm, hq₀⟩ := Nat.mul_ne_zero_iff.mp hprod
  obtain ⟨hDpos, hfpos⟩ := Nat.lcm_pos_iff.mp (Nat.pos_of_ne_zero hlcm)
  have hle : N ≤ D * f * q * d := (Nat.le_of_dvd hpos hN).trans
    (Nat.mul_le_mul_right d (Nat.mul_le_mul_right q (Nat.lcm_le_mul hDpos hfpos)))
  have hle' : (N : ℝ) ≤ (D : ℝ) * f * q * d := by exact_mod_cast hle
  have h := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_dvd_of_pos hN hpos)) hle'
  have hDreal : 0 < (D : ℝ) := Nat.cast_pos.mpr hDpos
  have hfreal : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hfpos.ne'
  have hqreal : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq₀
  have hdreal : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd₀
  have hDf := mul_ne_zero hDreal.ne' hfreal
  rw [Real.log_mul (mul_ne_zero hDf hqreal) hdreal, Real.log_mul hDf hqreal,
    Real.log_mul hDreal.ne' hfreal] at h
  have hDlog : log (D : ℝ) ≤ A * log x := by
    rw [← Real.log_rpow hx₀]
    exact Real.log_le_log hDreal hD
  have hlog₀ := log_natCast_nonneg f
  have hlog₁ : 1 ≤ log x := by linarith [abs_nonneg A]
  have hc : A * log x + log (f : ℝ) + 1 ≤ log x ^ 2 := by
    calc
      _ ≤ (A + log (f : ℝ) + 1) * log x := by
        nlinarith [mul_nonneg (add_nonneg hlog₀ zero_le_one) (sub_nonneg.mpr hlog₁)]
      _ ≤ _ := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self A]) (by linarith)
  have hxpow := one_le_rpow hx (by positivity : 0 ≤ ε / 5)
  nlinarith [mul_nonneg (sub_nonneg.mpr hxpow) (sub_nonneg.mpr (show 1 ≤ log x ^ 2 by nlinarith))]

end TauCeti
