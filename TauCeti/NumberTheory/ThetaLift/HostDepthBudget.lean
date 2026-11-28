/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import TauCeti.NumberTheory.PrimeFactors.Lcm

/-!
# Depth budgets for cyclic hosts of theta chains

The part of the conductor away from the two auxiliary primes is `lcm (2^(n+2)) f`, where `f`
is fixed and `n` is the dyadic layer. The sum of the logarithms of its prime divisors is bounded
independently of the layer. The logarithm of the whole conductor bounds both the common depth
allowance at those primes and the logarithm of the product of the two auxiliary primes.

The chain length and bad-prime budgets occur in Levent Alpöge's `Formalism.MainNotions.SizesAt`
(`Formalism/SharpRestriction/ElevenLe.lean`) and `Formalism.MainNotions.LinkG_at`
(`Formalism/SharpRestriction/GlobalTheoremInputs.lean`) in the published
[formalization](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005).
-/

public section

open Filter Real

namespace TauCeti.ThetaLift

/-- A full conductor bound `log F ≤ 2 x^(ε/5) (log x)^2` implies both depth budgets uniformly
in the layer `n`, the auxiliary conductor product `Q`, and the chain length `m ≥ x^α`.
Here `F = lcm (2^(n+2)) f * Q` with `f` fixed. For `C = 11` and `α = 1/2 - ε`, the hypotheses
on the exponents hold whenever `0 < ε ≤ 1/6`. No separate bound on the layer is needed. -/
theorem eventually_cyclic_host_depth_budget {ε α C : ℝ} (hε : 0 < ε) (hα : ε / 5 < α)
    (hC : 0 < C) {f : ℕ} (hf : f ≠ 0) :
    ∀ᶠ x : ℝ in atTop, ∀ (n : ℕ) {Q : ℕ} (m : ℝ), Q ≠ 0 →
      log ((Nat.lcm (2 ^ (n + 2)) f : ℝ) * Q) ≤ 2 * x ^ (ε / 5) * log x ^ 2 →
      x ^ α ≤ m →
      log Q ≤ m ∧ (∑ p ∈ (Nat.lcm (2 ^ (n + 2)) f).primeFactors, log p) *
        (2 + logb 2 (Nat.lcm (2 ^ (n + 2)) f)) ≤ C * x ^ ε := by
  let L := log ((2 * f : ℕ) : ℝ)
  have hL : 0 ≤ L := log_natCast_nonneg _
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  let c := min 1 (C * log 2 / (2 * (L + 1)))
  have hc : 0 < c := lt_min one_pos (by positivity)
  have hgap : 0 < min α ε - ε / 5 := sub_pos.mpr (lt_min hα (by linarith))
  have hlog := ((isLittleO_log_rpow_rpow_atTop 2 hgap).const_mul_left 2).bound hc
  have hlarge := (tendsto_rpow_atTop hε).eventually_ge_atTop (4 * L / C)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlog, hlarge] with x hx hlogx hlarge
  intro n Q m hQ hcond hm
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hsq : 2 * log x ^ 2 ≤ c * x ^ (min α ε - ε / 5) :=
    (le_abs_self _).trans (by
      simpa only [rpow_two, Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hx₀.le _)] using hlogx)
  have hF : log ((Nat.lcm (2 ^ (n + 2)) f : ℝ) * Q) ≤ c * x ^ min α ε := by
    refine hcond.trans ?_
    calc
      _ = x ^ (ε / 5) * (2 * log x ^ 2) := by ring
      _ ≤ x ^ (ε / 5) * (c * x ^ (min α ε - ε / 5)) := by gcongr
      _ = _ := by rw [mul_left_comm, ← rpow_add hx₀]; ring_nf
  let S := Nat.lcm (2 ^ (n + 2)) f
  have hS : S ≠ 0 := Nat.lcm_ne_zero (by positivity) hf
  rw [log_mul (Nat.cast_ne_zero.mpr hS) (Nat.cast_ne_zero.mpr hQ)] at hF
  have hLS := log_natCast_nonneg S
  have hmul (a : ℝ) (ha : min α ε ≤ a) : c * x ^ min α ε ≤ c * x ^ a :=
    mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hx ha) hc.le
  constructor
  · exact (le_add_of_nonneg_left hLS).trans <| hF.trans <| (hmul α (min_le_left _ _)).trans <|
      (mul_le_of_le_one_left (rpow_nonneg hx₀.le _) (min_le_left _ _)).trans hm
  · have hdepth₀ : 0 ≤ logb 2 S :=
      logb_nonneg one_lt_two (by exact_mod_cast Nat.pos_of_ne_zero hS)
    have hdepth : logb 2 S ≤ C * x ^ ε / (2 * (L + 1)) := by
      have hb := (le_add_of_nonneg_right (log_natCast_nonneg Q)).trans
        (hF.trans (hmul ε (min_le_right _ _)))
      have hc' : c ≤ C * log 2 / (2 * (L + 1)) := min_le_right _ _
      apply (div_le_iff₀ hlog2).2
      calc
        log (S : ℝ) ≤ c * x ^ ε := hb
        _ ≤ C * log 2 / (2 * (L + 1)) * x ^ ε := by gcongr
        _ = _ := by ring
    calc
      _ ≤ L * (2 + logb 2 S) := mul_le_mul_of_nonneg_right
        (Nat.sum_log_primeFactors_lcm_pow_succ_le 2 (n + 1) f)
        (by linarith)
      _ ≤ 2 * L + (L + 1) * (C * x ^ ε / (2 * (L + 1))) := by
        rw [mul_add, mul_comm L 2]
        gcongr; linarith
      _ ≤ C * x ^ ε := by
        field_simp
        nlinarith [(div_le_iff₀ hC).1 hlarge]

end TauCeti.ThetaLift
