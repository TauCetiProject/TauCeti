/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.TotalRemainder
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.IntegerEstimate

/-!
# The signed prime remainder at integer cutoffs

The bound on the total remainder over cyclotomic place labels implies a power bound at integer
cutoffs when the two signed remainders decay as inverse powers of the logarithm. The transfer uses
`Parameters.primeRemainder_le_of_totalRemainder_bound` to isolate the short cutoff and
`eventually_le_rpow_natCast_of_two_cutoffs` to estimate the terms at the long cutoff.

The bound follows `New.eventually_primeRemainder_natCast_le` in
`grh/src/New/Reduction/OneSidedBound.lean` of grh-lean at revision `72fead1`
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Filter Real

namespace TauCeti.OneSidedBound.Parameters

/-- If the cyclotomic total remainder satisfies its scaled upper bound at sufficiently large
integer cutoffs, logarithmic decay at levels `q₀` and `1` gives the one-sided bound with
coefficient `64 * φ(q₀) + 3` and exponent `-1/2 + 6 * ε`. Only the cardinality and residue
class of the exceptional labels enter this transfer. -/
theorem eventually_primeRemainder_natCast_le_of_totalRemainder_bound (P : Parameters)
    {ε : ℝ} {B : ℕ} (hB : 24 ≤ ε * (B : ℝ))
    (hR : ∀ᶠ y : ℝ in atTop, |primeRemainder P.d P.q₀ y| ≤ log y ^ (-(B : ℝ)))
    (hS : ∀ᶠ y : ℝ in atTop, |primeRemainder P.d 1 y| ≤ log y ^ (-(B : ℝ)))
    (hmain : ∀ᶠ x : ℕ in atTop, ∃ (s x₁ b m : ℕ) (A : Finset (ZMod (P.q₁ s))ˣ),
      x₁ ≤ x * b ∧
      (x : ℝ) ^ (ε / 6) - 1 ≤ log x₁ ∧ log b ≤ (x : ℝ) ^ ε + 1 ∧ √(x : ℝ) ≤ m ∧
      (∀ τ ∈ A, ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = -1) ∧
      ((Finset.univ.filter fun τ ↦ ZMod.unitsMap (P.q₀_dvd_q₁ s) τ = 1).card : ℝ) ≤
        A.card * log b ∧
      (m : ℝ) * P.totalRemainder s A (x * b) (x * b : ℕ) x x₁ ≤
        (Fintype.card (ZMod (P.q₁ s))ˣ : ℝ) * (x * b : ℕ) * log b ^ 5) :
    ∀ᶠ x : ℕ in atTop,
      primeRemainder P.d P.q₀ x ≤ (64 * (P.q₀.totient : ℝ) + 3) * (x : ℝ) ^ (-(1 / 2) + 6 * ε) := by
  refine eventually_le_rpow_natCast_of_two_cutoffs (Nat.cast_nonneg _) hB hR hS ?_
  have hε : 0 < ε := pos_of_mul_pos_left (by linarith only [hB]) (Nat.cast_nonneg B)
  filter_upwards [hmain, eventually_gt_atTop (1 : ℕ)] with x hx hx_gt_one
  obtain ⟨s, x₁, b, m, A, hcut, hlog₁, hlogb, hm, hclass, hcard, hrem⟩ := hx
  have hx₀ : 0 < x := zero_lt_one.trans hx_gt_one
  have hlog₁pos : 0 < log (x₁ : ℝ) := by
    have hpow := one_lt_rpow (by exact_mod_cast hx_gt_one : (1 : ℝ) < x) (by positivity : 0 < ε / 6)
    linarith only [hpow, hlog₁]
  have hx₁ : 0 < x₁ := Nat.pos_of_ne_zero fun h ↦ by
    simp only [h, Nat.cast_zero, log_zero, lt_irrefl] at hlog₁pos
  have ha : 0 < x * b := hx₁.trans_le hcut
  have hxN : x ≤ x * b := Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left ha)
  have hN : ⌊max (x : ℝ) x₁⌋₊ ≤ x * b := by
    have hmax : max (x : ℝ) x₁ ≤ ((x * b : ℕ) : ℝ) :=
      max_le (by exact_mod_cast hxN) (by exact_mod_cast hcut)
    exact (Nat.floor_mono hmax).trans_eq (Nat.floor_natCast _)
  have hm₀ : (0 : ℝ) < m := (sqrt_pos.mpr (Nat.cast_pos.mpr hx₀)).trans_le hm
  exact ⟨x₁, Nat.cast_pos.mpr hx₁, log b, log_natCast_nonneg _, m, hlog₁, hlogb, hm,
    P.primeRemainder_le_of_totalRemainder_bound hclass (Nat.cast_pos.mpr ha)
      (Nat.cast_pos.mpr hx₀) (Nat.cast_pos.mpr hx₁) hN hm₀ hcard hrem⟩

end TauCeti.OneSidedBound.Parameters
