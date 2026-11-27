/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Ranks
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Scales
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.SparseExponents
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.SparsePlaceScales

/-!
# Joint selection of ranks, cutoffs and Behrend parameters

The cyclotomic level used to round the larger cutoff depends on the chosen dyadic rank.
For fixed arithmetic parameters, the ranks, both integral cutoffs and the side length of the
Behrend box can be chosen together at every sufficiently large integer. In particular, the box
fits the same dyadic tower and its cardinality bound is large enough at the chosen cutoff.

The choices follow `New.eventually_exists_data` and `New.Parameters.exists_isSparse` in
`grh/src/New/Reduction/Data/Existence.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Reduction/Data/Existence.lean
-/

public section

open Filter Real

namespace TauCeti.OneSidedBound

/-- Choose the least admissible dyadic and ternary ranks, the integral cutoffs, and the
Behrend box simultaneously. The dimension `n` is fixed for all sufficiently large integers `x`.
The bound on the box cardinality pays for the tower degree after multiplying by `log b`,
and the short-transition bound is for the same ranks and tower used to round `b`. The threshold
`C` bounds `log (log b)` from below and is independent of `x`. -/
theorem Parameters.eventually_exists_admissible_ranks_and_scales (P : Parameters)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 100) (C : ℝ) :
    ∃ n : ℕ, 0 < n ∧ ∀ᶠ x : ℕ in atTop, ∃ e e' x₁ b H : ℕ,
      let m : ℕ := 2 ^ e
      let r : ℕ := 3 ^ e'
      let s := 22 * e
      0 < e ∧ 0 < e' ∧
      IsLeast {u : ℕ | (∃ i : ℕ, u = 2 ^ i) ∧ √(x : ℝ) ≤ u} m ∧
      IsLeast {u : ℕ | (∃ i : ℕ, u = 3 ^ i) ∧ x ^ 5 ≤ u} r ∧
      (m : ℝ) < 2 * √(x : ℝ) ∧ r < 3 * x ^ 5 ∧ (s : ℝ) ≤ 32 * log (x : ℝ) ∧
      P.q₁ s ≤ x ^ 12 ∧ P.q₂ s ≤ x ^ (33 * (P.q₀ * P.d)) ∧
      x₁ = ⌊exp ((x : ℝ) ^ (ε / 6))⌋₊ ∧ 0 < x₁ ∧ 0 < b ∧
      IsLeast {u : ℕ | P.q₁ s * x₁ ∣ u ∧ exp ((x : ℝ) ^ ε) < (u : ℝ)} b ∧
      (x : ℝ) ^ (ε / 6) - 1 ≤ log x₁ ∧ (x : ℝ) ^ ε ≤ log b ∧
      log b ≤ (x : ℝ) ^ ε + 1 ∧ C ≤ log (log b) ∧ (log b) ^ 100 ≤ x ∧
      x ^ 10^6 ≤ x₁ ∧ x₁ ^ 10^6 ≤ b ∧ (log x₁) ^ 6 ≤ log b ∧
      2 * l₀ s * ((r + 1 - m) * (5 * r) + 1) < 2 ^ s ∧
      0 < H ∧ (2 * l₀ s * H) ^ n ≤ 2 ^ s ∧
      (towerDeg s : ℝ) ≤ ((H : ℝ) ^ n / (n * H ^ 2)) * log b := by
  obtain ⟨xmin, hxmin⟩ := eventually_atTop.mp
    (eventually_exists_admissible_ranks P.q₀ P.d P.q₀_pos)
  -- Choose the ranks first so that the modulus in the rounding theorem is a function of `x`.
  choose e er he using fun x : ℕ ↦ hxmin (max x xmin) (le_max_right x xmin)
  let q (x : ℕ) := P.q₁ (22 * e x)
  have hq : ∀ᶠ x : ℕ in atTop, (q x : ℝ) ≤ (x : ℝ) ^ (12 : ℝ) := by
    filter_upwards [eventually_ge_atTop xmin] with x hx
    have hh := he x
    simp only [max_eq_left hx, ← l₀_def, ← towerDeg_def, ← Parameters.q₁_def] at hh
    obtain ⟨_, _, _, _, _, _, _, _, hlevel, _, _⟩ := hh
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast hlevel
  have hscales := eventually_exists_admissible_scales (C := C) hε (10 ^ 6) (10 ^ 6) 100
    (by norm_num; linarith) (Eventually.of_forall fun x ↦ P.q₁_pos (22 * e x)) hq
  obtain ⟨n, hn, hnlarge⟩ := eventually_sparse_place_parameter_bounds
    (show 0 < ε / 6 by positivity) (by linarith)
  refine ⟨n, hn, ?_⟩
  filter_upwards [eventually_ge_atTop xmin, hscales,
    tendsto_natCast_atTop_atTop.eventually hnlarge] with x hx hsc hsparse
  have hh := he x
  simp only [max_eq_left hx, ← l₀_def, ← towerDeg_def, ← Parameters.q₁_def,
    ← Parameters.q₂_def] at hh
  obtain ⟨he₀, hr₀, hm, hr, hmUpper, hrUpper, hs, _, hq₁, hq₂, hshort⟩ := hh
  obtain ⟨x₁, b, hx₁, hx₁₀, hb₀, hleast, hlog₁, hlogb, hlogb', hC, hsmall, hx₁', hb', hlog₆⟩ :=
    hsc
  have hdyadic := (dyadicTower_bounds (x := x) (e := e x)
    (by exact_mod_cast hm.1.2) (by exact_mod_cast hmUpper.le)).1
  have htower : 2 ^ (22 * e x) ≤ P.q₁ (22 * e x) := by
    rw [Parameters.q₁_def, towerDeg_def, ← mul_assoc, ← mul_assoc]
    have hl : 0 < l₀ (22 * e x) := (Nat.zero_le _).trans_lt (lt_l₀ _)
    exact Nat.le_mul_of_pos_left _ (by have := P.q₀_pos; positivity)
  have hupper : (2 : ℝ) ^ (22 * e x) ≤ (x : ℝ) ^ 12 := by
    exact_mod_cast htower.trans hq₁
  obtain ⟨hW₁, hWlo, hWhi, hbase, _⟩ := hsparse (22 * e x) (by exact_mod_cast hdyadic) hupper
  obtain ⟨H, hH, hfit, hcard⟩ := exists_sparse_digit_bound_of_tower hn hWlo
    (hWhi.trans (pow_le_pow_right₀ hW₁ (Nat.le_succ n))) hbase
  rw [← rpow_mul_natCast (Nat.cast_nonneg x), show ε / 6 * ((6 : ℕ) : ℝ) = ε by norm_num] at hcard
  refine ⟨e x, er x, x₁, b, H, he₀, hr₀, hm, hr, hmUpper, hrUpper, hs, hq₁, hq₂, hx₁, hx₁₀,
    hb₀, hleast, hlog₁, hlogb, hlogb', hC, hsmall, hx₁', hb', hlog₆, hshort, hH, hfit,
    hcard.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hlogb (by positivity)

end TauCeti.OneSidedBound
