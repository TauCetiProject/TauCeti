/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The logarithmic search range for the level primes

The primes defining the levels are sought in logarithmic windows of width `W = x^(ε/6)`.
The search uses the progression of modulus `q₂(s)²`; the left endpoints of the windows are
at most `24 * m * log b`. Both this bound and the modulus fit under a fixed power of `W`,
independently of the tower index and the cutoff. The same width satisfies `W^6 ≤ log b`.

The scales are those of `New.Parameters.IsLargeScale.exists_isAdmissibleData` in
[`New/Reduction/Data/Existence.lean`][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Data/Existence.lean
-/

public section

open Filter Real

namespace TauCeti.OneSidedBound.Parameters

/-- At sufficiently large initial cutoffs `x`, a single exponent `A` bounds both the search
modulus `q₂(s)²` and the left-endpoint bound `24 * m * log b` by `W^A`, where
`W = x^(ε/6)`. The lower cutoff bound also ensures `7 ≤ log b` and `W^6 ≤ log b`.
The hypotheses are the modulus estimate, the dyadic rank bound and the two bounds relating
`log b` to `x`. -/
theorem eventually_levelPrime_window_bounds (P : Parameters) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℕ, ∀ᶠ x : ℕ in atTop, ∀ {s m b : ℕ},
      P.q₂ s ≤ x ^ (33 * (P.q₀ * P.d)) → (m : ℝ) ≤ 2 * √(x : ℝ) →
      (x : ℝ) ^ ε ≤ log b → (log b) ^ 2 ≤ x →
      let W := (x : ℝ) ^ (ε / 6)
      7 ≤ log b ∧ W ^ 6 ≤ log b ∧
        (P.q₂ s : ℝ) ^ 2 ≤ W ^ A ∧ 24 * m * log b ≤ W ^ A := by
  let k := 33 * (P.q₀ * P.d)
  obtain ⟨A, hA⟩ := exists_nat_ge (max (2 * (k : ℝ)) 2 / (ε / 6))
  have hA' : max (2 * (k : ℝ)) 2 ≤ (ε / 6) * A := by
    have := (div_le_iff₀ (by positivity : 0 < ε / 6)).mp hA
    simpa only [mul_comm (A : ℝ)] using this
  refine ⟨A, ?_⟩
  filter_upwards [eventually_ge_atTop (48 : ℕ),
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 7]
    with x hx hxε s m b hq hm hlo hhi
  have hx' : (48 : ℝ) ≤ x := by exact_mod_cast hx
  have hx₀ : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hW : ((x : ℝ) ^ (ε / 6)) ^ A = (x : ℝ) ^ ((ε / 6) * A) :=
    (rpow_mul_natCast hx₀ _ _).symm
  have hwidth : ((x : ℝ) ^ (ε / 6)) ^ 6 = (x : ℝ) ^ ε := by
    rw [← rpow_mul_natCast hx₀]
    norm_num
  have hlog : 7 ≤ log b := hxε.trans hlo
  have hlog_sqrt : log b ≤ √(x : ℝ) := le_sqrt_of_sq_le hhi
  have hq' : (P.q₂ s : ℝ) ≤ (x : ℝ) ^ k := by exact_mod_cast hq
  refine ⟨hlog, hwidth.le.trans hlo, ?_, ?_⟩
  · rw [hW]
    calc
      (P.q₂ s : ℝ) ^ 2 ≤ ((x : ℝ) ^ k) ^ 2 := by gcongr
      _ = (x : ℝ) ^ (2 * (k : ℝ)) := by
        rw [← pow_mul, ← rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, mul_comm (k : ℝ)]
      _ ≤ _ := rpow_le_rpow_of_exponent_le (by linarith) ((le_max_left _ _).trans hA')
  · rw [hW]
    calc
      24 * (m : ℝ) * log b ≤ 24 * (2 * √(x : ℝ)) * √(x : ℝ) := by gcongr
      _ = 48 * (x : ℝ) := by simp only [mul_assoc, mul_self_sqrt hx₀]; ring
      _ ≤ (x : ℝ) ^ 2 := by nlinarith
      _ ≤ _ := by
        rw [← rpow_ofNat (x := (x : ℝ)) (n := 2)]
        exact rpow_le_rpow_of_exponent_le (by linarith) ((le_max_right _ _).trans hA')

end TauCeti.OneSidedBound.Parameters
