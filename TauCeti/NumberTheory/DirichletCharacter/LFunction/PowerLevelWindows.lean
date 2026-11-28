/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ZMod.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogarithmicWindows
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.PowerLevel

/-!
# Primes in logarithmic windows for powers of a fixed modulus

A single threshold works for all levels in a tower that are at most a fixed power of the window
width. The uniform near-one estimate for the tower supplies the disk hypothesis of the Gaussian
prime-window criterion. This gives the logarithmic prime selection of
`New.exists_prime_modEq_one_log_mem` in [`Lib/Analytic/Primes.lean`][short-proof], for every
reduced residue class rather than just `1`.

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/Primes.lean
-/

public section

open Filter Set

namespace TauCeti.LSeries

/-- For every sufficiently large width `W` (depending only on `m` and `A`), every reduced
class modulo a power `m ^ k ≤ W ^ A` contains a prime with logarithm in `[U, U + W]` whenever
`W ≤ U ≤ W ^ A`. The base `m` can be any positive integer. -/
theorem eventually_exists_prime_log_mem_Icc_pow_level (m : ℕ) [NeZero m] (A : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ (k : ℕ) {U : ℝ}, (↑(m ^ k) : ℝ) ≤ W ^ A → U ∈ Icc W (W ^ A) →
      ∀ a : (ZMod (m ^ k))ˣ, ∃ p : ℕ,
        p.Prime ∧ (p : ZMod (m ^ k)) = a ∧ Real.log p ∈ Icc U (U + W) := by
  have hwindow := Real.tendsto_sqrt_atTop.eventually
    (eventually_exists_prime_log_mem_Icc_of_logDeriv_bound (2 * A))
  have hderiv := Real.tendsto_sqrt_atTop.eventually
    (DirichletCharacter.eventually_norm_logDeriv_entireLFunction_le_near_one m (2 * A))
  filter_upwards [eventually_ge_atTop (0 : ℝ), hwindow, hderiv] with W hW hwindow hderiv
  intro k U hk hU a
  have hpow : (√W) ^ (2 * A) = W ^ A := by rw [pow_mul, Real.sq_sqrt hW]
  have hφ : ((m ^ k).totient : ℝ) ≤ W ^ A :=
    (Nat.cast_le.mpr (Nat.totient_le (m ^ k))).trans hk
  have h := hwindow (q := m ^ k) (U := U)
    (by simpa only [Real.sq_sqrt hW] using hU.1) (by simpa only [hpow] using hU.2)
    (by simpa only [hpow] using hφ) (fun χ s hs ↦ by
      obtain ⟨hne, hle⟩ := hderiv k (by simpa only [hpow, Nat.cast_pow] using hk) χ s
        (by simpa only [one_div] using hs)
      exact ⟨hne, hle.trans (min_le_left _ _)⟩) a
  simpa only [Real.sq_sqrt hW] using h

end TauCeti.LSeries
