/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Real.Sqrt
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogarithmicWindows
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.PowerLevel

/-!
# Primes in logarithmic windows at powers of a fixed modulus

Apply the logarithmic prime-window criterion at `X = √W`, using the uniform zero-free disk at
powers of a fixed base modulus. The resulting window of width `W` contains the logarithm of a
prime in each invertible residue class, once `W` is large enough independently of the exponent.

This specializes the Gaussian window argument of `New.exists_prime_modEq_one_log_mem` in
[lsernau/grh-lean, `Primes.lean`](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/Primes.lean).
-/

public section

open Filter

namespace TauCeti.LSeries

/-- For powers of a fixed nonzero modulus, every invertible class contains a prime whose
logarithm lies in `[U, U + W]`, uniformly for `W ≤ U ≤ W ^ A` and `m ^ k ≤ W ^ A`, once `W`
is large in terms of `m` and `A`. -/
theorem eventually_exists_prime_log_mem_Icc_pow_level (m : ℕ) [NeZero m] (A : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ (k : ℕ) (a : (ZMod (m ^ k))ˣ) (U : ℝ),
      (↑(m ^ k) : ℝ) ≤ W ^ A → W ≤ U → U ≤ W ^ A →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod (m ^ k)) = a ∧ Real.log p ∈ Set.Icc U (U + W) := by
  filter_upwards [Real.tendsto_sqrt_atTop.eventually
    (eventually_exists_prime_log_mem_Icc_of_logDeriv_bound (2 * A)),
    Real.tendsto_sqrt_atTop.eventually
      (DirichletCharacter.eventually_norm_logDeriv_entireLFunction_le_near_one m (2 * A)),
    eventually_ge_atTop (0 : ℝ)] with W hprime hzero hW k a U hk hU hUA
  have hpow : (√W) ^ (2 * A) = W ^ A := by rw [pow_mul, Real.sq_sqrt hW]
  have hφ : ((m ^ k).totient : ℝ) ≤ W ^ A :=
    (by exact_mod_cast Nat.totient_le (m ^ k) : ((m ^ k).totient : ℝ) ≤ ↑(m ^ k)).trans hk
  have hp := hprime (q := m ^ k) (U := U) (by rwa [Real.sq_sqrt hW]) (by rwa [hpow])
    (by rwa [hpow]) (fun χ s hs ↦
      (hzero k (by rwa [hpow, ← Nat.cast_pow]) χ s (by simpa only [one_div] using hs)).imp_right
        fun hb ↦ hb.trans (min_le_left _ _)) a
  simpa only [Real.sq_sqrt hW] using hp

end TauCeti.LSeries
