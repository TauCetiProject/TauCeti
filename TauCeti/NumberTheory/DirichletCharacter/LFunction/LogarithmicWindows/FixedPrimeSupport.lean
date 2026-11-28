/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Real.Sqrt
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogarithmicWindows.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.FixedPrimeSupport

/-!
# Primes in logarithmic windows for levels with fixed prime support

If the level ranges over integers supported on a fixed finite set of primes, every reduced residue
class has a prime in each sufficiently wide logarithmic window, uniformly for polynomially bounded
levels and left endpoints. This includes all powers of a fixed positive integer as levels. The
Gaussian prime-detection argument is that of `New.exists_prime_modEq_one_log_mem` in
[`grh/src/Lib/Analytic/Primes.lean` of lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/Lib/Analytic/Primes.lean
-/

public section

open Filter Set TauCeti.DirichletCharacter

namespace TauCeti.LSeries

/-- For sufficiently large `W`, every interval `[U, U + W]` with `W ≤ U ≤ W ^ A`
contains the logarithm of a prime in each reduced class modulo `q`, uniformly for
`q ≤ W ^ A` with prime divisors in `S`. The threshold for `W` depends only on `S` and `A`. -/
theorem eventually_exists_prime_log_mem_Icc_of_primeFactors_subset (S : Finset ℕ) (A : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ {q : ℕ} [NeZero q], q.primeFactors ⊆ S → (q : ℝ) ≤ W ^ A →
      ∀ ⦃U : ℝ⦄, W ≤ U → U ≤ W ^ A → ∀ a : (ZMod q)ˣ,
        ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ Real.log p ∈ Icc U (U + W) := by
  have hdetect := eventually_exists_prime_log_mem_Icc_of_logDeriv_bound (2 * A)
  have hbounds :=
    eventually_entireLFunction_ne_zero_and_norm_logDeriv_le_of_primeFactors_subset S (2 * A)
  filter_upwards [eventually_ge_atTop (0 : ℝ), Real.tendsto_sqrt_atTop.eventually hdetect,
    Real.tendsto_sqrt_atTop.eventually hbounds] with W hW hprime hdisk
  intro q _ hS hq U hU hUA a
  have hscale : (√W) ^ (2 * A) = W ^ A := by rw [pow_mul, Real.sq_sqrt hW]
  have htot : (q.totient : ℝ) ≤ (√W) ^ (2 * A) := by
    rw [hscale]
    exact (Nat.cast_le.mpr q.totient_le).trans hq
  simpa only [Real.sq_sqrt hW] using hprime (by simpa only [Real.sq_sqrt hW] using hU)
    (hscale ▸ hUA) htot (hdisk hS (hscale ▸ hq)) a

end TauCeti.LSeries
