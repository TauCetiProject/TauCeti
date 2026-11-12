/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# The von Mangoldt function at the higher prime powers

The weights `Λ(n) / n` at the non-prime `n` are supported on the prime powers `p ^ k` with
`k ≥ 2`, and their sum `∑ₚ ∑_{k ≥ 2} log p / p ^ k` is finite. This absolute constant bounds the
higher-prime-power part of every twisted von Mangoldt series on `1 ≤ re s`.

The summability is the trivial residue class case of Mathlib's
`ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div`.

## Main results

* `ArithmeticFunction.vonMangoldt.summable_nonprime_div`: `∑ₙ (if n is prime then 0 else Λ(n)) / n`
  converges.
-/

public section

open ArithmeticFunction

namespace ArithmeticFunction.vonMangoldt

/-- The von Mangoldt weights `Λ n / n` at the non-prime `n`, which are supported on the prime
powers `p ^ k` with `k ≥ 2`, are summable. -/
theorem summable_nonprime_div :
    Summable fun n : ℕ ↦ (if n.Prime then 0 else vonMangoldt n) / n := by
  have h (n : ℕ) : residueClass (1 : ZMod 1) n = vonMangoldt n :=
    Set.indicator_of_mem (Subsingleton.elim (n : ZMod 1) 1) _
  simpa only [h] using summable_residueClass_non_primes_div (1 : ZMod 1)

end ArithmeticFunction.vonMangoldt

