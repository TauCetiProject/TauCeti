/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.WeakPNT
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics
import TauCeti.NumberTheory.PrimeCounting

/-!
# The asymptotic size of the `n`-th prime

The prime number theorem `π(x) ∼ x / log x` (Mathlib's `Nat.isEquivalent_primeCounting`) is
equivalent to the asymptotic `p_n ∼ n log n` for the `n`-th prime `p_n = Nat.nth Nat.Prime n`.
This file proves the forward direction.

The deduction is the asymptotic inversion of the scale `x / log x`
(`Asymptotics.IsEquivalent.log_of_div_log` and `Asymptotics.IsEquivalent.of_div_log` in
`TauCeti/Analysis/SpecialFunctions/Log/Asymptotics.lean`): if `u → ∞` and `u / log u ∼ v`, then
`log u ∼ log v` and `u ∼ v log v`. At `u n = p_n` the prime number theorem and
`π(p_n) = n + 1` (`Nat.primeCounting_nth_prime`) give `p_n / log p_n ∼ n + 1 ∼ n`, so the
inversion applies with `v n = n`. The shift by one from the indexing `Nat.nth Nat.Prime 0 = 2`
does not affect any of the equivalences.

## Main results

* `Nat.isEquivalent_nth_prime_div_log`: `p_n / log p_n ∼ n`.
* `Nat.isEquivalent_log_nth_prime`: `log p_n ∼ log n`.
* `Nat.isEquivalent_nth_prime`: `p_n ∼ n log n`.

## References

The statements and the route through `p_n / log p_n ∼ n` and `log p_n ∼ log n` follow
`pi_nth_prime_asymp`, `log_nth_prime_asymp` and `nth_prime_asymp` in the
[PrimeNumberTheoremAnd project](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/692e4768ddaaf12ac8970718bf75ab083afce494/PrimeNumberTheoremAnd/Consequences.lean).
-/

public section

open Filter Asymptotics

namespace Nat

/-- The `n`-th prime, as a real number, tends to infinity. -/
theorem tendsto_nth_prime_atTop : Tendsto (fun n ↦ (nth Nat.Prime n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_iff.mpr (nth_strictMono infinite_setOfPred_prime).tendsto_atTop

/-- The `n`-th prime satisfies `p_n / log p_n ∼ n`: this is the prime number theorem at
`x = p_n`, where `π(p_n) = n + 1`. -/
theorem isEquivalent_nth_prime_div_log :
    (fun n ↦ (nth Nat.Prime n : ℝ) / Real.log (nth Nat.Prime n)) ~[atTop] fun n ↦ (n : ℝ) := by
  have h := (isEquivalent_primeCounting.comp_tendsto tendsto_nth_prime_atTop).symm
  simp only [Function.comp_def, floor_natCast, primeCounting_nth_prime, cast_add,
    cast_one] at h
  exact h.trans <| IsEquivalent.refl.add_isLittleO <|
    (isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop

/-- The logarithm of the `n`-th prime satisfies `log p_n ∼ log n`. -/
theorem isEquivalent_log_nth_prime :
    (fun n ↦ Real.log (nth Nat.Prime n)) ~[atTop] fun n ↦ Real.log n :=
  isEquivalent_nth_prime_div_log.log_of_div_log
    tendsto_nth_prime_atTop

/-- **The size of the `n`-th prime**: `p_n ∼ n log n`. -/
theorem isEquivalent_nth_prime :
    (fun n ↦ (nth Nat.Prime n : ℝ)) ~[atTop] fun n ↦ n * Real.log n :=
  isEquivalent_nth_prime_div_log.of_div_log
    tendsto_nth_prime_atTop

end Nat
