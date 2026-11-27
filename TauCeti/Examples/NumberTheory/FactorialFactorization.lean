/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.FactorialFactorization.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Checks for the least number of bounded factors of `n!`

* `4! = 24 = 2 · 12`, and `24 > 16`, so `factorialFactorCount 16 4 = 2`.
* `4! = 2 · 3 · 4`, and two factors at most `4` have product at most `16 < 24`, so
  `factorialFactorCount 4 4 = 3`.
* `3! = 6` has the prime factor `3 > 2`, so it has no factorization into factors at most `2` and
  `factorialFactorCount 2 3` is the junk value `0`.
-/

public section

namespace TauCeti.Examples.NumberTheory.FactorialFactorization

open Nat

example : factorialFactorCount 16 4 = 2 := by
  have hle : factorialFactorCount 16 4 ≤ 2 :=
    factorialFactorCount_le_card (s := {2, 12}) (by decide) (by decide)
  have hpow := factorial_le_pow_factorialFactorCount (B := 16) (n := 4) fun _ _ h ↦ by omega
  interval_cases factorialFactorCount 16 4 <;> simp_all [factorial]

example : factorialFactorCount 4 4 = 3 := by
  have hle : factorialFactorCount 4 4 ≤ 3 :=
    factorialFactorCount_le_card (s := {2, 3, 4}) (by decide) (by decide)
  have hpow := factorial_le_pow_factorialFactorCount (B := 4) (n := 4) fun _ _ h ↦ h
  interval_cases factorialFactorCount 4 4 <;> simp_all [factorial]

example : factorialFactorCount 2 3 = 0 :=
  factorialFactorCount_eq_zero_iff.2 (.inr ⟨3, prime_three, le_rfl, by norm_num⟩)

end TauCeti.Examples.NumberTheory.FactorialFactorization
