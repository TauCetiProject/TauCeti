/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs

/-!
# Exponential characteristic

Basic consequences of the exponential characteristic for semirings.

## Main results

* `ExpChar.prime_of_ne_one`: an exponential characteristic other than one is prime.
-/

public section

namespace ExpChar

/-- An exponential characteristic other than one is prime. -/
theorem prime_of_ne_one (R : Type*) [AddMonoidWithOne R] (p : ℕ) [ExpChar R p]
    (hp : p ≠ 1) : p.Prime :=
  (expChar_is_prime_or_one R p).resolve_right hp

end ExpChar
