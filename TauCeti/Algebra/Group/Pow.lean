/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Iterated powers in a monoid

## Main results

* `TauCeti.pow_pow_eq_self_of_pow_sq_eq_self`: if `a ^ (q ^ 2) = a` then `(a ^ q) ^ q = a`.
-/

public section

namespace TauCeti

variable {M : Type*} [Monoid M] {a : M} {q : ℕ}

/-- If `a ^ (q ^ 2) = a` then `(a ^ q) ^ q = a`. For example, an element of a field with `q ^ 2`
elements is fixed by applying the `q`-power map twice. -/
theorem pow_pow_eq_self_of_pow_sq_eq_self (ha : a ^ q ^ 2 = a) : (a ^ q) ^ q = a := by
  rw [← pow_mul, ← sq q, ha]

end TauCeti
