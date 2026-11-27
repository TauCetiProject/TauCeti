/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Finite

/-!
# Finiteness of iterated pointwise products

The `n`-fold pointwise product `s ^ n` of a finite set `s` in a monoid is finite
(`Set.Finite.pow`), and so is the `n`-fold sumset `n • s` in an additive monoid
(`Set.Finite.nsmul`). This complements Mathlib's `Set.Finite.mul` and `Set.Finite.add`.
-/

public section

open scoped Pointwise

namespace Set

variable {α : Type*} [Monoid α] {s : Set α}

/-- The `n`-fold pointwise product of a finite set is finite. -/
@[to_additive /-- The `n`-fold sumset of a finite set is finite. -/]
theorem Finite.pow (hs : s.Finite) (n : ℕ) : (s ^ n).Finite := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using ih.mul hs

end Set
