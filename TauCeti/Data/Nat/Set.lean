/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Set

/-!
# Sets of natural numbers

The successor function misses exactly `0`: `(Set.range Nat.succ)ᶜ = {0}`
(`Nat.compl_range_succ`), the complement form of Mathlib's `Nat.zero_union_range_succ`.
-/

public section

namespace Nat

/-- The successor function misses exactly `0`. -/
theorem compl_range_succ : (Set.range succ)ᶜ = {0} := by
  ext n
  cases n <;> simp

end Nat
