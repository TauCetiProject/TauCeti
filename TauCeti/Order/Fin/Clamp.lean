/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Clamp

/-!
# Clamping below the bound

`Fin.clamp n m` is `min n m` as an element of `Fin (m + 1)`. Mathlib's `Fin.clamp_eq_last`
evaluates it for `m ≤ n`; `Fin.clamp_eq_mk` is the other case, `n ≤ m`, where clamping leaves `n`
unchanged. Together they evaluate a family `r : Fin (m + 1) → α` extended to the natural numbers
by `r ∘ (Fin.clamp · m)`, as for the paths of generators of a type `D` structure.
-/

public section

namespace Fin

/-- Clamping a natural number that is at most `m` to `Fin (m + 1)` leaves it unchanged. -/
theorem clamp_eq_mk {n m : ℕ} (h : n ≤ m) : clamp n m = ⟨n, Nat.lt_succ_of_le h⟩ :=
  Fin.ext (Nat.min_eq_left h)

end Fin
