/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The value of the cyclic rotation of `Fin n`

Mathlib's `coe_finRotate` computes the value of `finRotate` on `Fin (n + 1)`, comparing the index
with `Fin.last n`. When the size of the type is not syntactically a successor, as for
`Fin (2 * (m + 1))`, it does not apply by rewriting. This file states the same computation for
every `Fin n`, with the wrap-around case read off the value of the index.
-/

public section

namespace TauCeti

/-- The cyclic rotation `finRotate n` adds one to the value of an index, except that it sends the
last index `n - 1` to `0`. -/
theorem coe_finRotate_eq_ite {n : ℕ} (i : Fin n) :
    (finRotate n i : ℕ) = if (i : ℕ) + 1 = n then 0 else (i : ℕ) + 1 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    rw [coe_finRotate]
    simp [Fin.ext_iff]

end TauCeti
