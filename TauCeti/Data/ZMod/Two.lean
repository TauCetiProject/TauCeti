/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# The canonical representative of a residue modulo two

A residue modulo two is `0` or `1`, so its canonical representative `ZMod.val` is the indicator
of being nonzero. This is the identity behind the counting arguments that read a `ℕ`-valued
weight off a `ZMod 2`-valued vector: summing the representatives of the coordinates counts the
nonzero ones.

## Main results

* `ZMod.val_eq_ite_mod_two`: `a.val = if a ≠ 0 then 1 else 0` for `a : ZMod 2`.
-/

public section

namespace ZMod

/-- **The representative of a residue modulo two is the indicator of being nonzero.** -/
theorem val_eq_ite_mod_two (a : ZMod 2) : a.val = if a ≠ 0 then 1 else 0 := by
  revert a
  decide

end ZMod
