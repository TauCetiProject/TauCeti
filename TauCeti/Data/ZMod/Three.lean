/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs

/-!
# Residues modulo three

A residue modulo three is `0`, `1`, or `2`.

## Main results

* `ZMod.eq_zero_or_eq_one_or_eq_two`: every element of `ZMod 3` is `0`, `1`, or `2`.
-/

public section

namespace ZMod

/-- Every residue modulo three is `0`, `1`, or `2`. -/
theorem eq_zero_or_eq_one_or_eq_two (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  decide +revert

end ZMod
