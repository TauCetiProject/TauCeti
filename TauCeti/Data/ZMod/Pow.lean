/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Powers indexed by residues

If `x ^ n = 1` in a monoid, then the power `x ^ a.val` of `x` at the canonical representative of
a residue `a : ZMod n` is multiplicative in `a`. At `n = 2` and `x = -1` this is the sign
`(-1) ^ a.val` of a residue modulo two.

## Main results

* `TauCeti.pow_val_add`: `x ^ (a + b).val = x ^ a.val * x ^ b.val` when `x ^ n = 1`.
-/

public section

namespace TauCeti

/-- **A power indexed by a residue is multiplicative in the residue:** if `x ^ n = 1`, then
`x ^ (a + b).val = x ^ a.val * x ^ b.val` for `a b : ZMod n`. -/
theorem pow_val_add {M : Type*} [Monoid M] {n : ℕ} [NeZero n] {x : M} (hx : x ^ n = 1)
    (a b : ZMod n) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

end TauCeti
