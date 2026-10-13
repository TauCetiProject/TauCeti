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
`(-1) ^ a.val` of a residue modulo two. The residue of a natural number `c` gives the power `x ^ c`,
and the residue `-1` gives the inverse of `x`.

## Main results

* `TauCeti.pow_val_add`: `x ^ (a + b).val = x ^ a.val * x ^ b.val` when `x ^ n = 1`.
* `TauCeti.pow_val_natCast`: `x ^ (c : ZMod n).val = x ^ c` when `x ^ n = 1`.
* `TauCeti.pow_val_neg_one`: `x ^ (-1 : ZMod n).val = x⁻¹` when `x ^ n = 1` and `n ≠ 0`.
-/

public section

namespace TauCeti

/-- **A power indexed by a residue is multiplicative in the residue:** if `x ^ n = 1`, then
`x ^ (a + b).val = x ^ a.val * x ^ b.val` for `a b : ZMod n`. -/
theorem pow_val_add {M : Type*} [Monoid M] {n : ℕ} [NeZero n] {x : M} (hx : x ^ n = 1)
    (a b : ZMod n) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

/-- If `x ^ n = 1`, then the power of `x` at the residue of a natural number `c` is `x ^ c`. -/
theorem pow_val_natCast {M : Type*} [Monoid M] {n : ℕ} {x : M} (hx : x ^ n = 1) (c : ℕ) :
    x ^ (c : ZMod n).val = x ^ c := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hx]

/-- If `x ^ n = 1` with `n ≠ 0`, then the power of `x` at the residue `-1` is the inverse of `x`. -/
theorem pow_val_neg_one {G : Type*} [DivisionMonoid G] {n : ℕ} [NeZero n] {x : G}
    (hx : x ^ n = 1) : x ^ (-1 : ZMod n).val = x⁻¹ := by
  have h1 : x ^ (1 : ZMod n).val = x := by simpa using pow_val_natCast hx 1
  have h := pow_val_add hx (-1) 1
  rw [neg_add_cancel, ZMod.val_zero, pow_zero, h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm

end TauCeti
