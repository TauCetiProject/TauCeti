/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import TauCeti.Data.ZMod.Nilpotent

/-!
# Residues modulo two and modulo powers of two

A residue modulo two is `0` or `1`, so its canonical representative `ZMod.val` is the indicator
of being nonzero. This is the identity behind the counting arguments that read a `ℕ`-valued
weight off a `ZMod 2`-valued vector: summing the representatives of the coordinates counts the
nonzero ones.

Since `2` is nilpotent in `ℤ/2^n` (`ZMod.isNilpotent_natCast_self_pow`), the units of
`ℤ/2^{k+1}` are exactly the odd elements: an even element plus a unit is a unit, and an even
element is never a unit. These are the cases `p = 2` of `ZMod.isUnit_natCast_mul_add` and
`ZMod.not_isUnit_natCast_mul`, stated with the numeral `2`.

## Main results

* `ZMod.val_eq_ite_mod_two`: `a.val = if a ≠ 0 then 1 else 0` for `a : ZMod 2`.
* `ZMod.isUnit_two_mul_add`: `2c + u` is a unit in `ℤ/2^n` when `u` is.
* `ZMod.not_isUnit_two_mul`: `2c` is not a unit in `ℤ/2^{k+1}`.
* `ZMod.eq_two_mul_or_eq_two_mul_add_one`: every element of `ℤ/n` is even or odd.
-/

public section

namespace ZMod

/-- **The representative of a residue modulo two is the indicator of being nonzero.** -/
theorem val_eq_ite_mod_two (a : ZMod 2) : a.val = if a ≠ 0 then 1 else 0 := by
  revert a
  decide

variable {n : ℕ}

/-- An even element plus a unit is a unit in `ℤ/2^n`. -/
theorem isUnit_two_mul_add {c u : ZMod (2 ^ n)} (hu : IsUnit u) : IsUnit (2 * c + u) :=
  mod_cast isUnit_natCast_mul_add (p := 2) hu

/-- An even element of `ℤ/2^{k+1}` is not a unit. -/
theorem not_isUnit_two_mul {k : ℕ} (c : ZMod (2 ^ (k + 1))) : ¬ IsUnit (2 * c) :=
  have : Nontrivial (ZMod (2 ^ (k + 1))) :=
    ZMod.nontrivial_iff.2 (Nat.one_lt_two_pow k.succ_ne_zero).ne'
  mod_cast not_isUnit_natCast_mul (p := 2) c

/-- Every element of `ℤ/n` is even or odd, according to the parity of an integer lift. -/
theorem eq_two_mul_or_eq_two_mul_add_one (x : ZMod n) :
    (∃ c, x = 2 * c) ∨ ∃ c, x = 2 * c + 1 := by
  obtain ⟨X, rfl⟩ := ZMod.intCast_surjective x
  rcases Int.even_or_odd' X with ⟨c, rfl | rfl⟩
  · exact Or.inl ⟨c, by push_cast; ring⟩
  · exact Or.inr ⟨c, by push_cast; ring⟩

end ZMod
