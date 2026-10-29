/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.ValMinAbs

/-!
# The residue window: small integers are recovered from their residues

If `2 * |z| < n` then `z` lies strictly inside the window `(-n/2, n/2]` that `ZMod.valMinAbs`
picks representatives from, so `ZMod.valMinAbs` returns `z` itself from the residue of `z` modulo
`n`. Two integers with the same residue modulo `n` are equal as soon as they differ by less than
`n`; in particular two integers inside the window that agree modulo `n` are equal.

This is the arithmetic behind the size bound in a modular reconstruction: bound the integer you
are looking for by half the modulus and its residue determines it.

## Main results

* `TauCeti.ZMod.valMinAbs_intCast_of_two_mul_natAbs_lt`: `((z : ZMod n)).valMinAbs = z`.
* `TauCeti.ZMod.eq_of_intCast_eq_of_natAbs_sub_lt`: two integers agreeing modulo `n` and
  differing by less than `n` are equal.
-/

public section

namespace TauCeti

namespace ZMod

/-- **An integer of absolute value less than half the modulus is returned by `ZMod.valMinAbs`.**
Such a `z` is the representative of its own residue class that `ZMod.valMinAbs` chooses. -/
theorem valMinAbs_intCast_of_two_mul_natAbs_lt {n : ℕ} {z : ℤ} (h : 2 * z.natAbs < n) :
    ((z : ZMod n)).valMinAbs = z := by
  have : NeZero n := ⟨by omega⟩
  refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ?_, ?_⟩ <;> omega

/-- **An integer is determined by its residue within distance less than the modulus.** Two
integers that agree modulo `n` and differ by less than `n` are equal. -/
theorem eq_of_intCast_eq_of_natAbs_sub_lt {n : ℕ} {z w : ℤ} (hzw : (z - w).natAbs < n)
    (h : (z : ZMod n) = w) : z = w :=
  Int.eq_of_sub_eq_zero <| Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    ((ZMod.intCast_eq_intCast_iff_dvd_sub w z n).1 h.symm) hzw

end ZMod

end TauCeti
