/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Bitwise

/-!
# Fixed-width bit fields of a natural number

A natural number `M` can be read as an array of fields of `w` bits each: field `i` occupies the
bits `w * i, …, w * i + w - 1`. This file defines reading and writing such a field.

Reading is `Nat.bitField w M i = M / 2 ^ (w * i) % 2 ^ w`. Writing a value `v < 2 ^ w` replaces
exactly that field, by exclusive-or with the difference of the old and new contents shifted into
place; a value that does not fit leaves `M` unchanged, so that a write never disturbs the
neighbouring fields. Both operations use only division, remainder, powers, exclusive-or and
multiplication of natural numbers, which the kernel evaluates on binary representations. This is
what makes the fields usable as a mutable array inside a computation checked by `decide`.

## Main definitions

* `Nat.bitField`: field `i` of width `w` of a natural number.
* `Nat.setBitField`: the natural number with field `i` replaced.

## Main results

* `Nat.bitField_setBitField`: reading after writing returns the written value at the written
  index, and the old contents everywhere else.
* `Nat.bitField_lt`: a field of width `w` is less than `2 ^ w`.
-/

public section

namespace Nat

/-- **Field `i` of width `w`** of the natural number `M`: the bits `w * i, …, w * i + w - 1` of
`M`, read as a natural number below `2 ^ w`. -/
@[expose]
def bitField (w M i : ℕ) : ℕ :=
  M / 2 ^ (w * i) % 2 ^ w

/-- **`M` with field `i` of width `w` replaced by `v`**, when `v < 2 ^ w`; otherwise `M` itself.
The new contents are installed by exclusive-or with `(bitField w M i ^^^ v) * 2 ^ (w * i)`, which
only touches the bits of field `i`. -/
@[expose]
def setBitField (w M i v : ℕ) : ℕ :=
  if v < 2 ^ w then M ^^^ ((bitField w M i ^^^ v) * 2 ^ (w * i)) else M

theorem bitField_lt (w M i : ℕ) : bitField w M i < 2 ^ w :=
  Nat.mod_lt _ (Nat.two_pow_pos w)

@[simp]
theorem bitField_zero (w i : ℕ) : bitField w 0 i = 0 := by
  simp [bitField]

/-- The bits of a field: bit `k` of field `i` is bit `w * i + k` of `M`, for `k < w`. -/
theorem testBit_bitField (w M i k : ℕ) :
    (bitField w M i).testBit k = (decide (k < w) && M.testBit (w * i + k)) := by
  rw [bitField, testBit_mod_two_pow, testBit_div_two_pow, Nat.add_comm k]

/-- **Reading after writing.** Field `j` of `setBitField w M i v` is `v` if `j = i` and `v` fits
in `w` bits, and is field `j` of `M` otherwise. -/
@[simp]
theorem bitField_setBitField (w M i v j : ℕ) :
    bitField w (setBitField w M i v) j = if i = j ∧ v < 2 ^ w then v else bitField w M j := by
  unfold setBitField
  by_cases hv : v < 2 ^ w
  swap
  · simp [hv]
  simp only [hv, ↓reduceIte]
  -- The written difference `D` fits in `w` bits, so its shift only meets field `i`.
  have hD : (bitField w M i ^^^ v).testBit = fun p ↦ decide (p < w) &&
      (bitField w M i ^^^ v).testBit p := by
    funext p
    by_cases hp : p < w
    · simp [hp]
    · simp only [hp, decide_false, Bool.false_and]
      exact testBit_lt_two_pow (Nat.lt_of_lt_of_le (xor_lt_two_pow (bitField_lt w M i) hv)
        (Nat.pow_le_pow_right Nat.two_pos (by omega)))
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_bitField, testBit_xor, testBit_mul_two_pow, hD]
  by_cases hij : i = j
  · subst hij
    by_cases hk : k < w
    · simp [hk, testBit_bitField]
    · simp only [hk, decide_false, Bool.false_and, and_self, ↓reduceIte]
      exact (testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right Nat.two_pos
        (by omega)))).symm
  · simp only [hij, false_and, ↓reduceIte]
    rw [testBit_bitField]
    by_cases hk : k < w
    · rcases Nat.lt_or_gt_of_ne hij with h | h
      · -- Field `j` lies above field `i`.
        have : w * (i + 1) ≤ w * j := Nat.mul_le_mul_left w h
        have : ¬ w * j + k - w * i < w := by rw [Nat.mul_add, Nat.mul_one] at this; omega
        simp [this]
      · -- Field `j` lies below field `i`.
        have : w * (j + 1) ≤ w * i := Nat.mul_le_mul_left w h
        have : ¬ w * i ≤ w * j + k := by rw [Nat.mul_add, Nat.mul_one] at this; omega
        simp [this]
    · simp [hk]

end Nat
