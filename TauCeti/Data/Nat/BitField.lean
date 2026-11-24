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
* `Nat.bitField_mul_of_forall_bitField_mul_lt`: multiplication by `r` acts on a field as long as
  neither it nor a lower field overflows.
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
  mod_lt _ (Nat.two_pow_pos w)

@[simp]
theorem bitField_zero (w i : ℕ) : bitField w 0 i = 0 := by
  simp [bitField]

/-- The bits of a field: bit `k` of field `i` is bit `w * i + k` of `M`, for `k < w`. -/
theorem testBit_bitField (w M i k : ℕ) :
    (bitField w M i).testBit k = (decide (k < w) && M.testBit (w * i + k)) := by
  rw [bitField, testBit_mod_two_pow, testBit_div_two_pow, add_comm k]

/-- Field `i + 1` of `M` is field `i` of `M / 2 ^ w`: dividing by `2 ^ w` drops the lowest
field. -/
theorem bitField_succ (w M i : ℕ) : bitField w M (i + 1) = bitField w (M / 2 ^ w) i := by
  rw [bitField, bitField, Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_succ, Nat.add_comm]

/-- **Multiplication without carries.** If each of the fields `0, …, i` of `M`, multiplied by `r`,
still fits in `w` bits, then field `i` of `M * r` is field `i` of `M` multiplied by `r`. -/
theorem bitField_mul_of_forall_bitField_mul_lt {w M r i : ℕ}
    (h : ∀ j ≤ i, bitField w M j * r < 2 ^ w) :
    bitField w (M * r) i = bitField w M i * r := by
  induction i generalizing M with
  | zero =>
    have h0 := h 0 le_rfl
    simp only [bitField, Nat.mul_zero, pow_zero, Nat.div_one] at h0 ⊢
    exact (Nat.mod_mul_mod M r (2 ^ w)).symm.trans (Nat.mod_eq_of_lt h0)
  | succ i ih =>
    have h0 := h 0 (Nat.zero_le _)
    simp only [bitField, Nat.mul_zero, pow_zero, Nat.div_one] at h0
    have hdiv : M * r / 2 ^ w = M / 2 ^ w * r := by
      conv_lhs => rw [← Nat.mod_add_div M (2 ^ w), Nat.add_mul, Nat.mul_assoc]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt h0, Nat.zero_add]
    rw [bitField_succ, hdiv,
      ih fun j hj ↦ by simpa [bitField_succ] using h (j + 1) (Nat.succ_le_succ hj), bitField_succ]

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
      exact testBit_lt_two_pow (lt_of_lt_of_le (xor_lt_two_pow (bitField_lt w M i) hv)
        (Nat.pow_le_pow_right Nat.two_pos (by omega)))
  apply eq_of_testBit_eq
  intro k
  rw [testBit_bitField, testBit_xor, testBit_mul_two_pow, hD]
  by_cases hij : i = j
  · subst hij
    by_cases hk : k < w
    · simp [hk, testBit_bitField]
    · simp only [hk, decide_false, Bool.false_and, and_self, ↓reduceIte]
      exact (testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right Nat.two_pos
        (by omega)))).symm
  · simp only [hij, false_and, ↓reduceIte]
    rw [testBit_bitField]
    by_cases hk : k < w
    · rcases lt_or_gt_of_ne hij with h | h
      · -- Field `j` lies above field `i`.
        have : w * (i + 1) ≤ w * j := mul_le_mul_left w h
        have : ¬ w * j + k - w * i < w := by rw [mul_add, mul_one] at this; omega
        simp [this]
      · -- Field `j` lies below field `i`.
        have : w * (j + 1) ≤ w * i := mul_le_mul_left w h
        have : ¬ w * i ≤ w * j + k := by rw [mul_add, mul_one] at this; omega
        simp [this]
    · simp [hk]

end Nat
