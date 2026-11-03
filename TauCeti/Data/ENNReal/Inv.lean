/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Inv

/-!
# Division estimates in `ℝ≥0∞`

For `a ≤ b` in `ℝ≥0∞` the difference `1 - a / b` lies in `[0, 1]`, and it is read in `ℝ` as
`1 - a.toReal / b.toReal`; when `a < b` it is positive. With `a = n` the dimension and `b = p` an
integrability exponent, this is the Hölder exponent `1 - n / p` of Morrey's embedding, which is `1`
for `p = ∞`.

The file also records the absorption step of elliptic estimates: a finite quantity bounded by `b`
plus half of itself is at most `2 b`.

## Main declarations

* `ENNReal.toReal_one_sub_div`: `(1 - a / b).toReal = 1 - a.toReal / b.toReal` for `a ≤ b`.
* `ENNReal.toNNReal_one_sub_div_pos`: `0 < (1 - a / b).toNNReal` for `a < b`.
* `ENNReal.le_mul_two_of_le_add_div_two`: the absorption step `a ≤ b + a / 2 → a ≤ 2 b` for
  finite `a`, as used in elliptic estimates.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- For `a ≤ b`, the difference `1 - a / b` is read in `ℝ` as `1 - a.toReal / b.toReal`. -/
@[simp]
theorem toReal_one_sub_div {a b : ℝ≥0∞} (hab : a ≤ b) :
    (1 - a / b).toReal = 1 - a.toReal / b.toReal := by
  rw [toReal_sub_of_le (div_le_of_le_mul (by simpa using hab)) one_ne_top, toReal_div, toReal_one]

/-- For `a < b`, the difference `1 - a / b` is positive, even after truncation to `ℝ≥0`. -/
theorem toNNReal_one_sub_div_pos {a b : ℝ≥0∞} (hab : a < b) : 0 < (1 - a / b).toNNReal :=
  toNNReal_pos (tsub_pos_of_lt (div_lt_of_lt_mul (by simpa using hab))).ne'
    (sub_ne_top one_ne_top)

/-- **Absorption**: a finite quantity bounded by `b` plus half of itself is at most `2 b`. -/
theorem le_mul_two_of_le_add_div_two {a b : ℝ≥0∞} (ha : a ≠ ∞) (h : a ≤ b + a / 2) :
    a ≤ b * 2 := by
  have h' : a / 2 + a / 2 ≤ b + a / 2 := by rwa [ENNReal.add_halves]
  rw [← ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl ofNat_ne_top)]
  exact (ENNReal.add_le_add_iff_right (div_ne_top ha two_ne_zero)).1 h'

end ENNReal
