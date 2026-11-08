/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

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
* `ENNReal.exists_nnreal_two_le_inv_sub_lt_and_inv_add_le_one`: for `r > 1` and `n > 0` with
  `n (2 - r) < 2 r`, a finite exponent `t ≥ 2` with `1/2 - 1/t < 1/n` and `1/r + 1/t ≤ 1`.
* `ENNReal.le_mul_two_of_le_add_div_two`: the absorption step `a ≤ b + a / 2 → a ≤ 2 b` for
  finite `a`, as used in elliptic estimates.
* `ENNReal.ofReal_pow_div_natCast_div_mul_ofReal_natCast_mul`: the cancellation
  `ofReal (d ^ n / n) / m * ofReal (n * a) = ofReal (a * d ^ n / m.toReal)` for `m` finite and
  nonzero.
-/

public section

open scoped ENNReal NNReal

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

/-- **A finite exponent `t ≥ 2` complementing `r`.** For `n > 0` and `r > 1` with
`n (2 - r) < 2 r`, there is a finite exponent `t ≥ 2` with `1/2 - 1/t < 1/n` and `1/r + 1/t ≤ 1`:
take `1/t = min (1/2) (1 - 1/r)`. -/
theorem exists_nnreal_two_le_inv_sub_lt_and_inv_add_le_one {n : ℝ} (hn : 0 < n) {r : ℝ≥0}
    (hr : 1 < r) (hrn : n * (2 - r) < 2 * r) :
    ∃ t : ℝ≥0, 0 < t ∧ (2 : ℝ≥0∞) ≤ t ∧ 2⁻¹ - (t : ℝ)⁻¹ < n⁻¹ ∧
      (r : ℝ)⁻¹ + (t : ℝ)⁻¹ ≤ 1 := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  set τ : ℝ := min 2⁻¹ (1 - (r : ℝ)⁻¹)
  have hrinv : (r : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hτ0 : 0 < τ := lt_min (by norm_num) (by linarith)
  have hτ2 : τ ≤ 2⁻¹ := min_le_left _ _
  have hτr : τ ≤ 1 - (r : ℝ)⁻¹ := min_le_right _ _
  have hτn : 2⁻¹ - τ < n⁻¹ := by
    have hn0 : 0 < n⁻¹ := inv_pos.2 hn
    have h2r : (r : ℝ)⁻¹ < 2⁻¹ + n⁻¹ := by
      rw [← sub_pos, show (2⁻¹ + n⁻¹ - (r : ℝ)⁻¹) = (2 * r - n * (2 - r)) / (2 * n * r) by
        field_simp; ring]
      exact div_pos (by linarith) (by positivity)
    have : 2⁻¹ - n⁻¹ < τ := lt_min (by linarith) (by linarith)
    linarith
  set t : ℝ≥0 := Real.toNNReal τ⁻¹
  have ht : (t : ℝ) = τ⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 hτ0.le)
  have ht0 : (0 : ℝ) < t := by rw [ht]; positivity
  have h2t : (2 : ℝ≥0∞) ≤ t := by
    have : (2 : ℝ) ≤ t := by
      rw [ht, le_inv_comm₀ two_pos hτ0]
      exact hτ2
    exact_mod_cast this
  exact ⟨t, by exact_mod_cast ht0, h2t, by rwa [ht, inv_inv], by rw [ht, inv_inv]; linarith⟩

/-- Cancelling a finite nonzero denominator `m` against the factor `n` of a product:
`ofReal (d ^ n / n) / m * ofReal (n * a) = ofReal (a * d ^ n / m)`. -/
theorem ofReal_pow_div_natCast_div_mul_ofReal_natCast_mul {n : ℕ} {d a : ℝ} {m : ℝ≥0∞}
    (hn : 0 < n) (hd : 0 ≤ d) (hm₀ : m ≠ 0) (hm_top : m ≠ ∞) :
    ENNReal.ofReal (d ^ n / n) / m * ENNReal.ofReal (n * a) =
      ENNReal.ofReal (a * d ^ n / m.toReal) := by
  have hmpos : 0 < m.toReal := toReal_pos hm₀ hm_top
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  conv_lhs => rw [← ofReal_toReal hm_top]
  rw [← ENNReal.ofReal_div_of_pos hmpos, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end ENNReal
