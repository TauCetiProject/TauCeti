/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Inv
import Mathlib.Tactic.Linarith
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
* `ENNReal.toReal_of_inv_add_inv_eq`: the real exponents of Young's inequality
  `1/p + 1/r = 1 + 1/q` with `1 ≤ p, r` and `q < ∞` are finite, with `1 ≤ p ≤ q`.
* `ENNReal.le_mul_two_of_le_add_div_two`: the absorption step `a ≤ b + a / 2 → a ≤ 2 b` for
  finite `a`, as used in elliptic estimates.
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
  rw [← ENNReal.div_le_iff two_ne_zero ofNat_ne_top, ← ENNReal.sub_half ha]
  exact tsub_le_iff_right.2 h

/-- **A finite exponent `t ≥ 2` complementing `r`.** For `n > 0` and `r > 1` with
`n (2 - r) < 2 r`, there is a finite exponent `t ≥ 2` with `1/2 - 1/t < 1/n` and `1/r + 1/t ≤ 1`:
take `1/t = min (1/2) (1 - 1/r)`. -/
theorem exists_nnreal_two_le_inv_sub_lt_and_inv_add_le_one {n : ℝ} (hn : 0 < n) {r : ℝ≥0}
    (hr : 1 < r) (hrn : n * (2 - r) < 2 * r) :
    ∃ t : ℝ≥0, 0 < t ∧ (2 : ℝ≥0∞) ≤ t ∧ 2⁻¹ - (t : ℝ)⁻¹ < n⁻¹ ∧
      (r : ℝ)⁻¹ + (t : ℝ)⁻¹ ≤ 1 := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have h2r : (r : ℝ)⁻¹ < 2⁻¹ + n⁻¹ := by
    field_simp
    linarith
  set τ : ℝ := min 2⁻¹ (1 - (r : ℝ)⁻¹)
  have hτ0 : 0 < τ := lt_min (by norm_num) (sub_pos.2 (inv_lt_one_of_one_lt₀ hr1))
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ)⁻¹ = τ :=
    ⟨τ⁻¹.toNNReal, by rw [Real.coe_toNNReal _ (inv_nonneg.2 hτ0.le), inv_inv]⟩
  have ht0 : (0 : ℝ) < t := inv_pos.1 (ht ▸ hτ0)
  refine ⟨t, mod_cast ht0, ?_, ht ▸ sub_lt_comm.1 (lt_min ?_ ?_),
    ht ▸ le_sub_iff_add_le'.1 (min_le_right _ _)⟩
  · have : (2 : ℝ) ≤ t := by rw [← inv_le_inv₀ ht0 two_pos, ht]; exact min_le_left _ _
    exact_mod_cast this
  · linarith [inv_pos.2 hn]
  · linarith

/-- The real exponents of Young's inequality: if `1 ≤ p`, `1 ≤ r` and `1/p + 1/r = 1 + 1/q` with
`q < ∞`, then `p` and `r` are finite, `q` is positive, and the relation holds between the real
exponents, with `1 ≤ p ≤ q`. -/
theorem toReal_of_inv_add_inv_eq {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hpqr : p⁻¹ + r⁻¹ = 1 + q⁻¹) (hq : q ≠ ∞) :
    p ≠ ∞ ∧ r ≠ ∞ ∧ q ≠ 0 ∧ 1 ≤ p.toReal ∧ p.toReal ≤ q.toReal ∧
      p.toReal⁻¹ + r.toReal⁻¹ = 1 + q.toReal⁻¹ := by
  have hp1 : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hp
  have hr1 : r⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hr
  have hq0 : q⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hq
  have hp_top : p ≠ ∞ := by
    rintro rfl
    rw [ENNReal.inv_top, zero_add] at hpqr
    have : 1 + q⁻¹ ≤ 1 + 0 := by rw [add_zero, ← hpqr]; exact hr1
    exact hq0 (nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 this))
  have hr_top : r ≠ ∞ := by
    rintro rfl
    rw [ENNReal.inv_top, add_zero] at hpqr
    have : 1 + q⁻¹ ≤ 1 + 0 := by rw [add_zero, ← hpqr]; exact hp1
    exact hq0 (nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 this))
  have hqp : q⁻¹ ≤ p⁻¹ := by
    have : 1 + q⁻¹ ≤ 1 + p⁻¹ := by
      rw [← hpqr, add_comm]
      gcongr
    exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 this
  have hq_ne : q ≠ 0 := by
    rintro rfl
    rw [ENNReal.inv_zero] at hpqr
    exact ENNReal.add_ne_top.2 ⟨(hp1.trans_lt ENNReal.one_lt_top).ne,
      (hr1.trans_lt ENNReal.one_lt_top).ne⟩ (hpqr.trans (by simp))
  refine ⟨hp_top, hr_top, hq_ne, by simpa using ENNReal.toReal_mono hp_top hp,
    ENNReal.toReal_mono hq (ENNReal.inv_le_inv.1 hqp), ?_⟩
  have h := congrArg ENNReal.toReal hpqr
  rwa [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hp).ne')
      (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hr).ne'),
    ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.inv_ne_top.2 hq_ne), ENNReal.toReal_inv,
    ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at h

end ENNReal
