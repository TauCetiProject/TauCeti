/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination

/-!
# Rescaling by a square root

For `0 ≤ a`, multiplying by `(√a)⁻¹` and squaring divides the square by `a`:
`((√a)⁻¹ * x) ^ 2 = x ^ 2 / a`. This is the change of variables `x ↦ (√a)⁻¹ * x` that turns the
kernel `1 + x ^ 2 / a` into `1 + y ^ 2`. A square factor comes out of a square root as its
absolute value: `√(x ^ 2 * y) = |x| * √y`. Doubling the argument does not decrease the square
root, with no sign hypothesis since `√x = 0` for `x ≤ 0`. Powers of `(√a)⁻¹` absorb integer
powers of `a`: `(√a)⁻¹ ^ n * a ^ p = (√a)⁻¹ ^ (n - 2p)` for `a > 0` and `2p ≤ n`, the
normalisation that leaves a factor `(√N)⁻¹ ^ (n - 2p)` in a central limit theorem.

The rational square-root map `k ↦ 2√k / (1 + k)` has complementary square
`((1 - k) / (1 + k))²` and inverts `k ↦ (1 - √(1 - k²)) / (1 + √(1 - k²))` up to sign.
These identities are used by both kinds of complete elliptic integral in Landen's transformation.
For `|t| ≤ 1`, the square of `√(1 - t²)` is `1 - t²`; for any nonzero `t`, this square
is strictly less than `1`. In particular, for nonnegative ordered inputs `0 ≤ b ≤ a`,
squaring `√(1 - (b / a)²)` recovers its argument, as needed for AGM evaluations. For
`t ∈ (-1, 1)` the square root `√(1 - t²)` itself is positive.

A real number `x` of the same sign as `c` is rescaled to `c` by the positive square of
`√(c / x)`. For `0 ≤ t < √2 - 1`, completing `(t + 1)² < 2` bounds the quadratic majorant
`2 t + t² < 1`.

For nonnegative `a` and `b`, the geometric mean is at most the arithmetic mean,
`√(ab) ≤ (a + b) / 2`, as `NNReal.sqrt_mul_le_half_add` states in `ℝ≥0`, and the square of
`√a - √b` expands to `a + b - 2√(ab)`.

## Main results

* `Real.inv_sqrt_mul_sq`: `((√a)⁻¹ * x) ^ 2 = x ^ 2 / a` for `0 ≤ a`.
* `Real.sqrt_sq_mul`: `√(x ^ 2 * y) = |x| * √y`.
* `Real.sqrt_le_sqrt_two_mul`: `√x ≤ √(2 * x)`.
* `Real.inv_sqrt_pow_mul_pow`: `(√a)⁻¹ ^ n * a ^ p = (√a)⁻¹ ^ (n - 2p)` for `0 < a` and `2p ≤ n`.
* `Real.one_sub_sq_two_mul_sqrt_div_one_add`: the complementary square of `2√k / (1 + k)`.
* `Real.sq_two_mul_sqrt_div_one_add_lt_one`: this square is less than `1` for `k ≠ 1`.
* `Real.two_mul_sqrt_div_one_add_eq_abs`: the two rational square-root transformations
  compose to the absolute value on `[-1, 1]`.
* `Real.sq_sqrt_one_sub_sq`: `√(1 - t²)² = 1 - t²` for `|t| ≤ 1`.
* `Real.sq_sqrt_one_sub_sq_div`: the same identity for `t = b / a` when `0 ≤ b ≤ a`.
* `Real.sq_sqrt_one_sub_sq_lt_one`: `√(1 - t²)² < 1` for nonzero `t`.
* `Real.sqrt_one_sub_sq_pos`: `0 < √(1 - t²)` for `t ∈ (-1, 1)`.
* `Real.exists_pos_sq_mul_eq_of_mul_pos`: `μ ^ 2 * x = c` for some `μ > 0` when `0 < c * x`.
* `Real.two_mul_add_sq_lt_one`: `2 * t + t ^ 2 < 1` for `0 ≤ t < √2 - 1`.
* `Real.sqrt_mul_le_half_add`: `√(ab) ≤ (a + b) / 2` for `0 ≤ a` and `0 ≤ b`.
* `Real.sq_sqrt_sub_sqrt`: `(√a - √b)² = a + b - 2√(ab)` for `0 ≤ a` and `0 ≤ b`.
-/

public section

namespace Real

/-- For `0 ≤ a` and `0 ≤ t`, if `t < |a - √r|`, then both `√r * t` and `t ^ 2`
are strictly less than `|a ^ 2 - r|`. No sign hypothesis on `r` is required. -/
theorem max_sqrt_mul_sq_lt_abs_sq_sub {a r t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (h : t < |a - √r|) : max (√r * t) (t ^ 2) < |a ^ 2 - r| := by
  rcases le_total 0 r with hr | hr
  swap
  · rw [sqrt_eq_zero_of_nonpos hr]
    simp only [sqrt_eq_zero_of_nonpos hr, sub_zero, abs_of_nonneg ha] at h
    rw [abs_of_nonneg (by nlinarith : 0 ≤ a ^ 2 - r)]
    simp only [zero_mul, max_eq_right (sq_nonneg t)]
    nlinarith [mul_self_lt_mul_self ht h]
  have hab : |a - √r| ≤ a + √r :=
    abs_le.mpr ⟨by linarith, by nlinarith [sqrt_nonneg r]⟩
  have heq : |a ^ 2 - r| = |a - √r| * (a + √r) := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ a + √r), ← abs_mul]
    congr 1
    nlinarith [sq_sqrt hr]
  rw [heq]
  refine max_lt_iff.mpr ⟨?_, ?_⟩
  · by_cases hr0 : r = 0
    · simp only [hr0, sqrt_zero, zero_mul, add_zero, sub_zero, abs_of_nonneg ha] at h ⊢
      have ha' : 0 < a := ht.trans_lt h
      positivity
    · simpa only [mul_comm] using
        (mul_lt_mul_of_pos_right h (sqrt_pos.mpr (lt_of_le_of_ne hr (Ne.symm hr0)))).trans_le
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ha) (abs_nonneg (a - √r)))
  · nlinarith [mul_self_lt_mul_self ht h,
      mul_le_mul_of_nonneg_left hab (abs_nonneg (a - √r))]


/-- Multiplying by `(√a)⁻¹` and squaring divides the square by `a`. -/
@[simp]
theorem inv_sqrt_mul_sq {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : ((√a)⁻¹ * x) ^ 2 = x ^ 2 / a := by
  rw [mul_pow, inv_pow, sq_sqrt ha, inv_mul_eq_div]

/-- A square factor comes out of a square root as its absolute value. -/
theorem sqrt_sq_mul (x y : ℝ) : √(x ^ 2 * y) = |x| * √y := by
  rw [sqrt_mul (sq_nonneg _), sqrt_sq_eq_abs]

/-- Doubling the argument does not decrease the square root. There is no sign hypothesis: both
sides vanish when `x ≤ 0`. -/
theorem sqrt_le_sqrt_two_mul (x : ℝ) : √x ≤ √(2 * x) := by
  rcases le_total 0 x with h | h
  · exact sqrt_le_sqrt (by linarith)
  · rw [sqrt_eq_zero_of_nonpos h]
    positivity

/-- Powers of `(√a)⁻¹` absorb powers of `a`: `(√a)⁻¹ ^ n * a ^ p = (√a)⁻¹ ^ (n - 2p)` for
`0 < a` and `2p ≤ n`. -/
theorem inv_sqrt_pow_mul_pow {a : ℝ} (ha : 0 < a) {n p : ℕ} (h : 2 * p ≤ n) :
    (√a)⁻¹ ^ n * a ^ p = (√a)⁻¹ ^ (n - 2 * p) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have ha' : a ^ p = √a ^ (2 * p) := by rw [pow_mul, sq_sqrt ha.le]
  rw [Nat.add_sub_cancel_left, ha', pow_add, mul_right_comm, ← mul_pow,
    inv_mul_cancel₀ (sqrt_pos.2 ha).ne', one_pow, one_mul]

/-- The complementary square of `2√k / (1 + k)` is `((1 - k) / (1 + k))²`. -/
theorem one_sub_sq_two_mul_sqrt_div_one_add {k : ℝ} (hk : 0 ≤ k) :
    1 - (2 * √k / (1 + k)) ^ 2 = ((1 - k) / (1 + k)) ^ 2 := by
  field_simp
  rw [sq_sqrt hk]
  ring

/-- For `k ≠ 1`, the square of `2√k / (1 + k)` is strictly less than `1`. For negative `k` it is
`0`, since `√k = 0`. -/
theorem sq_two_mul_sqrt_div_one_add_lt_one {k : ℝ} (hk₁ : k ≠ 1) :
    (2 * √k / (1 + k)) ^ 2 < 1 := by
  rcases lt_or_ge k 0 with hk | hk₀
  · rw [sqrt_eq_zero_of_nonpos hk.le]
    norm_num
  have hp : 0 < 1 + k := by linarith
  have hne : (1 - k) / (1 + k) ≠ 0 := div_ne_zero (sub_ne_zero.2 hk₁.symm) hp.ne'
  have hsq := one_sub_sq_two_mul_sqrt_div_one_add hk₀
  linarith [sq_pos_of_ne_zero hne]

/-- For `k² ≤ 1`, applying `x ↦ 2√x / (1 + x)` to
`(1 - √(1 - k²)) / (1 + √(1 - k²))` gives `|k|`. -/
theorem two_mul_sqrt_div_one_add_eq_abs {k : ℝ} (hk : k ^ 2 ≤ 1) :
    2 * √((1 - √(1 - k ^ 2)) / (1 + √(1 - k ^ 2))) /
      (1 + (1 - √(1 - k ^ 2)) / (1 + √(1 - k ^ 2))) = |k| := by
  set c := √(1 - k ^ 2)
  have hc : 0 ≤ c := sqrt_nonneg _
  have hc₁ : c ≤ 1 := sqrt_le_one.2 (by nlinarith)
  have hcsq : c ^ 2 = 1 - k ^ 2 := sq_sqrt (by linarith)
  have hp : 0 < 1 + c := by linarith
  have hq : 0 ≤ (1 - c) / (1 + c) := div_nonneg (by linarith) hp.le
  have hnn : 0 ≤ 2 * √((1 - c) / (1 + c)) / (1 + (1 - c) / (1 + c)) := by
    positivity
  rw [← sqrt_sq_eq_abs, ← sqrt_sq hnn]
  congr 1
  rw [div_pow, mul_pow, sq_sqrt hq]
  field_simp
  linear_combination -4 * hcsq

/-- For `|t| ≤ 1`, squaring `√(1 - t²)` recovers its argument. -/
theorem sq_sqrt_one_sub_sq {t : ℝ} (ht : |t| ≤ 1) : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := by
  have : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  exact sq_sqrt (by linarith)

/-- For nonnegative ordered inputs, squaring `√(1 - (b / a)²)` recovers its argument. -/
theorem sq_sqrt_one_sub_sq_div {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    (√(1 - (b / a) ^ 2)) ^ 2 = 1 - (b / a) ^ 2 := by
  by_cases ha : a = 0
  · simp [ha]
  have ha' : 0 < a := lt_of_le_of_ne (hb.trans hba) (Ne.symm ha)
  have hratio : 0 ≤ b / a := div_nonneg hb ha'.le
  have hle : b / a ≤ 1 := (div_le_one ha').2 hba
  exact sq_sqrt_one_sub_sq (by rwa [abs_of_nonneg hratio])

/-- For any nonzero real input, the square of `√(1 - t²)` is less than `1`. -/
theorem sq_sqrt_one_sub_sq_lt_one {t : ℝ} (ht : t ≠ 0) :
    (√(1 - t ^ 2)) ^ 2 < 1 := by
  rw [sq_sqrt']
  exact max_lt (by nlinarith [sq_pos_of_ne_zero ht]) zero_lt_one

/-- For `t ∈ (-1, 1)`, the square root `√(1 - t²)` is positive. -/
theorem sqrt_one_sub_sq_pos {t : ℝ} (ht : t ∈ Set.Ioo (-1) 1) : 0 < √(1 - t ^ 2) :=
  sqrt_pos.2 (by nlinarith [ht.1, ht.2])

/-- A value `x` of the same sign as `c` can be rescaled to `c` by a positive square. -/
theorem exists_pos_sq_mul_eq_of_mul_pos {c x : ℝ} (h : 0 < c * x) :
    ∃ μ : ℝ, 0 < μ ∧ μ ^ 2 * x = c := by
  have hcx : 0 < c / x := div_pos_iff.2 (mul_pos_iff.1 h)
  have hx : x ≠ 0 := by rintro rfl; simp at h
  refine ⟨√(c / x), sqrt_pos.2 hcx, ?_⟩
  rw [sq_sqrt hcx.le]
  field_simp

/-- Whenever `0 ≤ t < √2 - 1`, the quadratic majorant `2 * t + t ^ 2` is strictly less than `1`. -/
theorem two_mul_add_sq_lt_one {t : ℝ} (ht₀ : 0 ≤ t) (ht : t < √2 - 1) :
    2 * t + t ^ 2 < 1 := by
  have hlt : t + 1 < √2 := by linarith
  have hsq : (t + 1) ^ 2 < √2 ^ 2 := pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
  rw [sq_sqrt zero_le_two] at hsq
  linarith

/-- For nonnegative `a`, `b`, the geometric mean is at most the arithmetic mean:
`√(ab) ≤ (a + b) / 2`. This is `NNReal.sqrt_mul_le_half_add` for real numbers. -/
theorem sqrt_mul_le_half_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    √(a * b) ≤ (a + b) / 2 :=
  sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (a - b)]⟩

/-- For nonnegative `a`, `b`, `(√a - √b)² = a + b - 2 √(ab)`. -/
theorem sq_sqrt_sub_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (√a - √b) ^ 2 = a + b - 2 * √(a * b) := by
  rw [sub_sq, sq_sqrt ha, sq_sqrt hb, sqrt_mul ha]
  ring

end Real
