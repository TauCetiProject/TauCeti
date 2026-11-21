/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
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
* `Real.sqrt_bounds_of_abs_sub_le`: `√y / r ≤ √x ≤ r √y` when `|x - y| ≤ (1 - r⁻²) y`
  and `1 ≤ r`.
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

/-- A relative error at most `1 - r⁻²` bounds square roots within the factor `r ≥ 1`.
The reference value need not be assumed nonnegative. -/
theorem sqrt_bounds_of_abs_sub_le {x y r : ℝ} (hr : 1 ≤ r)
    (herror : |x - y| ≤ (1 - r⁻¹ ^ 2) * y) :
    sqrt y / r ≤ sqrt x ∧ sqrt x ≤ r * sqrt y := by
  rcases hr.eq_or_lt with h | hr
  · subst r
    have hxy : x = y := sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using herror))
    simp [hxy]
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hri : 0 < r⁻¹ := inv_pos.mpr hrpos
  have hri1 : r⁻¹ < 1 := (inv_lt_one₀ hrpos).mpr hr
  have hd : 0 < 1 - r⁻¹ ^ 2 := by
    nlinarith [(sq_lt_sq₀ hri.le zero_le_one).mpr hri1]
  have hy : 0 ≤ y := nonneg_of_mul_nonneg_right ((abs_nonneg _).trans herror) hd
  have hrinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hrpos.ne'
  have hmargin : 1 - r⁻¹ ^ 2 ≤ r ^ 2 - 1 := by nlinarith [sq_nonneg (r - r⁻¹)]
  have hupper : x ≤ (r * sqrt y) ^ 2 := by
    rw [mul_pow, sq_sqrt hy]
    nlinarith [(abs_le.mp herror).2, mul_le_mul_of_nonneg_right hmargin hy]
  have hlower : (sqrt y / r) ^ 2 ≤ x := by
    rw [div_pow, sq_sqrt hy, div_eq_mul_inv, ← inv_pow]
    nlinarith [(abs_le.mp herror).1]
  exact ⟨le_sqrt_of_sq_le hlower,
    sqrt_le_iff.mpr ⟨mul_nonneg hrpos.le (sqrt_nonneg _), hupper⟩⟩

private theorem sqrt_cubic_remainder_le {c h : ℝ} (hc : 0 ≤ c) :
    h ^ 3 * (4 * c + h) / (8 * c ^ 3) ≤ |h * (2 * c + h)| ^ 3 / c ^ 5 := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  rcases le_total h 0 with hh0 | hh0
  · by_cases hlow : -4 * c ≤ h
    · have hn : h ^ 3 * (4 * c + h) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg h]) (by linarith)
      exact (div_nonpos_of_nonpos_of_nonneg hn (by positivity)).trans (by positivity)
    · let t := -h - 4 * c
      have ht : 0 ≤ t := by dsimp [t]; linarith
      have heq : h = -(4 * c + t) := by dsimp [t]; ring
      have hprod : 0 ≤ h * (2 * c + h) :=
        mul_nonneg_of_nonpos_of_nonpos hh0 (by linarith)
      rw [abs_of_nonneg hprod, div_le_div_iff₀ (by positivity) (by positivity), heq]
      apply sub_nonneg.mp
      ring_nf
      positivity
  · rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    apply sub_nonneg.mp
    ring_nf
    positivity

/-- For any positive `c`, the square root is bounded above by its quadratic expansion at
`c ^ 2` plus the explicit cubic error `|y - c ^ 2| ^ 3 / c ^ 5`. -/
theorem sqrt_le_quadratic_add_cubic {y c : ℝ} (hc : 0 < c) :
    Real.sqrt y ≤ c + (y - c ^ 2) / (2 * c) -
      (y - c ^ 2) ^ 2 / (8 * c ^ 3) + |y - c ^ 2| ^ 3 / c ^ 5 := by
  by_cases hy : 0 ≤ y
  · set δ : ℝ := y - c ^ 2
    set h : ℝ := Real.sqrt y - c with hh
    have hs2 := Real.sq_sqrt hy
    have hδeq : δ = h * (2 * c + h) := by
      dsimp [δ, h]
      nlinarith only [hs2]
    have hid : h - δ / (2 * c) + δ ^ 2 / (8 * c ^ 3) =
        h ^ 3 * (4 * c + h) / (8 * c ^ 3) := by
      rw [hδeq]
      field_simp [hc.ne']
      ring
    have hrem := sqrt_cubic_remainder_le (h := h) hc.le
    rw [← hδeq, ← hid, hh] at hrem
    linarith only [hrem]
  · set u : ℝ := -y
    have hu0 : 0 ≤ u := by dsimp [u]; linarith
    have hyu : y = -u := by dsimp [u]; ring
    rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hy), hyu,
      abs_of_nonpos (by nlinarith [sq_nonneg c])]
    have heq : c + (-u - c ^ 2) / (2 * c) - (-u - c ^ 2) ^ 2 / (8 * c ^ 3) +
        (-(-u - c ^ 2)) ^ 3 / c ^ 5 =
        (11 * c ^ 6 + 18 * c ^ 4 * u + 23 * c ^ 2 * u ^ 2 + 8 * u ^ 3) /
          (8 * c ^ 5) := by field_simp [hc.ne']; ring
    rw [heq]
    positivity

private theorem sqrt_linear_error {d c C r δ a q : ℝ} (hd : 0 < d) (hdc : d ≤ c)
    (he : |δ - a - q / 2| ≤ C * r ^ 3) :
    δ / (2 * c) ≤ a / (2 * c) + q / (4 * c) + (C / d) * r ^ 3 := by
  have hc : 0 < c := hd.trans_le hdc
  have h := div_le_div_of_nonneg_right ((le_abs_self _).trans he)
    (by positivity : 0 ≤ 2 * c)
  have hb : C * r ^ 3 / (2 * c) ≤ (C / d) * r ^ 3 := by
    calc
      C * r ^ 3 / (2 * c) ≤ C * r ^ 3 / d :=
        div_le_div_of_nonneg_left ((abs_nonneg _).trans he) hd (by linarith)
      _ = (C / d) * r ^ 3 := by ring
  have heq : (δ - a - q / 2) / (2 * c) =
      δ / (2 * c) - a / (2 * c) - q / (4 * c) := by field_simp [hc.ne']; ring
  rw [heq] at h
  linarith

private theorem sqrt_square_error {d c D L Q C r δ a q : ℝ}
    (hd : 0 < d) (hdc : d ≤ c) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : |a| ≤ L * r) (hq : |q| ≤ Q * r ^ 2)
    (hδ : |δ| ≤ D * r) (he : |δ - a - q / 2| ≤ C * r ^ 3) :
    -(δ ^ 2 / (8 * c ^ 3)) ≤ -(a ^ 2 / (8 * c ^ 3)) +
      ((Q + C) * (D + L) / d ^ 3) * r ^ 3 := by
  by_cases hr0 : r = 0
  · have ha0 : a = 0 := abs_nonpos_iff.mp (by simpa only [hr0, mul_zero] using ha)
    have hδ0 : δ = 0 := abs_nonpos_iff.mp (by simpa only [hr0, mul_zero] using hδ)
    simp [hr0, ha0, hδ0]
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans he) (pow_pos hrpos 3)
  have hc : 0 < c := hd.trans_le hdc
  have hr32 : r ^ 3 ≤ r ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)]
  have hminus : |δ - a| ≤ (Q + C) * r ^ 2 := by
    calc
      |δ - a| = |(δ - a - q / 2) + q / 2| := by congr 1; ring
      _ ≤ |δ - a - q / 2| + |q / 2| := abs_add_le _ _
      _ ≤ C * r ^ 3 + Q * r ^ 2 / 2 := by
        simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
          add_le_add he (by gcongr)
      _ ≤ (Q + C) * r ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hr32 hC, (abs_nonneg q).trans hq]
  have hplus : |δ + a| ≤ (D + L) * r := by
    calc
      |δ + a| ≤ |δ| + |a| := abs_add_le _ _
      _ ≤ D * r + L * r := add_le_add hδ ha
      _ = (D + L) * r := by ring
  have hsquare : |δ ^ 2 - a ^ 2| ≤ (Q + C) * (D + L) * r ^ 3 := by
    calc
      |δ ^ 2 - a ^ 2| = |δ - a| * |δ + a| := by rw [← abs_mul]; congr 1; ring
      _ ≤ ((Q + C) * r ^ 2) * ((D + L) * r) :=
        mul_le_mul hminus hplus (abs_nonneg _) ((abs_nonneg _).trans hminus)
      _ = (Q + C) * (D + L) * r ^ 3 := by ring
  have hnum : a ^ 2 - δ ^ 2 ≤ (Q + C) * (D + L) * r ^ 3 :=
    (le_abs_self _).trans (by simpa only [abs_sub_comm] using hsquare)
  have hden : d ^ 3 ≤ 8 * c ^ 3 := by
    nlinarith [pow_le_pow_left₀ hd.le hdc 3, pow_nonneg hc.le 3]
  have hfrac := div_le_div₀ ((abs_nonneg _).trans hsquare) hnum
    (by positivity : 0 < d ^ 3) hden
  rw [sub_div] at hfrac
  have heq : (Q + C) * (D + L) * r ^ 3 / d ^ 3 =
      ((Q + C) * (D + L) / d ^ 3) * r ^ 3 := by ring
  rw [heq] at hfrac
  linarith only [hfrac]

private theorem sqrt_expansion_bound {d c D L Q C r y a q : ℝ}
    (hd : 0 < d) (hdc : d ≤ c) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : |a| ≤ L * r) (hq : |q| ≤ Q * r ^ 2)
    (hδ : |y - c ^ 2| ≤ D * r) (he : |y - c ^ 2 - a - q / 2| ≤ C * r ^ 3) :
    Real.sqrt y ≤ c + a / (2 * c) + q / (4 * c) - a ^ 2 / (8 * c ^ 3) +
      (D ^ 3 / d ^ 5 + C / d + (Q + C) * (D + L) / d ^ 3) * r ^ 3 := by
  have hc : 0 < c := hd.trans_le hdc
  by_cases hr0 : r = 0
  · have ha0 : a = 0 := abs_nonpos_iff.mp (by simpa only [hr0, mul_zero] using ha)
    have hq0 : q = 0 := abs_nonpos_iff.mp (by simpa [hr0] using hq)
    have hy : y = c ^ 2 := sub_eq_zero.mp
      (abs_nonpos_iff.mp (by simpa only [hr0, mul_zero] using hδ))
    simp [hr0, ha0, hq0, hy, Real.sqrt_sq hc.le]
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hD : 0 ≤ D := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans hδ) hrpos
  have hsqrt := Real.sqrt_le_quadratic_add_cubic (y := y) hc
  have hcubic : |y - c ^ 2| ^ 3 / c ^ 5 ≤ (D ^ 3 / d ^ 5) * r ^ 3 := by
    calc
      |y - c ^ 2| ^ 3 / c ^ 5 ≤ (D * r) ^ 3 / d ^ 5 := by gcongr
      _ = (D ^ 3 / d ^ 5) * r ^ 3 := by ring
  have hlinear := sqrt_linear_error hd hdc he
  have hnegative := sqrt_square_error hd hdc hr hr1 ha hq hδ he
  linarith

/-- Uniform bounds for the linear and quadratic coefficients give a common cubic error for a
one-sided square-root expansion. The expansion scale is at least the positive number `d`, and
the displacement size `r` is at most one. -/
theorem exists_forall_sqrt_le_quadratic_add_cubic (d L₀ Q₀ C₀ : ℝ) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c y a q r : ℝ, d ≤ c → 0 ≤ r → r ≤ 1 →
      |a| ≤ L₀ * r → |q| ≤ Q₀ * r ^ 2 →
      y ≤ c ^ 2 + a + q / 2 + C₀ * r ^ 3 →
      Real.sqrt y ≤ c + a / (2 * c) + q / (4 * c) - a ^ 2 / (8 * c ^ 3) + C * r ^ 3 := by
  let L := max L₀ 0
  let Q := max Q₀ 0
  let B := max C₀ 0
  let D := L + Q + B + 1
  have hL : 0 ≤ L := le_max_right _ _
  have hQ : 0 ≤ Q := le_max_right _ _
  have hB : 0 ≤ B := le_max_right _ _
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D ^ 3 / d ^ 5 + B / d + (Q + B) * (D + L) / d ^ 3,
    add_nonneg (add_nonneg (div_nonneg (pow_nonneg hD.le 3) (pow_nonneg hd.le 5))
      (div_nonneg hB hd.le))
      (div_nonneg (mul_nonneg (add_nonneg hQ hB) (add_nonneg hD.le hL))
        (pow_nonneg hd.le 3)), ?_⟩
  intro c y a q r hdc hr hr1 ha hq hy
  have ha' : |a| ≤ L * r := ha.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)
  have hq' : |q| ≤ Q * r ^ 2 :=
    hq.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  let z := c ^ 2 + a + q / 2 + B * r ^ 3
  have hyz : y ≤ z := hy.trans (by dsimp [z]; gcongr; exact le_max_left _ _)
  have he : |z - c ^ 2 - a - q / 2| ≤ B * r ^ 3 := by
    -- Expand the local majorant to identify its remainder before removing the absolute value.
    rw [show z - c ^ 2 - a - q / 2 = B * r ^ 3 by dsimp [z]; ring,
      abs_of_nonneg (by positivity)]
  have hr2 : r ^ 2 ≤ r := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1)]
  have hr3 : r ^ 3 ≤ r := by nlinarith [mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)]
  have hδ : |z - c ^ 2| ≤ D * r := by
    calc
      |z - c ^ 2| = |(z - c ^ 2 - a - q / 2) + a + q / 2| := by congr 1; ring
      _ ≤ |z - c ^ 2 - a - q / 2| + |a| + |q / 2| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ B * r ^ 3 + L * r + Q * r ^ 2 / 2 := by
        simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
          add_le_add (add_le_add he ha') (by gcongr)
      _ ≤ D * r := by
        dsimp [D]
        nlinarith [mul_le_mul_of_nonneg_left hr2 hQ, mul_le_mul_of_nonneg_left hr3 hB]
  exact (Real.sqrt_le_sqrt hyz).trans
    (sqrt_expansion_bound hd hdc hr hr1 ha' hq' hδ he)

end Real
