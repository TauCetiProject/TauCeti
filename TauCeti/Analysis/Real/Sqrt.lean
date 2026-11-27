/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.LinearCombination

/-!
# Elementary square-root identities and inequalities

For `0 ≤ a`, multiplying by `(√a)⁻¹` and squaring divides the square by `a`:
`((√a)⁻¹ * x) ^ 2 = x ^ 2 / a`. This is the change of variables `x ↦ (√a)⁻¹ * x` that turns the
kernel `1 + x ^ 2 / a` into `1 + y ^ 2`. A square factor comes out of a square root as its
absolute value: `√(x ^ 2 * y) = |x| * √y`, so a nonnegative factor `y` comes out against the
quotient by it: `√(x * y) = y * √(x / y)`. Conjugating `t` by `√(u / t)` recovers `u`.
Doubling the argument does not decrease the square root, with no sign hypothesis since `√x = 0`
for `x ≤ 0`. Powers of `(√a)⁻¹` absorb integer
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
`√a - √b` expands to `a + b - 2√(ab)`. An eventually nonnegative function tends to `0` along a
filter exactly when its square root does.

The square root is subadditive and `1/2`-Hölder, `|√t - √s| ≤ √|t - s|`, and two displacement
estimates compare the square-root and inverse-square-root functions with the identity near `1`.
These bounds control scalar spectral factors of positive operators close to the identity. They
rest on the factorisation `|√x - √y| (√x + √y) = |x - y|` for nonnegative `x` and `y`.

The modular `√(1 + t²) - 1` is at most `|t|` and `t² / 2` and is locally Lipschitz, and
`|t / √(t² + p)| ≤ 1` for `p ≥ 0`. The map `y ↦ y / √(1 - y²)` inverts `t ↦ t / √(1 + t²)`, and
`y ↦ √(1 - y²) / y` recovers `|t|` from `1 / √(1 + t²)`. For `d ≠ 0` and `0 ≤ c`, a square
factor cancels against its absolute value, `|d| (√(d² c p))⁻¹ = (√c)⁻¹ (√p)⁻¹`, as in changes of
variables. For `p > 0` the substitution `t ↦ t + √(t² + p)` is positive and maps `ℝ` onto
`(0, ∞)`, and for `c > 0` the map `y ↦ y (√(y² + c) − y)` is strictly increasing on `[0, ∞)`. For
`a ≥ 0`, `{x | x² ≤ a}` is the interval `[-√a, √a]`, and for every `a`, `{x | a ≤ x²}` is a union
of two rays. Finally, `c √u` tends to `0` as `u → 0` (and through positive values as `u → 0⁺` when
`c > 0`), `α / (β y + √(y² + c)) → 0` as `y → +∞` for `β ≠ -1`, and the forward difference
`√x (√(x + 1) - √x)` tends to `1/2` as `x → ∞`.

## Main results

* `Real.inv_sqrt_mul_sq`, `Real.div_sqrt_sq`: `((√a)⁻¹ * x) ^ 2 = x ^ 2 / a` and
  `(x / √a) ^ 2 = x ^ 2 / a` for `0 ≤ a`.
* `Real.sqrt_sq_mul`, `Real.sqrt_mul_sq`: `√(x ^ 2 * y) = |x| * √y` and
  `√(x * y ^ 2) = √x * |y|`.
* `Real.sqrt_mul_eq_mul_sqrt_div`: `√(x * y) = y * √(x / y)` for `0 ≤ y`.
* `Real.sqrt_div_mul_mul_sqrt_div`: `√(u / t) * t * √(u / t) = u` for `0 ≤ u / t` and `t ≠ 0`.
* `Real.sqrt_le_sqrt_two_mul`: `√x ≤ √(2 * x)`.
* `Real.inv_sqrt_pow_mul_pow`: `(√a)⁻¹ ^ n * a ^ p = (√a)⁻¹ ^ (n - 2p)` for `0 < a` and `2p ≤ n`.
* `Real.sqrt_natCast_pow_self_pos`: `0 < √n ^ n` for every natural number `n`.
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
* `Real.abs_sqrt_sub_sqrt_mul_sqrt_add_sqrt`: `|√x - √y| (√x + √y) = |x - y|` for `0 ≤ x` and
  `0 ≤ y`.
* `Real.abs_sqrt_sub_one_le_abs_sub_one`: for every real `μ`, `|√μ - 1| ≤ |μ - 1|`.
* `Real.abs_one_sub_inv_sqrt_le_abs_sub_one`: if `1 ≤ μ + √μ`, `|1 - (√μ)⁻¹| ≤ |μ - 1|`.
* `Real.sqrt_add_le_add_sqrt`: for all reals `a` and `b`, `√(a + b) ≤ √a + √b`.
* `Real.sqrt_le_sqrt_add_sqrt_abs_sub`: for all reals `t` and `s`, `√t ≤ √s + √|t - s|`.
* `Real.abs_sqrt_sub_sqrt_le`: for all reals `t` and `s`, `|√t - √s| ≤ √|t - s|`.
* `Real.one_le_sqrt_one_add_sq`: for every real `t`, `1 ≤ √(1 + t²)`.
* `Real.abs_div_sqrt_sq_add_le_one`: for `p ≥ 0` and every real `t`, `|t / √(t² + p)| ≤ 1`.
* `Real.mul_inv_sqrt_one_add_sq_div_sqrt_one_sub_sq`: `y ↦ y / √(1 - y²)` inverts
  `t ↦ t / √(1 + t²)`.
* `Real.sqrt_one_sub_sq_div_inv_sqrt_one_add_sq`: `y ↦ √(1 - y²) / y` recovers `|t|` from
  `1 / √(1 + t²)`.
* `Real.sqrt_one_add_sq_sub_one_le_abs`: for every real `t`, `√(1 + t²) - 1 ≤ |t|`.
* `Real.sqrt_one_add_sq_sub_one_le_sq_div_two`: for every real `t`, `√(1 + t²) - 1 ≤ t² / 2`.
* `Real.abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le`: for all reals `a` and `b`,
  `|√(1 + a²) - √(1 + b²)| ≤ |a - b| (|a| + |b|)`.
* `Real.abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le_abs_sub`: `t ↦ √(1 + t²)` is `1`-Lipschitz.
* `Real.one_add_div_two_le_sqrt_one_add_sq`: for every real `t`, `(1 + t) / 2 ≤ √(1 + t²)`.
* `Real.abs_mul_inv_sqrt_sq_mul_mul`: for `d ≠ 0` and `0 ≤ c`,
  `|d| (√(d² c p))⁻¹ = (√c)⁻¹ (√p)⁻¹`.
* `Real.inv_sqrt_two_sq_add_inv_sqrt_two_sq`: `((√2)⁻¹)² + ((√2)⁻¹)² = 1`.
* `Real.add_sqrt_sq_add_pos`, `Real.image_add_sqrt_sq_add_eq_Ioi`: for `p > 0`, the substitution
  `t ↦ t + √(t² + p)` is positive and maps `ℝ` onto `(0, ∞)`.
* `Real.strictMonoOn_mul_sqrt_sq_add_sub`: for `c > 0`, `y ↦ y (√(y² + c) − y)` is strictly
  increasing on `[0, ∞)`.
* `Real.setOf_sq_le_eq_Icc`: for `0 ≤ a`, `{x | x² ≤ a} = [-√a, √a]`.
* `Real.setOf_le_sq_eq_union`: `{x | a ≤ x²} = (-∞, -√a] ∪ [√a, ∞)`.
* `Real.tendsto_mul_sqrt_nhds_zero`: `c √u → 0` as `u → 0`.
* `Real.tendsto_mul_sqrt_nhdsGT_zero`, `Real.tendsto_sqrt_nhdsGT_zero`: for `c > 0`,
  `c √u → 0⁺` as `u → 0⁺`.
* `Real.tendsto_div_mul_add_sqrt_sq_add_atTop`: for `β ≠ -1`,
  `α / (β y + √(y² + c)) → 0` as `y → +∞`.
* `Real.tendsto_sqrt_mul_sqrt_add_one_sub_sqrt`: `√x (√(x + 1) - √x) → 1/2` as `x → ∞`.
* `Real.sq_sqrt_sub_sqrt`: `(√a - √b)² = a + b - 2√(ab)` for `0 ≤ a` and `0 ≤ b`.
* `Real.sqrt_bounds_of_abs_sub_le`: `√y / r ≤ √x ≤ r √y` when `|x - y| ≤ (1 - r⁻²) y`
  and `1 ≤ r`.
* `Real.tendsto_sqrt_nhds_zero_iff`: an eventually nonnegative function tends to `0` exactly when
  its square root does.
* `Real.nat_sqrt_floor_le_real_sqrt`, `Real.real_sqrt_lt_nat_sqrt_floor_add_one`,
  `Real.nat_floor_real_sqrt_eq_nat_sqrt_floor`: for every real `x`, the natural square root of
  `⌊x⌋₊` satisfies `Nat.sqrt ⌊x⌋₊ ≤ √x < Nat.sqrt ⌊x⌋₊ + 1`, so `⌊√x⌋₊ = Nat.sqrt ⌊x⌋₊`.
* `TauCeti.sum_range_inv_sqrt_add_one_le`: the sum of the reciprocal square roots of `1` through
  `n` is at most `2√n`.
* `TauCeti.tendsto_sqrt_natCast_add_one_atTop`: `√(n + 1) → ∞` along the natural numbers, the
  divergence of the normalization of an `(n + 1) × (n + 1)` random matrix.

## References

`Real.abs_sqrt_sub_one_le_abs_sub_one` and `Real.abs_one_sub_inv_sqrt_le_abs_sub_one` come from
the [AIQ DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
`ForTauCeti/Analysis/SpecialFunctions/Sqrt.lean`.

`Real.add_sqrt_sq_add_pos` and `Real.image_add_sqrt_sq_add_eq_Ioi` are extracted from, and their
proofs adapted from, Jeremy Tan's
[Mathlib PR #34397](https://github.com/leanprover-community/mathlib4/pull/34397), commit
`376352b6e080265bc0380074baaf9aafa0b70a80`.

`Real.strictMonoOn_mul_sqrt_sq_add_sub` and `Real.tendsto_div_mul_add_sqrt_sq_add_atTop` are
adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/ErrorFunctions/BoundsAsymptotics/ContinuedFractions.lean`.
-/

public section

namespace Real

/-- For nonnegative `x`, `y`, the difference of squares of `√x` and `√y` in absolute value:
`|√x - √y| (√x + √y) = |x - y|`. -/
@[simp]
theorem abs_sqrt_sub_sqrt_mul_sqrt_add_sqrt (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |√x - √y| * (√x + √y) = |x - y| :=
  calc |√x - √y| * (√x + √y) = |(√x + √y) * (√x - √y)| := by
        rw [abs_mul, abs_of_nonneg (add_nonneg (sqrt_nonneg x) (sqrt_nonneg y))]
        ring
    _ = |x - y| := by rw [← sq_sub_sq, sq_sqrt hx, sq_sqrt hy]

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
    rw [← abs_sqrt_sub_sqrt_mul_sqrt_add_sqrt _ _ (sq_nonneg a) hr, sqrt_sq ha]
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

/-- Dividing by `√a` and squaring divides the square by `a`. -/
theorem div_sqrt_sq {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : (x / √a) ^ 2 = x ^ 2 / a := by
  rw [div_pow, sq_sqrt ha]

/-- A square factor comes out of a square root as its absolute value. -/
theorem sqrt_sq_mul (x y : ℝ) : √(x ^ 2 * y) = |x| * √y := by
  rw [sqrt_mul (sq_nonneg _), sqrt_sq_eq_abs]

/-- A square factor comes out of a square root as its absolute value, on the right:
`√(x * y ^ 2) = √x * |y|`. -/
theorem sqrt_mul_sq (x y : ℝ) : √(x * y ^ 2) = √x * |y| := by
  rw [sqrt_mul' _ (sq_nonneg _), sqrt_sq_eq_abs]

/-- A nonnegative factor comes out of a square root against the quotient by it:
`√(x * y) = y * √(x / y)` for `0 ≤ y`. Both sides vanish at `y = 0`. -/
theorem sqrt_mul_eq_mul_sqrt_div (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : √(x * y) = y * √(x / y) := by
  rcases hy.eq_or_lt with rfl | hy
  · simp
  -- The factor `y` is the square root of `y ^ 2` in `x * y = y ^ 2 * (x / y)`.
  have h : x * y = y ^ 2 * (x / y) := by
    rw [sq, mul_assoc, mul_div_cancel₀ x hy.ne', mul_comm]
  rw [h, sqrt_sq_mul, abs_of_pos hy]

/-- Conjugating `t` by `√(u / t)` recovers `u`: `√(u / t) * t * √(u / t) = u` when `u / t` is
nonnegative and `t ≠ 0`. -/
theorem sqrt_div_mul_mul_sqrt_div {u t : ℝ} (h : 0 ≤ u / t) (ht : t ≠ 0) :
    √(u / t) * t * √(u / t) = u := by
  rw [mul_right_comm, mul_self_sqrt h, div_mul_cancel₀ _ ht]

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

/-- The power `√n ^ n` (the constant `n^{n/2}`) is positive; it is `1` for `n = 0`. -/
theorem sqrt_natCast_pow_self_pos (n : ℕ) : 0 < √(n : ℝ) ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact pow_pos (sqrt_pos.mpr (Nat.cast_pos.mpr hn)) n

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

/-- The squared half-angle quotient can be rationalized when `|t| ≤ 1`. -/
theorem sq_div_one_add_sqrt_one_sub_sq {t : ℝ} (ht : |t| ≤ 1) :
    (t / (1 + √(1 - t ^ 2))) ^ 2 =
      (1 - √(1 - t ^ 2)) / (1 + √(1 - t ^ 2)) := by
  set s := √(1 - t ^ 2)
  have hs : s ^ 2 = 1 - t ^ 2 := sq_sqrt_one_sub_sq ht
  have ht₂ : t ^ 2 = 1 - s ^ 2 := by linarith
  have hs₀ : 0 ≤ s := sqrt_nonneg _
  rw [div_pow, ht₂]
  field_simp
  ring

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

/-- For every real `μ`, the square root is no farther from `1` than `μ` is:
`|√μ - 1| ≤ |μ - 1|`. -/
theorem abs_sqrt_sub_one_le_abs_sub_one (μ : ℝ) :
    |√μ - 1| ≤ |μ - 1| := by
  rcases le_total 0 μ with hμ | hμ
  · have h := abs_sqrt_sub_sqrt_mul_sqrt_add_sqrt μ 1 hμ zero_le_one
    rw [sqrt_one] at h
    calc |√μ - 1| ≤ |√μ - 1| * (√μ + 1) :=
          le_mul_of_one_le_right (abs_nonneg _) (le_add_of_nonneg_left (sqrt_nonneg μ))
      _ = |μ - 1| := h
  · rw [sqrt_eq_zero_of_nonpos hμ, abs_of_nonpos (by linarith : μ - 1 ≤ 0)]
    norm_num
    linarith

/-- If `1 ≤ μ + √μ`, then the inverse square root is no farther from `1` than `μ` is:
`|1 - (√μ)⁻¹| ≤ |μ - 1|`. The hypothesis forces `0 < μ` and holds for `1 / 2 ≤ μ`; for positive
`μ ≠ 1` it is equivalent to the bound. -/
theorem abs_one_sub_inv_sqrt_le_abs_sub_one (μ : ℝ) (hμ : 1 ≤ μ + √μ) :
    |1 - (√μ)⁻¹| ≤ |μ - 1| := by
  have hμ₀ : 0 < μ := by
    by_contra! h
    rw [sqrt_eq_zero_of_nonpos h] at hμ
    linarith
  have hs : 0 < √μ := sqrt_pos.2 hμ₀
  have h := abs_sqrt_sub_sqrt_mul_sqrt_add_sqrt μ 1 hμ₀.le zero_le_one
  rw [sqrt_one] at h
  -- `|1 - (√μ)⁻¹| = |√μ - 1| / √μ`, and `1 ≤ (√μ + 1) √μ = μ + √μ`.
  have h1 : 1 ≤ (√μ + 1) * √μ := by rwa [add_one_mul, mul_self_sqrt hμ₀.le]
  calc |1 - (√μ)⁻¹| = |√μ - 1| / √μ := by
        rw [inv_eq_one_div, one_sub_div hs.ne', abs_div, abs_of_pos hs]
    _ ≤ |√μ - 1| * (√μ + 1) := by
        rw [div_le_iff₀ hs, mul_assoc]
        exact le_mul_of_one_le_right (abs_nonneg _) h1
    _ = |μ - 1| := h

/-- Subadditivity of the square root: `√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le_add_sqrt (a b : ℝ) : √(a + b) ≤ √a + √b := by
  rw [sqrt_le_left (by positivity), add_sq, sq_sqrt', sq_sqrt']
  nlinarith [le_max_left a 0, le_max_left b 0, mul_nonneg (sqrt_nonneg a) (sqrt_nonneg b)]

/-- For all reals `t` and `s`, `√t ≤ √s + √|t - s|`. -/
theorem sqrt_le_sqrt_add_sqrt_abs_sub (t s : ℝ) : √t ≤ √s + √|t - s| :=
  (sqrt_le_sqrt (by linarith [le_abs_self (t - s)])).trans (sqrt_add_le_add_sqrt s |t - s|)

/-- **The square root is `1/2`-Hölder.** For all reals `t` and `s`, `|√t - √s| ≤ √|t - s|`. -/
theorem abs_sqrt_sub_sqrt_le (t s : ℝ) : |√t - √s| ≤ √|t - s| := by
  have h₁ := sqrt_le_sqrt_add_sqrt_abs_sub t s
  have h₂ := sqrt_le_sqrt_add_sqrt_abs_sub s t
  rw [abs_sub_comm s t] at h₂
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- For every real `t`, `1 ≤ √(1 + t²)`. -/
theorem one_le_sqrt_one_add_sq (t : ℝ) : 1 ≤ √(1 + t ^ 2) :=
  one_le_sqrt.mpr (by nlinarith [sq_nonneg t])

/-- For `p ≥ 0` and every real `t`, `|t / √(t² + p)| ≤ 1`, including when the
square root vanishes. -/
theorem abs_div_sqrt_sq_add_le_one {p : ℝ} (hp : 0 ≤ p) (t : ℝ) :
    |t / √(t ^ 2 + p)| ≤ 1 := by
  rw [abs_div, abs_of_nonneg (sqrt_nonneg _)]
  exact div_le_one_of_le₀ (abs_le_sqrt (le_add_of_nonneg_right hp)) (sqrt_nonneg _)

/-- The map `y ↦ y / √(1 - y²)` inverts `t ↦ t / √(1 + t²)` on every real `t`. -/
theorem mul_inv_sqrt_one_add_sq_div_sqrt_one_sub_sq (t : ℝ) :
    t * (√(1 + t ^ 2))⁻¹ / √(1 - (t * (√(1 + t ^ 2))⁻¹) ^ 2) = t := by
  have hs : 0 < (√(1 + t ^ 2))⁻¹ := inv_pos.2 (sqrt_pos.2 (by positivity))
  have h : 1 - (t * (√(1 + t ^ 2))⁻¹) ^ 2 = (√(1 + t ^ 2))⁻¹ ^ 2 := by
    rw [mul_pow, inv_pow, sq_sqrt (by positivity)]
    field_simp
    ring
  rw [h, sqrt_sq hs.le, mul_div_assoc, div_self hs.ne', mul_one]

/-- The map `y ↦ √(1 - y²) / y` recovers `|t|` from `1 / √(1 + t²)`, for every real `t`. -/
theorem sqrt_one_sub_sq_div_inv_sqrt_one_add_sq (t : ℝ) :
    √(1 - ((√(1 + t ^ 2))⁻¹) ^ 2) / (√(1 + t ^ 2))⁻¹ = |t| := by
  have hs : 0 < (√(1 + t ^ 2))⁻¹ := inv_pos.2 (sqrt_pos.2 (by positivity))
  have h : 1 - ((√(1 + t ^ 2))⁻¹) ^ 2 = (|t| * (√(1 + t ^ 2))⁻¹) ^ 2 := by
    rw [mul_pow, inv_pow, sq_sqrt (by positivity), sq_abs]
    field_simp
    ring
  rw [h, sqrt_sq (by positivity), mul_div_assoc, div_self hs.ne', mul_one]

/-- The modular `√(1 + t²) - 1` grows at most linearly: `√(1 + t²) - 1 ≤ |t|`. -/
theorem sqrt_one_add_sq_sub_one_le_abs (t : ℝ) : √(1 + t ^ 2) - 1 ≤ |t| := by
  rw [sub_le_iff_le_add']
  have h := sqrt_add_le_add_sqrt 1 (t ^ 2)
  rwa [sqrt_one, sqrt_sq_eq_abs] at h

/-- The modular `√(1 + t²) - 1` is at most quadratic: `√(1 + t²) - 1 ≤ t² / 2`. -/
theorem sqrt_one_add_sq_sub_one_le_sq_div_two (t : ℝ) : √(1 + t ^ 2) - 1 ≤ t ^ 2 / 2 := by
  rw [sub_le_iff_le_add']
  exact sqrt_one_add_le (by linarith [sq_nonneg t])

/-- The modular `√(1 + t²) - 1` is locally Lipschitz with a linear modulus:
`|√(1 + a²) - √(1 + b²)| ≤ |a - b| (|a| + |b|)`. -/
theorem abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le (a b : ℝ) :
    |√(1 + a ^ 2) - √(1 + b ^ 2)| ≤ |a - b| * (|a| + |b|) := by
  have ha := one_le_sqrt_one_add_sq a
  have hb := one_le_sqrt_one_add_sq b
  calc |√(1 + a ^ 2) - √(1 + b ^ 2)|
      ≤ |√(1 + a ^ 2) - √(1 + b ^ 2)| * (√(1 + a ^ 2) + √(1 + b ^ 2)) :=
        le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = |a + b| * |a - b| := by
        rw [abs_sqrt_sub_sqrt_mul_sqrt_add_sqrt _ _ (by positivity) (by positivity),
          add_sub_add_left_eq_sub, sq_sub_sq, abs_mul]
    _ ≤ (|a| + |b|) * |a - b| := mul_le_mul_of_nonneg_right (abs_add_le a b) (abs_nonneg _)
    _ = |a - b| * (|a| + |b|) := mul_comm _ _

/-- The function `t ↦ √(1 + t²)` is `1`-Lipschitz on the real line:
`|√(1 + a²) - √(1 + b²)| ≤ |a - b|`. -/
theorem abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le_abs_sub (a b : ℝ) :
    |√(1 + a ^ 2) - √(1 + b ^ 2)| ≤ |a - b| := by
  have hpos : 0 < √(1 + a ^ 2) + √(1 + b ^ 2) := by
    linarith [one_le_sqrt_one_add_sq a, one_le_sqrt_one_add_sq b]
  -- `|a| ≤ √(1 + a²)` and `|b| ≤ √(1 + b²)`, so the sum of the roots dominates `|a + b|`.
  have hab : |a + b| ≤ √(1 + a ^ 2) + √(1 + b ^ 2) :=
    (abs_add_le a b).trans (add_le_add (abs_le_sqrt (by nlinarith)) (abs_le_sqrt (by nlinarith)))
  refine le_of_mul_le_mul_right ?_ hpos
  -- `|√(1 + a²) - √(1 + b²)| (√(1 + a²) + √(1 + b²)) = |a + b| |a - b|`.
  rw [abs_sqrt_sub_sqrt_mul_sqrt_add_sqrt _ _ (by positivity) (by positivity),
    add_sub_add_left_eq_sub, sq_sub_sq, abs_mul]
  exact (mul_le_mul_of_nonneg_right hab (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- For every real `t`, `(1 + t) / 2 ≤ √(1 + t²)`. -/
theorem one_add_div_two_le_sqrt_one_add_sq (t : ℝ) : (1 + t) / 2 ≤ √(1 + t ^ 2) :=
  le_sqrt_of_sq_le (by nlinarith [sq_nonneg (t - 1)])

/-- **A square factor cancels against its absolute value.** For `d ≠ 0` and `0 ≤ c`,
`|d| (√(d² c p))⁻¹ = (√c)⁻¹ (√p)⁻¹`. This is the cancellation of the Jacobian `|d|` of a change
of variables against the square root of an integrand that has acquired the factor `d²`. -/
theorem abs_mul_inv_sqrt_sq_mul_mul {d c : ℝ} (hd : d ≠ 0) (hc : 0 ≤ c) (p : ℝ) :
    |d| * (√(d ^ 2 * c * p))⁻¹ = (√c)⁻¹ * (√p)⁻¹ := by
  rw [sqrt_mul (mul_nonneg (sq_nonneg d) hc), sqrt_sq_mul d c, mul_inv,
    mul_inv, mul_assoc, mul_inv_cancel_left₀ (abs_ne_zero.2 hd)]

/-- The vector `((√2)⁻¹, (√2)⁻¹)` has unit length: `((√2)⁻¹)² + ((√2)⁻¹)² = 1`. -/
theorem inv_sqrt_two_sq_add_inv_sqrt_two_sq : (√2)⁻¹ ^ 2 + (√2)⁻¹ ^ 2 = (1 : ℝ) := by
  rw [inv_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- For `0 < p`, `t + √(t² + p)` is positive. -/
theorem add_sqrt_sq_add_pos {p : ℝ} (hp : 0 < p) (t : ℝ) : 0 < t + √(t ^ 2 + p) := by
  rcases le_or_gt 0 t with ht | ht; · positivity
  rw [← neg_lt_iff_pos_add']
  nth_rw 1 [← abs_of_nonpos ht.le, ← sqrt_sq_eq_abs, ← add_zero (t ^ 2)]
  gcongr

/-- For `0 < p`, the map `t ↦ t + √(t² + p)` sends `ℝ` onto `(0, ∞)`. -/
theorem image_add_sqrt_sq_add_eq_Ioi {p : ℝ} (hp : 0 < p) :
    (fun t : ℝ ↦ t + √(t ^ 2 + p)) '' Set.univ = Set.Ioi 0 := by
  ext x
  rw [Set.image_univ, Set.mem_range, Set.mem_Ioi]
  refine ⟨fun ⟨t, ht⟩ ↦ ht.symm ▸ add_sqrt_sq_add_pos hp t, fun hx ↦ ?_⟩
  use (x ^ 2 - p) / (2 * x)
  have hradicand : ((x ^ 2 - p) / (2 * x)) ^ 2 + p = ((x ^ 2 + p) / (2 * x)) ^ 2 := by
    field_simp
    ring
  have hsqrt : √(((x ^ 2 - p) / (2 * x)) ^ 2 + p) = (x ^ 2 + p) / (2 * x) := by
    rw [hradicand, sqrt_sq (by positivity)]
  rw [hsqrt]
  field_simp
  ring

/-- For `c > 0`, `y ↦ y (√(y² + c) − y)` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_mul_sqrt_sq_add_sub {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (fun y => y * (√(y ^ 2 + c) - y)) (Set.Ici 0) := by
  intro y₁ h0 y₂ h2 h12
  simp only [Set.mem_Ici] at h0 h2
  have hs : ∀ y : ℝ, √(y ^ 2 + c) ^ 2 = y ^ 2 + c := fun y => sq_sqrt (by positivity)
  have hp : ∀ y : ℝ, 0 < √(y ^ 2 + c) := fun y => sqrt_pos.mpr (by positivity)
  -- `√(y² + c) − y = c / (√(y² + c) + y)`
  have hrw : ∀ y : ℝ, 0 ≤ y → √(y ^ 2 + c) - y = c / (√(y ^ 2 + c) + y) := by
    intro y hy
    rw [eq_div_iff (by linarith [hp y])]; nlinarith [hs y]
  dsimp only
  rw [hrw y₁ h0, hrw y₂ h2, mul_div_assoc', mul_div_assoc',
    div_lt_div_iff₀ (by linarith [hp y₁]) (by linarith [hp y₂])]
  have hkey : y₁ * √(y₂ ^ 2 + c) < y₂ * √(y₁ ^ 2 + c) := by
    refine lt_of_not_ge fun hcon => ?_
    have hnn : 0 ≤ y₂ * √(y₁ ^ 2 + c) := mul_nonneg h2 (hp _).le
    have := mul_self_le_mul_self hnn hcon
    nlinarith [hs y₁, hs y₂, mul_lt_mul_of_pos_left (mul_self_lt_mul_self h0 h12) hc]
  nlinarith [mul_lt_mul_of_pos_left hkey hc]

/-- The closed sublevel `{x² ≤ a}` of the square, for `0 ≤ a`, is the interval `[-√a, √a]`. -/
theorem setOf_sq_le_eq_Icc {a : ℝ} (ha : 0 ≤ a) : {x : ℝ | x ^ 2 ≤ a} = Set.Icc (-√a) √a := by
  ext x
  simp [sq_le ha]

/-- The closed superlevel `{a ≤ x²}` of the square is the union of the two rays
`(-∞, -√a]` and `[√a, ∞)`; for `a ≤ 0` they cover the line, since then `√a = 0`. -/
theorem setOf_le_sq_eq_union (a : ℝ) :
    {x : ℝ | a ≤ x ^ 2} = Set.Iic (-√a) ∪ Set.Ici √a := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  rw [← sqrt_le_sqrt_iff (sq_nonneg x), sqrt_sq_eq_abs, le_abs']

section Limits

open Filter
open scoped Topology

/-- For every `c`, `c √u` tends to `0` as `u → 0`. -/
theorem tendsto_mul_sqrt_nhds_zero (c : ℝ) : Tendsto (fun u => c * √u) (𝓝 0) (𝓝 0) := by
  have h : Continuous fun u => c * √u := by fun_prop
  simpa using h.tendsto 0

/-- For `c > 0`, `c √u` tends to `0` through positive values as `u → 0⁺`. -/
theorem tendsto_mul_sqrt_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u => c * √u) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_mul_sqrt_nhds_zero c).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact mul_pos hc (sqrt_pos.2 hu)

/-- The square root tends to `0` through positive values as `u → 0⁺`. -/
theorem tendsto_sqrt_nhdsGT_zero : Tendsto (√·) (𝓝[>] 0) (𝓝[>] (0 : ℝ)) := by
  simpa using tendsto_mul_sqrt_nhdsGT_zero one_pos

/-- For `β ≠ −1`, `α / (β y + √(y² + c))` tends to `0` as `y → +∞`. -/
theorem tendsto_div_mul_add_sqrt_sq_add_atTop (α : ℝ) {β : ℝ} (hβ : β ≠ -1) (c : ℝ) :
    Tendsto (fun y => α / (β * y + √(y ^ 2 + c))) atTop (𝓝 0) := by
  -- For `y > 0` the function is `(α / y) / (β + √(1 + c / y²))`.
  have hden : Tendsto (fun y : ℝ => β + √(1 + c / y ^ 2)) atTop (𝓝 (β + 1)) := by
    have : Tendsto (fun y : ℝ => 1 + c / y ^ 2) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero))
    simpa using tendsto_const_nhds.add this.sqrt
  have h := (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun y : ℝ => α / y) atTop (𝓝 0)).div
    hden fun h => hβ (by linarith)
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  have hs : √(y ^ 2 + c) = y * √(1 + c / y ^ 2) := by
    rw [show y ^ 2 + c = y ^ 2 * (1 + c / y ^ 2) by field_simp, sqrt_sq_mul, abs_of_pos hy]
  simp only [Pi.div_apply, hs, div_div]
  ring

/-- The forward difference of the square root is asymptotic to its derivative:
`√x (√(x + 1) - √x) → 1/2` as `x → ∞`. -/
theorem tendsto_sqrt_mul_sqrt_add_one_sub_sqrt :
    Tendsto (fun x : ℝ => √x * (√(x + 1) - √x)) atTop (𝓝 (1 / 2)) := by
  have hlim : Tendsto (fun x : ℝ => (√(1 + x⁻¹) + 1)⁻¹) atTop (𝓝 (1 / 2)) := by
    have h := ((tendsto_inv_atTop_zero.const_add 1).sqrt.add_const 1).inv₀ (by norm_num)
    norm_num at h
    simpa [one_div] using h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have ha : 0 < √x := sqrt_pos.2 hx
  have hq : √(1 + x⁻¹) = √(x + 1) / √x := by
    rw [← sqrt_div (by linarith) x]
    congr 1
    field_simp
  rw [hq, div_add_one ha.ne', inv_div, eq_comm, eq_div_iff (by positivity)]
  linear_combination √x * (sq_sqrt (show 0 ≤ x + 1 by linarith) - sq_sqrt hx.le)

end Limits

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

open Filter Topology in
/-- An eventually nonnegative real function tends to `0` exactly when its square root does. -/
theorem tendsto_sqrt_nhds_zero_iff {α : Type*} {l : Filter α} {f : α → ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x) :
    Tendsto (fun x ↦ √(f x)) l (𝓝 0) ↔ Tendsto f l (𝓝 0) := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa using h.sqrt⟩
  refine (by simpa using h.pow 2 : Tendsto (fun x ↦ √(f x) ^ 2) l (𝓝 0)).congr' ?_
  filter_upwards [hf] with x hx using sq_sqrt hx

/-- For every real `x`, the natural square root of `⌊x⌋₊` is at most `√x`. For `x < 0` both
sides are zero. This extends Mathlib's `Real.nat_sqrt_le_real_sqrt` from natural to real `x`. -/
theorem nat_sqrt_floor_le_real_sqrt (x : ℝ) : ((⌊x⌋₊.sqrt : ℕ) : ℝ) ≤ √x := by
  rcases le_or_gt 0 x with hx | hx
  · exact nat_sqrt_le_real_sqrt.trans (sqrt_le_sqrt (Nat.floor_le hx))
  · simp [Nat.floor_of_nonpos hx.le, sqrt_eq_zero_of_nonpos hx.le]

/-- For every real `x`, `√x` is less than the natural square root of `⌊x⌋₊` plus one. This
extends Mathlib's `Real.real_sqrt_lt_nat_sqrt_succ` from natural to real `x`. -/
theorem real_sqrt_lt_nat_sqrt_floor_add_one (x : ℝ) : √x < (⌊x⌋₊.sqrt : ℕ) + 1 := by
  rw [sqrt_lt' (by positivity)]
  have h : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((⌊x⌋₊.sqrt + 1) ^ 2 : ℕ) :=
    Nat.cast_le.2 (Nat.add_one_le_iff.2 (Nat.sqrt_lt'.1 (Nat.lt_add_one _)))
  push_cast at h
  linarith [Nat.lt_floor_add_one x]

/-- For every real `x`, the floor of `√x` is the natural square root of `⌊x⌋₊`. This extends
Mathlib's `Real.nat_floor_real_sqrt_eq_nat_sqrt` from natural to real `x`. -/
@[simp]
theorem nat_floor_real_sqrt_eq_nat_sqrt_floor (x : ℝ) : ⌊√x⌋₊ = ⌊x⌋₊.sqrt :=
  (Nat.floor_eq_iff (sqrt_nonneg x)).2
    ⟨nat_sqrt_floor_le_real_sqrt x, real_sqrt_lt_nat_sqrt_floor_add_one x⟩

end Real

namespace TauCeti

/-- The sum of the reciprocal square roots of the first `n` positive integers is at most `2√n`. -/
theorem sum_range_inv_sqrt_add_one_le (n : ℕ) :
    (∑ i ∈ Finset.range n, (√((i : ℝ) + 1))⁻¹) ≤ 2 * √(n : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, 2 * (√((i : ℝ) + 1) - √(i : ℝ)) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hpos : 0 < √((i : ℝ) + 1) := by positivity
      have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)
      have hsq' := Real.sq_sqrt (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      nlinarith only [hsq, hsq', sq_nonneg (√((i : ℝ) + 1) - √(i : ℝ))]
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [← Nat.cast_succ]
      rw [Finset.sum_range_sub (fun i : ℕ ↦ √(i : ℝ))]
      simp

open Filter in
/-- The square roots of the successive natural numbers `n + 1` tend to infinity. -/
theorem tendsto_sqrt_natCast_add_one_atTop :
    Tendsto (fun n : ℕ ↦ √((n + 1 : ℕ) : ℝ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

end TauCeti
