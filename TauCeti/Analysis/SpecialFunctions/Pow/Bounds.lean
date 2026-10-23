/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Elementary bounds on real powers

A base at least `2` raised to a negative exponent of size at least `1` is at most `1 / 2`. This
is the shape in which the local ratio of an Euler factor is bounded away from `1`, so that the
denominator `1 - y ^ (-s)` stays bounded below.

For any `θ < 1` and any exponent `β`, some base `τ ∈ (0, 1)` has `θ < τ ^ β`. This is how a
geometric ratio is chosen in iteration arguments, such as the absorption lemma.

For `1 ≤ p`, the graph of `u ↦ u ^ p` on `[0, ∞)` lies above each of its tangent lines:
`v ^ p + p * v ^ (p - 1) * (u - v) ≤ u ^ p`, strictly so when `1 < p` and `u ≠ v`. This is
Bernoulli's inequality made homogeneous, and it is the first-order optimality test for weighted
sums of powers.

For `t ∈ [0, 1]` and any exponent `r`, the sum `(1 - t) ^ r + t ^ r` is positive, so it can be
used as the normalizing denominator of a pair of weights.

If `1 ≤ C`, `D < n` and `C ^ (D / (n - D)) < B + 1`, then `(⌊C B⌋₊ + 1) ^ D < (B + 1) ^ n`. This
is the counting step of Siegel's lemma: it compares the integer points of a box with the cells
of a partition of the image of that box under `D` linear forms.

For `t > 0` and every natural `k`, `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k`: the Japanese bracket
decays at least as fast as `t ^ (-1)`. This converts symbol estimates of order `0` into Mihlin's
condition.

If `0 < d` and `2 ≤ d ^ (p - 2)`, then `d ^ (-p) ≤ 1 / (2 d ^ 2)`: an approximation of quality
`d ^ (-p)` meets the hypothesis of Legendre's theorem `Real.exists_rat_eq_convergent`.

If `2 ≤ q ≤ q'` and `q ^ p < q (q + q')`, then `q ^ (p - 1) < 2 q'`, so
`(p - 1) log q < log 2 + log q'`. Hence `t < log q' / log q` once `log 2 < (p - 1 - t) log q`.
This reads off the growth of consecutive continued-fraction denominators from the lower error
bound `1 / (q (q + q')) < |ξ - p / q|`.

For `s ≥ 0` the weight `(1 + ‖x‖) ^ s` on a seminormed group is subadditive up to the constant
`2 ^ s`. This is the weight inequality behind product estimates in weighted sequence spaces.

## Main results

* `Real.rpow_neg_le_half`: `y ^ (-s) ≤ 1 / 2` for `2 ≤ y` and `1 ≤ s`.
* `Real.exists_pos_lt_one_lt_rpow`: for `θ < 1` and any `β`, some `τ ∈ (0, 1)` has `θ < τ ^ β`.
* `Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow` and
  `Real.rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow`: the tangent-line inequalities for `u ↦ u ^ p`.
* `Real.one_sub_rpow_add_rpow_pos`: `0 < (1 - t) ^ r + t ^ r` for `t ∈ [0, 1]`.
* `Real.floor_mul_add_one_pow_lt`: `(⌊C B⌋₊ + 1) ^ D < (B + 1) ^ n` for `1 ≤ C`, `D < n` and
  `C ^ (D / (n - D)) < B + 1`.
* `Real.one_add_sq_rpow_neg_le`: `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k` for `0 < t`.
* `Real.rpow_neg_le_one_div_two_mul_sq`: `d ^ (-p) ≤ 1 / (2 d ^ 2)` for `2 ≤ d ^ (p - 2)`.
* `Real.lt_log_div_log_of_rpow_lt`: `t < log q' / log q` for `2 ≤ q ≤ q'`,
  `q ^ p < q (q + q')` and `log 2 < (p - 1 - t) log q`.
* `TauCeti.one_add_norm_add_rpow_le`: `(1 + ‖x + y‖) ^ s ≤ 2 ^ s ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s)`
  for `0 ≤ s`.
-/

public section

namespace Real

/-- If `2 ≤ y` and `1 ≤ s`, then `y ^ (-s) ≤ 1 / 2`. -/
theorem rpow_neg_le_half {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) : y ^ (-s) ≤ 1 / 2 :=
  calc y ^ (-s) ≤ (2 : ℝ) ^ (-s) := rpow_le_rpow_of_nonpos two_pos hy (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    _ = 1 / 2 := by norm_num

/-- For `θ < 1` and any exponent `β`, some ratio `τ ∈ (0, 1)` has `θ < τ ^ β`. -/
theorem exists_pos_lt_one_lt_rpow {θ : ℝ} (hθ : θ < 1) (β : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ θ < τ ^ β := by
  rcases le_or_gt β 0 with hβ | hβ
  · exact ⟨1 / 2, by norm_num, by norm_num,
      hθ.trans_le (one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num) hβ)⟩
  · set c := max ((1 + θ) / 2) (1 / 2)
    have hc0 : 0 < c := lt_max_of_lt_right (by norm_num)
    have hc1 : c < 1 := max_lt (by linarith) (by norm_num)
    refine ⟨c ^ β⁻¹, rpow_pos_of_pos hc0 _, rpow_lt_one hc0.le hc1 (inv_pos.2 hβ), ?_⟩
    rw [← rpow_mul hc0.le, inv_mul_cancel₀ hβ.ne', rpow_one]
    exact lt_max_of_lt_left (by linarith)

/-- **The strict tangent-line inequality for real powers.** For `1 < p` and distinct `u, v ≥ 0`,
`u ↦ u ^ p` lies strictly above its tangent line at `v`. -/
theorem rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow {p u v : ℝ} (hp : 1 < p) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (huv : u ≠ v) : v ^ p + p * v ^ (p - 1) * (u - v) < u ^ p := by
  rcases hv.eq_or_lt with rfl | hv
  · rw [zero_rpow (by linarith), zero_rpow (by linarith)]
    simpa using rpow_pos_of_pos (hu.lt_of_ne' huv) p
  · have hs : -1 ≤ (u - v) / v := by
      rw [le_div_iff₀ hv]
      linarith
    have h := one_add_mul_self_lt_rpow_one_add hs (div_ne_zero (sub_ne_zero.2 huv) hv.ne') hp
    have hu_div : 1 + (u - v) / v = u / v := by
      field_simp
      ring
    rw [hu_div, div_rpow hu hv.le, lt_div_iff₀ (rpow_pos_of_pos hv p)] at h
    rw [rpow_sub_one hv.ne']
    calc v ^ p + p * (v ^ p / v) * (u - v) = (1 + p * ((u - v) / v)) * v ^ p := by
          field_simp
      _ < u ^ p := h

/-- **The tangent-line inequality for real powers.** For `1 ≤ p` and `u, v ≥ 0`, `u ↦ u ^ p` lies
above its tangent line at `v`. This is Bernoulli's inequality
`one_add_mul_self_le_rpow_one_add` made homogeneous. -/
theorem rpow_add_mul_rpow_sub_one_mul_sub_le_rpow {p u v : ℝ} (hp : 1 ≤ p) (hu : 0 ≤ u)
    (hv : 0 ≤ v) : v ^ p + p * v ^ (p - 1) * (u - v) ≤ u ^ p := by
  rcases hp.eq_or_lt with rfl | hp
  · simp
  rcases eq_or_ne u v with rfl | huv
  · simp
  exact (rpow_add_mul_rpow_sub_one_mul_sub_lt_rpow hp hu hv huv).le

/-- For `t ∈ [0, 1]` and any exponent `r`, `(1 - t) ^ r + t ^ r` is positive: at least one of the
two bases is positive. -/
theorem one_sub_rpow_add_rpow_pos (r : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < (1 - t) ^ r + t ^ r := by
  rcases ht.1.eq_or_lt with rfl | ht₀
  · simpa using add_pos_of_pos_of_nonneg zero_lt_one (rpow_nonneg le_rfl r)
  · exact add_pos_of_nonneg_of_pos (rpow_nonneg (sub_nonneg.2 ht.2) r) (rpow_pos_of_pos ht₀ r)

/-- **The counting estimate of Siegel's lemma.** If `1 ≤ C`, `D < n` and
`C ^ (D / (n - D)) < B + 1`, then `(⌊C B⌋₊ + 1) ^ D < (B + 1) ^ n`: the `(B + 1) ^ n` integer
points of the box `[0, B]^n` outnumber the cells of a partition of `[0, C B]^D` into
`⌊C B⌋₊ + 1` intervals per coordinate. -/
theorem floor_mul_add_one_pow_lt {C : ℝ} (hC : 1 ≤ C) {D n B : ℕ} (hDn : D < n)
    (hB : C ^ ((D : ℝ) / (n - D)) < B + 1) :
    (⌊C * B⌋₊ + 1) ^ D < (B + 1) ^ n := by
  have hnD : (D : ℝ) < n := by exact_mod_cast hDn
  rw [← Nat.cast_lt (α := ℝ)]
  push_cast
  calc ((⌊C * B⌋₊ : ℝ) + 1) ^ D ≤ (C * (B + 1)) ^ D := by
        gcongr
        linarith [Nat.floor_le (by positivity : 0 ≤ C * B)]
    _ = (C ^ ((D : ℝ) / (n - D))) ^ ((n : ℝ) - D) * (B + 1) ^ D := by
        rw [mul_pow, ← rpow_mul (by positivity), div_mul_cancel₀ _ (by linarith), rpow_natCast]
    _ < (B + 1) ^ ((n : ℝ) - D) * (B + 1) ^ D := by gcongr
    _ = (B + 1) ^ n := by
        rw [← rpow_natCast _ D, ← rpow_add (by positivity), sub_add_cancel, rpow_natCast]

/-- For `t > 0`, `(1 + t ^ 2) ^ (-k / 2) ≤ 1 / t ^ k`. -/
theorem one_add_sq_rpow_neg_le {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (1 + t ^ 2) ^ (-(k : ℝ) / 2) ≤ 1 / t ^ k := by
  have hpow : t ^ k ≤ (1 + t ^ 2) ^ ((k : ℝ) / 2) := by
    calc t ^ k = (t ^ 2) ^ ((k : ℝ) / 2) := by
          rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul ht.le]
          ring_nf
      _ ≤ _ := rpow_le_rpow (by positivity) (by linarith) (by positivity)
  rw [neg_div, rpow_neg (by positivity), ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hpow

/-- If `0 < d` and `2 ≤ d ^ (p - 2)`, then `d ^ (-p) ≤ 1 / (2 d ^ 2)`. -/
theorem rpow_neg_le_one_div_two_mul_sq {d p : ℝ} (hd : 0 < d) (h2 : 2 ≤ d ^ (p - 2)) :
    d ^ (-p) ≤ 1 / (2 * d ^ 2) := by
  have hsplit : d ^ (-p) = (d ^ (p - 2))⁻¹ * (d ^ 2)⁻¹ := by
    rw [← rpow_neg hd.le, ← rpow_natCast, ← rpow_neg hd.le, ← rpow_add hd]
    congr 1
    push_cast
    ring
  rw [hsplit, one_div, mul_inv]
  gcongr

/-- The logarithmic form of `q ^ p < q (q + q')`: if moreover `2 ≤ q ≤ q'` and
`log 2 < (p - 1 - t) log q`, then `t < log q' / log q`. -/
theorem lt_log_div_log_of_rpow_lt {q q' p t : ℝ} (hq : 2 ≤ q) (hqq' : q ≤ q')
    (hpow : q ^ p < q * (q + q')) (hlog2 : log 2 < (p - 1 - t) * log q) :
    t < log q' / log q := by
  have hq0 : 0 < q := by linarith
  have hlog : 0 < log q := log_pos (by linarith)
  have hpow' : q ^ (p - 1) < 2 * q' := by
    rw [rpow_sub_one hq0.ne', div_lt_iff₀ hq0]
    nlinarith
  have hlogs : (p - 1) * log q < log 2 + log q' := by
    rw [← log_rpow hq0, ← log_mul two_ne_zero (by linarith)]
    exact log_lt_log (rpow_pos_of_pos hq0 _) hpow'
  rw [lt_div_iff₀ hlog]
  nlinarith

end Real

namespace TauCeti

/-- The weight `(1 + ‖x‖) ^ s` is subadditive up to a constant: for `s ≥ 0`,
`(1 + ‖x + y‖) ^ s ≤ 2 ^ s ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s)`. -/
theorem one_add_norm_add_rpow_le {E : Type*} [SeminormedAddGroup E] {s : ℝ} (hs : 0 ≤ s)
    (x y : E) :
    (1 + ‖x + y‖) ^ s ≤ 2 ^ s * ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s) := by
  have hx : 0 ≤ 1 + ‖x‖ := by positivity
  have hy : 0 ≤ 1 + ‖y‖ := by positivity
  calc (1 + ‖x + y‖) ^ s ≤ (2 * max (1 + ‖x‖) (1 + ‖y‖)) ^ s := by
        gcongr
        linarith [norm_add_le x y, le_max_left (1 + ‖x‖) (1 + ‖y‖),
          le_max_right (1 + ‖x‖) (1 + ‖y‖)]
    _ = 2 ^ s * max (1 + ‖x‖) (1 + ‖y‖) ^ s :=
        Real.mul_rpow zero_le_two (hx.trans (le_max_left _ _))
    _ ≤ 2 ^ s * ((1 + ‖x‖) ^ s + (1 + ‖y‖) ^ s) := by
        gcongr
        rcases le_total (1 + ‖x‖) (1 + ‖y‖) with h | h
        · rw [max_eq_right h]
          exact le_add_of_nonneg_left (Real.rpow_nonneg hx s)
        · rw [max_eq_left h]
          exact le_add_of_nonneg_right (Real.rpow_nonneg hy s)

end TauCeti
