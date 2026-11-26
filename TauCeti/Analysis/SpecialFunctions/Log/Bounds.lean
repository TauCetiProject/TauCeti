/-
Copyright (c) 2026 Matteo Cipollina, The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Elementary bounds for the real logarithm

From `log x ≤ x - 1` for `x > 0` (`Real.log_le_sub_one_of_pos`) applied at `x = 2` and `x / 2`,
one obtains `log 4 = 2 log 2 ≤ 2` and `log x / x ≤ 1 / 2` for every real `x ≥ 0` (holding at
`x = 0` via `0 / 0 = 0`). The first compares explicit prime-counting constants involving `log 4`
with rational constants, and the second bounds the contribution `log p / p` of a single prime at a
real cutoff `x` when passing between inclusive and strict prime sums. From `e² < (3 / 2) ^ 5`
(Mathlib's `Real.exp_one_lt_d9`) one obtains `log (3 / 2) > 2 / 5`
(`Real.two_fifths_lt_log_three_halves`), which locates the zero of the unoffset logarithmic
integral below `3 / 2`.

Near `1` from below, `|log x| ≤ 2 (1 - x)` for `1 / 2 ≤ x ≤ 1`
(`Real.abs_log_le_two_mul_one_sub`), which turns exponential decay of `1 - x` into exponential
decay of `log x`, as for the modulus `|α|²` of a section tending to one.

`Real.neg_log_le_sqrt_two_div` bounds `-log x` by `sqrt (2 / x)` for every `x ≥ 0`,
including the totalized value at zero. `Real.posLog_le_sqrt_two_mul_abs` bounds
`posLog x` by `sqrt (2 * |x|)` for every real `x`.
Applied to reciprocal distances, these inequalities dominate logarithmic singularities by
inverse-square-root kernels. Their integrals control dyadic averages and the choice of circles
in Hadamard minimum-modulus estimates.

`Real.sq_log_mul_exp_one_le_sixteen_mul_sqrt` squares `e y ≤ exp y` (`Real.exp_one_mul_le_exp`)
at `y = log x / 4`: since `L² e^{−L/2}` peaks at `L = 4` with value `16 / e²`, the square of the
logarithm is at most `16 √x / e²` for `x ≥ 1`. This bounds the prime powers that are not primes
in explicit prime-counting estimates.

## Main results

* `Real.log_four_le_two`: `log 4 ≤ 2`.
* `Real.two_fifths_lt_log_three_halves`: `2 / 5 < log (3 / 2)`.
* `Real.log_div_self_le_half`: `log x / x ≤ 1 / 2` for every nonnegative real `x`.
* `Real.abs_log_le_two_mul_one_sub`: `|log x| ≤ 2 (1 - x)` for `1 / 2 ≤ x ≤ 1`.
* `Real.neg_log_le_sqrt_two_div`: `-log x ≤ sqrt (2 / x)` for every nonnegative real `x`.
* `Real.posLog_le_sqrt_two_mul_abs`: `posLog x ≤ sqrt (2 * |x|)` for every real `x`.
* `Real.sq_log_mul_exp_one_le_sixteen_mul_sqrt`: `(log x · e)² ≤ 16 √x` for `x ≥ 1`.
* `Real.mul_log_natCast_div_le_log_of_pow_le_mul_pow`: a logarithmic bound from a
  cross-multiplied comparison of natural powers.
* `Real.sub_sq_div_two_le_log_one_add`: `u - u ^ 2 / 2 ≤ log (1 + u)` for `0 ≤ u`.
* `TauCeti.Real.artanhPartial`, `TauCeti.Real.two_mul_artanhPartial_le_log`,
  `TauCeti.Real.log_le_two_mul_artanhPartial_add`,
  `TauCeti.Real.neg_two_mul_artanhPartial_add_le_log`,
  `TauCeti.Real.log_le_neg_two_mul_artanhPartial`: two-sided rational enclosures for `Real.log` via
  `artanh` partial sums.
-/

public section

namespace Real

/-- The natural logarithm of `4` is at most `2`. -/
theorem log_four_le_two : log 4 ≤ 2 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, log_pow]
  norm_num
  linarith [log_le_sub_one_of_pos zero_lt_two]

/-- `2 / 5 < log (3 / 2)`, from `e² < (3 / 2) ^ 5` and `e < 2.7182818286`. -/
theorem two_fifths_lt_log_three_halves : (2 / 5 : ℝ) < log (3 / 2) := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  refine (pow_lt_pow_iff_left₀ (exp_pos _).le (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)).1 ?_
  rw [← exp_natCast_mul, show ((5 : ℕ) : ℝ) * (2 / 5) = (2 : ℕ) * 1 by norm_num, exp_natCast_mul]
  have h := exp_one_lt_d9
  have h0 := (exp_pos 1).le
  nlinarith

/-- For every nonnegative real `x`, `log x / x ≤ 1 / 2` (holding at `x = 0` via `0 / 0 = 0`). -/
theorem log_div_self_le_half {x : ℝ} (hx : 0 ≤ x) : log x / x ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  have h := log_le_sub_one_of_pos (half_pos hx)
  rw [log_div hx.ne' two_ne_zero] at h
  rw [div_le_iff₀ hx]
  linarith [log_le_sub_one_of_pos zero_lt_two]

/-- Near `1` from below the logarithm is controlled by the distance to `1`: for `1 / 2 ≤ x ≤ 1`,
`|log x| ≤ 2 (1 - x)`. -/
theorem abs_log_le_two_mul_one_sub {x : ℝ} (hx : 1 / 2 ≤ x) (hx₁ : x ≤ 1) :
    |log x| ≤ 2 * (1 - x) := by
  have hx₀ : 0 < x := by linarith
  -- `-log x = log x⁻¹ ≤ x⁻¹ - 1 = (1 - x) / x ≤ 2 (1 - x)`.
  have h := log_le_sub_one_of_pos (inv_pos.mpr hx₀)
  rw [log_inv, inv_eq_one_div, div_sub_one hx₀.ne', le_div_iff₀ hx₀] at h
  rw [abs_of_nonpos (log_nonpos hx₀.le hx₁)]
  nlinarith

/-- The negative logarithm is bounded by an inverse-square-root majorant on the nonnegative
half-line, including its totalized value at zero. -/
theorem neg_log_le_sqrt_two_div {x : ℝ} (hx : 0 ≤ x) :
    -Real.log x ≤ Real.sqrt (2 / x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  by_cases ht : 0 ≤ -Real.log x
  · have hmain : (-Real.log x) ^ 2 / 2 ≤ Real.exp (-Real.log x) := by
      simpa using Real.pow_div_factorial_le_exp (-Real.log x) ht 2
    have hexp : Real.exp (-Real.log x) = x⁻¹ := by
      simp [Real.exp_neg, Real.exp_log hx]
    have hsq : (-Real.log x) ^ 2 ≤ 2 / x := by
      rw [hexp] at hmain
      rw [div_eq_mul_inv]
      nlinarith [hmain]
    exact (Real.le_sqrt ht (div_nonneg (by norm_num) hx.le)).2 hsq
  · exact (lt_of_not_ge ht).le.trans (Real.sqrt_nonneg _)

/-- The positive logarithm is bounded by a square-root majorant, including zero. -/
theorem posLog_le_sqrt_two_mul_abs (x : ℝ) : Real.posLog x ≤ Real.sqrt (2 * |x|) := by
  rw [Real.posLog_apply]
  refine max_le (Real.sqrt_nonneg _) ?_
  simpa only [Real.log_inv, neg_neg, div_inv_eq_mul, Real.log_abs] using
    (neg_log_le_sqrt_two_div (inv_nonneg.mpr (abs_nonneg x)))

/-- For `x ≥ 1`, `(log x · e)² ≤ 16 √x`: the maximum of `L² e^{−L/2}` is `16/e²`, at `L = 4`. -/
theorem sq_log_mul_exp_one_le_sixteen_mul_sqrt {x : ℝ} (hx : 1 ≤ x) :
    (log x * exp 1) ^ 2 ≤ 16 * √x := by
  have hsqrt : √x = exp (log x / 4) ^ 2 := by
    rw [sqrt_eq_iff_mul_self_eq_of_pos (by positivity), ← pow_add, ← exp_natCast_mul,
      show ((2 + 2 : ℕ) : ℝ) * (log x / 4) = log x by push_cast; ring, exp_log (by linarith)]
  have h := pow_le_pow_left₀ (by have := log_nonneg hx; positivity)
    (exp_one_mul_le_exp (x := log x / 4)) 2
  rw [hsqrt]
  nlinarith

/-- An upper bound on a power of a ratio of natural numbers gives a logarithmic bound
with any nonnegative coefficient at most the exponent, including when the ratio is zero. -/
theorem mul_log_natCast_div_le_log_of_pow_le_mul_pow {p q m N : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (ham : a ≤ m) (hpow : p ^ m ≤ N * q ^ m) :
    a * log ((p : ℝ) / q) ≤ log N := by
  by_cases hq : q = 0
  · simpa [hq] using log_natCast_nonneg N
  have hq' : 0 < (q : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hq)
  by_cases h : 1 ≤ (p : ℝ) / q
  · have hratio : ((p : ℝ) / q) ^ m ≤ N := by
      rw [div_pow, div_le_iff₀ (pow_pos hq' _)]
      exact_mod_cast hpow
    calc
      _ ≤ (m : ℝ) * log ((p : ℝ) / q) := mul_le_mul_of_nonneg_right ham (log_nonneg h)
      _ = log (((p : ℝ) / q) ^ m) := (log_pow _ _).symm
      _ ≤ _ := log_le_log (pow_pos (zero_lt_one.trans_le h) _) hratio
  · exact (mul_nonpos_of_nonneg_of_nonpos ha
      (log_nonpos (div_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q)) (le_of_not_ge h))).trans
      (log_natCast_nonneg N)

/-- Quadratic lower bound `u - u ^ 2 / 2 ≤ log (1 + u)` for all `u ≥ 0`. -/
theorem sub_sq_div_two_le_log_one_add {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 2 / 2 ≤ log (1 + u) := by
  let ψ (t : ℝ) : ℝ := log (1 + t) - (t - t ^ 2 / 2)
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) u, HasDerivAt ψ ((1 + t)⁻¹ - (1 - t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ ↦ log (1 + s)) (1 + t)⁻¹ t := by
      simpa using ((hasDerivAt_id t).const_add 1).log (by linarith [ht.1] : (1 : ℝ) + t ≠ 0)
    have h2 : HasDerivAt (fun s : ℝ ↦ s - s ^ 2 / 2) (1 - t) t := by
      simpa using (hasDerivAt_id t).fun_sub ((hasDerivAt_pow 2 t).div_const 2)
    exact h1.fun_sub h2
  have hψ_mono : MonotoneOn ψ (Set.Icc 0 u) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
      (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      fun t ht ↦ ?_
    rw [interior_Icc] at ht
    rw [(hderiv t ⟨ht.1.le, ht.2.le⟩).deriv, sub_nonneg, inv_eq_one_div,
      le_div_iff₀ (by linarith [ht.1] : 0 < 1 + t)]
    nlinarith [ht.1]
  have hψ0 := hψ_mono (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
  simp only [ψ, add_zero, log_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, sub_self, sub_nonneg] at hψ0
  exact hψ0

end Real

namespace TauCeti.Real

/-- Partial sum `∑ i < n, x ^ (2 * i + 1) / (2 * i + 1)` of `artanh x`, used in rational
enclosures of `Real.log` via `log a = 2 * artanh ((a - 1) / (a + 1))`. -/
noncomputable def artanhPartial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)

/-- Defining equation of `TauCeti.Real.artanhPartial`. -/
theorem artanhPartial_def (n : ℕ) (x : ℝ) :
    artanhPartial n x = ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1) :=
  (rfl)

private theorem artanh_arg_spec {a : ℝ} (ha : 1 ≤ a) :
    0 ≤ (a - 1) / (a + 1) ∧ (a - 1) / (a + 1) < 1 ∧
      (1 + (a - 1) / (a + 1)) / (1 - (a - 1) / (a + 1)) = a := by
  have ha1 : 0 < a + 1 := by linarith
  refine ⟨div_nonneg (by linarith) ha1.le, (div_lt_one ha1).mpr (by linarith), ?_⟩
  field_simp [ha1.ne']
  ring

/-- Lower rational enclosure `2 * artanhPartial n ((a - 1) / (a + 1)) ≤ log a` for `1 ≤ a`. -/
theorem two_mul_artanhPartial_le_log {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    2 * artanhPartial n ((a - 1) / (a + 1)) ≤ Real.log a := by
  obtain ⟨hx0, hx1, hdiv⟩ := artanh_arg_spec ha
  have hle := Real.sum_range_le_log_div hx0 hx1 n
  rw [hdiv] at hle
  rw [artanhPartial_def]
  linarith

/-- Upper rational enclosure of `log a` for `1 ≤ a` via `artanhPartial` and a geometric tail. -/
theorem log_le_two_mul_artanhPartial_add {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    Real.log a ≤ 2 * (artanhPartial n ((a - 1) / (a + 1)) +
      ((a - 1) / (a + 1)) ^ (2 * n + 1) / (1 - ((a - 1) / (a + 1)) ^ 2)) := by
  obtain ⟨hx0, hx1, hdiv⟩ := artanh_arg_spec ha
  have hle := Real.log_div_le_sum_range_add hx0 hx1 n
  rw [hdiv] at hle
  rw [artanhPartial_def]
  linarith

/-- Lower rational enclosure of `log a` for `0 < a ≤ 1` via `artanhPartial` and a geometric
tail. -/
theorem neg_two_mul_artanhPartial_add_le_log {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (n : ℕ) :
    -2 * (artanhPartial n ((1 - a) / (1 + a)) +
      ((1 - a) / (1 + a)) ^ (2 * n + 1) / (1 - ((1 - a) / (1 + a)) ^ 2)) ≤ Real.log a := by
  have hinv : 1 ≤ a⁻¹ := one_le_inv₀ ha0 |>.mpr ha1
  have harg : (a⁻¹ - 1) / (a⁻¹ + 1) = (1 - a) / (1 + a) := by
    field_simp [ha0.ne']
  have hle := log_le_two_mul_artanhPartial_add hinv n
  rw [Real.log_inv, harg] at hle
  linarith

/-- Upper rational enclosure `log a ≤ -2 * artanhPartial n ((1 - a) / (1 + a))` for `0 < a ≤ 1`.
-/
theorem log_le_neg_two_mul_artanhPartial {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (n : ℕ) :
    Real.log a ≤ -2 * artanhPartial n ((1 - a) / (1 + a)) := by
  have hinv : 1 ≤ a⁻¹ := one_le_inv₀ ha0 |>.mpr ha1
  have harg : (a⁻¹ - 1) / (a⁻¹ + 1) = (1 - a) / (1 + a) := by
    field_simp [ha0.ne']
  have hle := two_mul_artanhPartial_le_log hinv n
  rw [Real.log_inv, harg] at hle
  linarith

end TauCeti.Real
