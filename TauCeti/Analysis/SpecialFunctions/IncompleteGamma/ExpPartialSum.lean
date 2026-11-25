/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Artanh
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# The normalized exponential partial sums `e^{-nx} e_n(nx)`

Write `e_n(y) = ∑_{k ≤ n} y ^ k / k!` for the `n`th partial sum of the exponential series
(DLMF 8.4.11). For `y ≥ 0` the quantity `e^{-y} e_n(y)` is the regularized upper incomplete Gamma
function `Q(n + 1, y) = 1 - P(n + 1, y)`, the probability that a Poisson variable of mean `y` is at
most `n`. This file proves the limits DLMF 8.11.13 of these normalized partial sums along the rays
`y = n x`:

* `e^{-nx} e_n(nx) → 1` for `0 ≤ x < 1`;
* `e^{-n} e_n(n) → 1 / 2`;
* `e^{-nx} e_n(nx) → 0` for `x > 1`.

The cases `x ≠ 1` follow from Chernoff-type bounds on the two tails of the exponential series,
which are proved here for every `n` and `y`: `e^{-y} e_n(y) ≤ (y / n) ^ n e^{n - y}` for `n ≤ y`,
and `1 - e^{-y} e_n(y) ≤ (y / (n + 1)) ^ (n + 1) e^{n + 1 - y}` for `0 ≤ y ≤ n + 1`.

The case `x = 1` is Ramanujan's problem. Through `n! (1 - e^{-y} e_n(y)) = ∫₀ʸ tⁿ e^{-t} dt`
(`TauCeti.integral_pow_mul_exp_neg`), the two quantities `e^{-n} e_n(n)` and `1 - e^{-n} e_n(n)`
are the masses of `tⁿ e^{-t} dt / n!` to the right and to the left of its mode `t = n`. Reflecting
the left half onto the right half, the density at `n - s` is at most the density at `n + s`
(`tanh u ≤ u`), and for `s ≤ n v` with `v ≤ 1 / 8` it is at least
`exp (-(8 / 3) n v³)` times it (`log ((1 + u) / (1 - u)) ≤ 2u + (8 / 3) u³`). Together with the
tail bound beyond `n + n v`, this gives
`0 ≤ 2 e^{-n} e_n(n) - 1 ≤ (8 / 3) n v³ + e^{-n v² / 4}`, and `v = n^{-2/5}` sends both terms to
`0`.

## Main results

* `TauCeti.exp_neg_mul_sum_pow_div_factorial_le_of_le`: for `n ≤ y`,
  `e^{-y} e_n(y) ≤ (y / n) ^ n e^{n - y}`.
* `TauCeti.one_sub_exp_neg_mul_sum_pow_div_factorial_le_of_le`: for `0 ≤ y ≤ n + 1`,
  `1 - e^{-y} e_n(y) ≤ (y / (n + 1)) ^ (n + 1) e^{n + 1 - y}`.
* `TauCeti.one_le_two_mul_exp_neg_mul_sum_pow_div_factorial_self`: `e_n(n) ≥ eⁿ / 2`.
* `TauCeti.two_mul_exp_neg_mul_sum_pow_div_factorial_self_sub_one_le`: for `0 ≤ v ≤ 1 / 8`,
  `2 e^{-n} e_n(n) - 1 ≤ (8 / 3) n v³ + e^{-n v² / 4}`.
* `TauCeti.tendsto_exp_neg_mul_sum_pow_div_factorial_of_lt_one`,
  `TauCeti.tendsto_exp_neg_mul_sum_pow_div_factorial_self`,
  `TauCeti.tendsto_exp_neg_mul_sum_pow_div_factorial_of_one_lt`: DLMF 8.11.13.

## References

* NIST *Digital Library of Mathematical Functions*, 8.4.11 and 8.11.13,
  <https://dlmf.nist.gov/8.11>.
* S. Ramanujan, Question 294, *J. Indian Math. Soc.* 3 (1911), 128; G. Szegő, Über einige von
  S. Ramanujan gestellte Aufgaben, *J. London Math. Soc.* 3 (1928), 225–232.
-/

public section

open Filter Finset Real Topology
open scoped Nat

namespace TauCeti

/-! ### Chernoff bounds for the two tails of the exponential series -/

/-- **The lower tail of the exponential series.** For `n ≤ y`, the probability
`e^{-y} ∑_{k ≤ n} y ^ k / k!` that a Poisson variable of mean `y` is at most `n` is at most
`(y / n) ^ n e^{n - y}`. -/
theorem exp_neg_mul_sum_pow_div_factorial_le_of_le {n : ℕ} {y : ℝ} (hny : (n : ℝ) ≤ y) :
    rexp (-y) * ∑ k ∈ range (n + 1), y ^ k / k ! ≤ (y / n) ^ n * rexp (n - y) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hc : 1 ≤ y / n := (one_le_div hn').2 hny
  have hsum : ∑ k ∈ range (n + 1), y ^ k / k ! ≤
      (y / n) ^ n * ∑ k ∈ range (n + 1), (n : ℝ) ^ k / k ! := by
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    rw [show y ^ k = (y / n) ^ k * (n : ℝ) ^ k by rw [← mul_pow, div_mul_cancel₀ _ hn'.ne'],
      mul_div_assoc]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hc (Nat.lt_succ_iff.1 (mem_range.1 hk))) (by positivity)
  calc rexp (-y) * ∑ k ∈ range (n + 1), y ^ k / k !
      ≤ rexp (-y) * ((y / n) ^ n * rexp n) := by
        gcongr
        exact hsum.trans (mul_le_mul_of_nonneg_left (sum_le_exp_of_nonneg hn'.le _)
          (by positivity))
    _ = (y / n) ^ n * rexp (n - y) := by rw [sub_eq_neg_add, Real.exp_add]; ring

/-- **The upper tail of the exponential series.** For `0 ≤ y ≤ n + 1`, the probability
`1 - e^{-y} ∑_{k ≤ n} y ^ k / k!` that a Poisson variable of mean `y` exceeds `n` is at most
`(y / (n + 1)) ^ (n + 1) e^{n + 1 - y}`. -/
theorem one_sub_exp_neg_mul_sum_pow_div_factorial_le_of_le {n : ℕ} {y : ℝ} (hy : 0 ≤ y)
    (hyn : y ≤ n + 1) :
    1 - rexp (-y) * ∑ k ∈ range (n + 1), y ^ k / k ! ≤
      (y / (n + 1)) ^ (n + 1) * rexp (n + 1 - y) := by
  have hm : (0 : ℝ) < n + 1 := by positivity
  set c := y / (n + 1) with hc_def
  have hc0 : 0 ≤ c := div_nonneg hy hm.le
  have hc1 : c ≤ 1 := (div_le_one hm).2 hyn
  -- The tails `∑_{k > n}` of the exponential series at `y` and at `n + 1`.
  have hy_tail := (hasSum_nat_add_iff' (n + 1)).2
    (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) y)
  have hm_tail := (hasSum_nat_add_iff' (n + 1)).2
    (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) ((n : ℝ) + 1))
  rw [← Real.exp_eq_exp_ℝ] at hy_tail hm_tail
  have htail : rexp y - ∑ k ∈ range (n + 1), y ^ k / k ! ≤
      c ^ (n + 1) * (rexp (n + 1) - ∑ k ∈ range (n + 1), ((n : ℝ) + 1) ^ k / k !) := by
    refine hasSum_le (fun k => ?_) hy_tail (hm_tail.mul_left (c ^ (n + 1)))
    rw [show y = c * (n + 1) by rw [hc_def, div_mul_cancel₀ _ hm.ne'], mul_pow, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hc0 hc1 (by omega)) (by positivity)
  have hpos : 0 ≤ ∑ k ∈ range (n + 1), ((n : ℝ) + 1) ^ k / k ! := by positivity
  calc 1 - rexp (-y) * ∑ k ∈ range (n + 1), y ^ k / k !
      = rexp (-y) * (rexp y - ∑ k ∈ range (n + 1), y ^ k / k !) := by
        rw [mul_sub, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    _ ≤ rexp (-y) * (c ^ (n + 1) * rexp (n + 1)) := by
        gcongr
        exact htail.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    _ = c ^ (n + 1) * rexp (n + 1 - y) := by
        rw [show rexp ((n : ℝ) + 1 - y) = rexp (-y) * rexp (n + 1) by
          rw [← Real.exp_add]; ring_nf]
        ring

/-! ### The density `tⁿ e^{-t}` on either side of its mode -/

/-- The density `tᵐ e^{-t}` at `t = m (1 + v)` is `(m (1 + v) e^{-v})ᵐ e^{-m}`. -/
private lemma pow_mul_exp_neg_eq (m : ℕ) (v : ℝ) :
    ((m : ℝ) + m * v) ^ m * rexp (-((m : ℝ) + m * v)) =
      ((m : ℝ) * ((1 + v) * rexp (-v))) ^ m * rexp (-m) := by
  simp only [mul_pow, ← Real.exp_natCast_mul]
  rw [show -((m : ℝ) + m * v) = m * -v + -m by ring, Real.exp_add,
    show (m : ℝ) + m * v = m * (1 + v) by ring, mul_pow]
  ring

/-- The density `tᵐ e^{-t}` at `t = m (1 - u)` is `(m (1 - u) e^u)ᵐ e^{-m}`. -/
private lemma pow_mul_exp_neg_sub_eq (m : ℕ) (u : ℝ) :
    ((m : ℝ) - m * u) ^ m * rexp (-((m : ℝ) - m * u)) =
      ((m : ℝ) * ((1 - u) * rexp u)) ^ m * rexp (-m) := by
  simpa [sub_eq_add_neg] using pow_mul_exp_neg_eq m (-u)

/-- **Reflection about the mode.** For `0 ≤ s ≤ m`, the density `tᵐ e^{-t}` at `m - s` is at most
its value at `m + s`. -/
private lemma pow_mul_exp_neg_sub_le (m : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hsm : s ≤ m) :
    ((m : ℝ) - s) ^ m * rexp (-((m : ℝ) - s)) ≤ ((m : ℝ) + s) ^ m * rexp (-((m : ℝ) + s)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [le_antisymm (by simpa using hsm) hs0]
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  obtain ⟨u, rfl⟩ : ∃ u, s = m * u := ⟨s / m, by rw [mul_div_cancel₀ _ hm'.ne']⟩
  have hu0 : 0 ≤ u := (mul_nonneg_iff_of_pos_left hm').1 hs0
  rw [pow_mul_exp_neg_sub_eq, pow_mul_exp_neg_eq]
  have hu1 : u ≤ 1 := (mul_le_iff_le_one_right hm').1 hsm
  have : 0 ≤ (m : ℝ) * ((1 - u) * rexp u) :=
    mul_nonneg hm'.le (mul_nonneg (by linarith) (Real.exp_pos u).le)
  have := Real.one_sub_mul_exp_le_one_add_mul_exp_neg hu0
  gcongr

/-- **Comparison near the mode.** For `0 ≤ s ≤ m / 2`, the density `tᵐ e^{-t}` at `m + s` is at
most `exp ((8 / 3) m (s / m)³)` times its value at `m - s`, written with `s = m u`. -/
private lemma pow_mul_exp_neg_add_le (m : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    ((m : ℝ) + m * u) ^ m * rexp (-((m : ℝ) + m * u)) ≤
      rexp (8 / 3 * m * u ^ 3) * (((m : ℝ) - m * u) ^ m * rexp (-((m : ℝ) - m * u))) := by
  rw [pow_mul_exp_neg_sub_eq, pow_mul_exp_neg_eq]
  calc ((m : ℝ) * ((1 + u) * rexp (-u))) ^ m * rexp (-m)
      ≤ (rexp (8 / 3 * u ^ 3) * (m * ((1 - u) * rexp u))) ^ m * rexp (-m) := by
        gcongr ?_ ^ _ * _
        rw [mul_left_comm (rexp (8 / 3 * u ^ 3))]
        exact mul_le_mul_of_nonneg_left
          (Real.one_add_mul_exp_neg_le_exp_mul_one_sub_mul_exp hu0 hu1) m.cast_nonneg
    _ = _ := by
        rw [mul_pow, show (8 / 3 : ℝ) * m * u ^ 3 = m * (8 / 3 * u ^ 3) by ring,
          Real.exp_natCast_mul]
        ring

/-- The mass of `tⁿ e^{-t} dt` on `[0, n]`, reflected about the mode `t = n`, is
`n! (1 - e^{-n} e_n(n))`. -/
private lemma integral_reflect_left (n : ℕ) :
    ∫ s in (0 : ℝ)..n, ((n : ℝ) - s) ^ n * rexp (-((n : ℝ) - s)) =
      n ! * (1 - rexp (-n) * ∑ k ∈ range (n + 1), (n : ℝ) ^ k / k !) := by
  have h := intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n * rexp (-t)) (n : ℝ)
    (a := 0) (b := n)
  simp only [sub_self, sub_zero] at h
  rw [h, integral_pow_mul_exp_neg]

/-- The mass of `tⁿ e^{-t} dt` on `[n, n + w]`, translated to `[0, w]`, is
`n! (e^{-n} e_n(n) - e^{-(n + w)} e_n(n + w))`. -/
private lemma integral_reflect_right (n : ℕ) (w : ℝ) :
    ∫ s in (0 : ℝ)..w, ((n : ℝ) + s) ^ n * rexp (-((n : ℝ) + s)) =
      n ! * (rexp (-n) * (∑ k ∈ range (n + 1), (n : ℝ) ^ k / k !) -
        rexp (-((n : ℝ) + w)) * ∑ k ∈ range (n + 1), ((n : ℝ) + w) ^ k / k !) := by
  have hf : Continuous fun t : ℝ => t ^ n * rexp (-t) := by fun_prop
  have h := intervalIntegral.integral_comp_add_left (fun t : ℝ => t ^ n * rexp (-t)) (n : ℝ)
    (a := 0) (b := w)
  simp only [add_zero] at h
  rw [h, ← intervalIntegral.integral_interval_sub_left
    (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 ((n : ℝ) + w))
    (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 (n : ℝ)),
    integral_pow_mul_exp_neg, integral_pow_mul_exp_neg]
  ring

/-! ### Ramanujan's problem: `e^{-n} e_n(n) → 1 / 2` -/

/-- **`e_n(n) ≥ eⁿ / 2`**: a Poisson variable of integer mean `n` is at most `n` with probability
at least `1 / 2`. -/
theorem one_le_two_mul_exp_neg_mul_sum_pow_div_factorial_self (n : ℕ) :
    1 ≤ 2 * (rexp (-n) * ∑ k ∈ range (n + 1), (n : ℝ) ^ k / k !) := by
  have hmono : ∫ s in (0 : ℝ)..n, ((n : ℝ) - s) ^ n * rexp (-((n : ℝ) - s)) ≤
      ∫ s in (0 : ℝ)..n, ((n : ℝ) + s) ^ n * rexp (-((n : ℝ) + s)) :=
    intervalIntegral.integral_mono_on n.cast_nonneg
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      fun s hs => pow_mul_exp_neg_sub_le n hs.1 hs.2
  rw [integral_reflect_left, integral_reflect_right n n] at hmono
  have hT : 0 ≤ rexp (-(n + n : ℝ)) * ∑ k ∈ range (n + 1), ((n : ℝ) + n) ^ k / k ! := by
    positivity
  have hfac : (0 : ℝ) < n ! := by positivity
  nlinarith

/-- On `[0, n v]` with `v ≤ 1 / 2`, the left half of `tⁿ e^{-t}` reflected about the mode carries
at least `e^{-(8 / 3) n v³}` times the mass of the right half. -/
private lemma exp_neg_mul_integral_reflect_right_le {n : ℕ} (hn : 0 < n) {v : ℝ} (hv0 : 0 ≤ v)
    (hv : v ≤ 1 / 2) :
    rexp (-(8 / 3 * n * v ^ 3)) *
        ∫ s in (0 : ℝ)..(n * v), ((n : ℝ) + s) ^ n * rexp (-((n : ℝ) + s)) ≤
      ∫ s in (0 : ℝ)..(n * v), ((n : ℝ) - s) ^ n * rexp (-((n : ℝ) - s)) := by
  have hN : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by positivity)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs => ?_
  obtain ⟨u, rfl⟩ : ∃ u, s = n * u := ⟨s / n, by rw [mul_div_cancel₀ _ hN.ne']⟩
  have hu0 : 0 ≤ u := (mul_nonneg_iff_of_pos_left hN).1 hs.1
  have huv : u ≤ v := (mul_le_mul_iff_of_pos_left hN).1 hs.2
  have hf0 : 0 ≤ ((n : ℝ) - n * u) ^ n * rexp (-((n : ℝ) - n * u)) := by
    have : 0 ≤ (n : ℝ) - n * u := by nlinarith
    positivity
  have hε : 8 / 3 * n * u ^ 3 ≤ 8 / 3 * n * v ^ 3 := by gcongr
  calc rexp (-(8 / 3 * n * v ^ 3)) * (((n : ℝ) + n * u) ^ n * rexp (-((n : ℝ) + n * u)))
      ≤ rexp (-(8 / 3 * n * v ^ 3)) *
          (rexp (8 / 3 * n * v ^ 3) * (((n : ℝ) - n * u) ^ n * rexp (-((n : ℝ) - n * u)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact (pow_mul_exp_neg_add_le n hu0 (by linarith)).trans
          (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hε) hf0)
    _ = ((n : ℝ) - n * u) ^ n * rexp (-((n : ℝ) - n * u)) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- The lower tail at `n + n v`: for `0 ≤ v ≤ 1 / 8`,
`e^{-(n + n v)} e_n(n + n v) ≤ e^{-n v² / 4}`. -/
private lemma exp_neg_mul_sum_pow_div_factorial_add_le {n : ℕ} (hn : 0 < n) {v : ℝ}
    (hv0 : 0 ≤ v) (hv : v ≤ 1 / 8) :
    rexp (-((n : ℝ) + n * v)) * ∑ k ∈ range (n + 1), ((n : ℝ) + n * v) ^ k / k ! ≤
      rexp (-(n * v ^ 2 / 4)) := by
  have : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine (exp_neg_mul_sum_pow_div_factorial_le_of_le (by nlinarith)).trans ?_
  rw [show ((n : ℝ) + n * v) / n = 1 + v by field_simp,
    show (n : ℝ) - (n + n * v) = n * -v by ring, Real.exp_natCast_mul, ← mul_pow]
  calc ((1 + v) * rexp (-v)) ^ n ≤ (rexp (v - v ^ 2 / 4) * rexp (-v)) ^ n := by
        gcongr
        exact Real.one_add_le_exp_sub_sq_div_four hv0 hv
    _ = rexp (-(n * v ^ 2 / 4)) := by
        rw [← Real.exp_add, ← Real.exp_natCast_mul]; ring_nf

/-- **A quantitative form of Ramanujan's limit.** For `0 ≤ v ≤ 1 / 8`,
`2 e^{-n} e_n(n) - 1 ≤ (8 / 3) n v³ + e^{-n v² / 4}`. -/
theorem two_mul_exp_neg_mul_sum_pow_div_factorial_self_sub_one_le (n : ℕ) {v : ℝ}
    (hv0 : 0 ≤ v) (hv : v ≤ 1 / 8) :
    2 * (rexp (-n) * ∑ k ∈ range (n + 1), (n : ℝ) ^ k / k !) - 1 ≤
      8 / 3 * n * v ^ 3 + rexp (-(n * v ^ 2 / 4)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  have hN : (0 : ℝ) < n := Nat.cast_pos.2 hn
  -- Dropping `[n v, n]` from the reflected left mass.
  have hdrop : ∫ s in (0 : ℝ)..(n * v), ((n : ℝ) - s) ^ n * rexp (-((n : ℝ) - s)) ≤
      ∫ s in (0 : ℝ)..n, ((n : ℝ) - s) ^ n * rexp (-((n : ℝ) - s)) := by
    refine intervalIntegral.integral_mono_interval le_rfl (by positivity)
      (mul_le_of_le_one_right hN.le (by linarith)) ?_
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun s hs => ?_)
    have : 0 ≤ (n : ℝ) - s := by linarith [hs.2]
    positivity
  -- `e^{-ε} n! (a - T) ≤ n! (1 - a)`, with `a = e^{-n} e_n(n)` and `T` the tail beyond `n + n v`.
  have hkey := (exp_neg_mul_integral_reflect_right_le hn hv0 (by linarith)).trans hdrop
  rw [integral_reflect_right, integral_reflect_left] at hkey
  have hT := exp_neg_mul_sum_pow_div_factorial_add_le hn hv0 hv
  have ha1 := exp_neg_mul_sum_pow_div_factorial_le_one n hN.le
  have ha0 : 0 ≤ rexp (-n) * ∑ k ∈ range (n + 1), (n : ℝ) ^ k / k ! := by positivity
  have hT0 : 0 ≤ rexp (-((n : ℝ) + n * v)) * ∑ k ∈ range (n + 1), ((n : ℝ) + n * v) ^ k / k ! := by
    positivity
  generalize rexp (-n) * ∑ k ∈ range (n + 1), (n : ℝ) ^ k / k ! = a at hkey ha0 ha1 ⊢
  generalize rexp (-((n : ℝ) + n * v)) * ∑ k ∈ range (n + 1), ((n : ℝ) + n * v) ^ k / k ! = T
    at hkey hT hT0
  generalize hε : 8 / 3 * (n : ℝ) * v ^ 3 = ε at hkey ⊢
  have hε0 : 0 ≤ ε := hε ▸ by positivity
  have hkey' : rexp (-ε) * (a - T) ≤ 1 - a := by
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < n !)
    linear_combination hkey
  have h1 := Real.add_one_le_exp (-ε)
  have h2 : rexp (-ε) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right h1 ha0, mul_le_mul_of_nonneg_right h2 hT0,
    mul_le_mul_of_nonneg_left ha1 hε0]

/-! ### The limits DLMF 8.11.13 -/

/-- **DLMF 8.11.13 for `0 ≤ x < 1`**: `e^{-nx} e_n(nx) → 1` as `n → ∞`. -/
theorem tendsto_exp_neg_mul_sum_pow_div_factorial_of_lt_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    Tendsto (fun n : ℕ => rexp (-(n * x)) * ∑ k ∈ range (n + 1), ((n : ℝ) * x) ^ k / k !)
      atTop (𝓝 1) := by
  have hr0 : 0 ≤ x * rexp (1 - x) := by positivity
  have hlim : Tendsto (fun n : ℕ => x * rexp 1 * (x * rexp (1 - x)) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0
      (mul_exp_one_sub_lt_one hx.ne)).const_mul (x * rexp 1)
  have hsub : Tendsto (fun n : ℕ =>
      1 - rexp (-(n * x)) * ∑ k ∈ range (n + 1), ((n : ℝ) * x) ^ k / k !) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim
    · exact sub_nonneg.2 (exp_neg_mul_sum_pow_div_factorial_le_one n (by positivity))
    · have hnx : (n : ℝ) * x / (n + 1) ≤ x := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      calc 1 - rexp (-(n * x)) * ∑ k ∈ range (n + 1), ((n : ℝ) * x) ^ k / k !
          ≤ ((n : ℝ) * x / (n + 1)) ^ (n + 1) * rexp (n + 1 - n * x) :=
            one_sub_exp_neg_mul_sum_pow_div_factorial_le_of_le (by positivity) (by nlinarith)
        _ ≤ x ^ (n + 1) * rexp (n + 1 - n * x) := by gcongr
        _ = x * rexp 1 * (x * rexp (1 - x)) ^ n := by
            rw [show (n : ℝ) + 1 - n * x = n * (1 - x) + 1 by ring, Real.exp_add,
              Real.exp_natCast_mul]
            ring
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsub

/-- **Ramanujan's limit, DLMF 8.11.13 for `x = 1`**: `e^{-n} e_n(n) → 1 / 2` as `n → ∞`. -/
theorem tendsto_exp_neg_mul_sum_pow_div_factorial_self :
    Tendsto (fun n : ℕ => rexp (-n) * ∑ k ∈ range (n + 1), (n : ℝ) ^ k / k !) atTop
      (𝓝 (1 / 2)) := by
  have hv : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(2 / 5 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hε : Tendsto (fun n : ℕ => 8 / 3 * (n : ℝ) ^ (-(1 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (8 / 3 : ℝ)
  have hT : Tendsto (fun n : ℕ => rexp (-((n : ℝ) ^ (1 / 5 : ℝ) / 4))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop).atTop_div_const
        (by norm_num)))
  have h2 : Tendsto (fun n : ℕ =>
      2 * (rexp (-n) * ∑ k ∈ range (n + 1), (n : ℝ) ^ k / k !) - 1) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => by
      linarith [one_le_two_mul_exp_neg_mul_sum_pow_div_factorial_self n]) ?_
      (by simpa only [add_zero] using hε.add hT)
    filter_upwards [eventually_ge_atTop 1,
      hv.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with n hn hvn
    have hN : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have h := two_mul_exp_neg_mul_sum_pow_div_factorial_self_sub_one_le n
      (Real.rpow_nonneg hN.le _) hvn
    have e3 : (n : ℝ) * ((n : ℝ) ^ (-(2 / 5 : ℝ))) ^ 3 = (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
      rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_one_add' hN.le (by norm_num)]
      norm_num
    have e2 : (n : ℝ) * ((n : ℝ) ^ (-(2 / 5 : ℝ))) ^ 2 = (n : ℝ) ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_one_add' hN.le (by norm_num)]
      norm_num
    rwa [mul_assoc, e3, e2] at h
  simpa using (h2.add_const 1).div_const 2

/-- **DLMF 8.11.13 for `x > 1`**: `e^{-nx} e_n(nx) → 0` as `n → ∞`. -/
theorem tendsto_exp_neg_mul_sum_pow_div_factorial_of_one_lt {x : ℝ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => rexp (-(n * x)) * ∑ k ∈ range (n + 1), ((n : ℝ) * x) ^ k / k !)
      atTop (𝓝 0) := by
  have : 0 ≤ x := by linarith
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (mul_exp_one_sub_lt_one hx.ne'))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hN : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine (exp_neg_mul_sum_pow_div_factorial_le_of_le (by nlinarith)).trans_eq ?_
  rw [mul_div_cancel_left₀ _ hN.ne', show (n : ℝ) - n * x = n * (1 - x) by ring,
    Real.exp_natCast_mul, mul_pow]

end TauCeti
