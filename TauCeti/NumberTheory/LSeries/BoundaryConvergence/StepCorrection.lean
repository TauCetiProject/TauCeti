/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TauCeti.Analysis.Complex.LaplaceTransform

/-!
# The step correction of a bounded Dirichlet series

For coefficients `a : ℕ → ℂ`, the step function `t ↦ a ⌊exp t⌋₊` has, at least formally,
Laplace transform `∑ n ≥ 1, a n ∫ x in n..n+1, x ^ (-z - 1)`. Comparing each integral with the
value `n ^ (-z - 1)` at the left endpoint, this differs from the shifted Dirichlet series
`∑ n ≥ 1, a n n ^ (-z - 1)` by the *step correction*
`H z = ∑ n ≥ 1, a n (∫ x in n..n+1, x ^ (-z - 1) - n ^ (-z - 1))`.

Although the Dirichlet series itself only converges absolutely for `re z > 0`, the step
correction is holomorphic on the larger half-plane `-1 < re z` when `a` is bounded: by the mean
value theorem its `n`-th term is at most `‖a n‖ ‖z + 1‖ n ^ (-re z - 2)`. This is what lets the
bounded-Laplace (Newman) Tauberian theorem for the step function transfer to ordered partial sums
`∑ n ≤ N, a n / n` of the Dirichlet series at `s = 1`, where the step correction takes the
absolutely convergent value `∑ n ≥ 1, a n (log (1 + 1 / n) - 1 / n)`.

## Main declarations

* `TauCeti.LSeries.stepCorrectionTerm a n z`: the `n`-th term of the step correction, zero for
  `n = 0`;
* `TauCeti.LSeries.stepCorrection a z`: the step correction `H z`;
* `TauCeti.LSeries.norm_stepCorrectionTerm_le`: the mean value bound on the terms;
* `TauCeti.LSeries.hasSum_stepCorrection`: absolute convergence for `-1 < re z`;
* `TauCeti.LSeries.differentiableOn_stepCorrection`: holomorphy on `-1 < re z`;
* `TauCeti.LSeries.stepCorrection_zero`: the value `∑ a n (log (1 + 1 / n) - 1 / n)` at `0`.

## References

* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
* D. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104
  (1997), 705–708.
-/

public section

open Filter MeasureTheory Set Metric
open scoped Topology Complex Interval

namespace TauCeti.LSeries

variable {a : ℕ → ℂ} {M : ℝ} {z : ℂ}

/-- The `n`-th term of the step correction of the coefficients `a` at `z`: it is `0` for `n = 0`,
and otherwise `a n * (∫ x in n..n+1, x ^ (-z - 1) - n ^ (-z - 1))`, the difference between the
contribution of the step `[n, n + 1)` to the Laplace transform of `t ↦ a ⌊exp t⌋₊` and the
`n`-th term of the Dirichlet series of `a` at `z + 1`. -/
noncomputable def stepCorrectionTerm (a : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 0 else a n * ((∫ x in (n : ℝ)..n + 1, (x : ℂ) ^ (-z - 1)) - (n : ℂ) ^ (-z - 1))

/-- The step correction `∑ n ≥ 1, a n (∫ x in n..n+1, x ^ (-z - 1) - n ^ (-z - 1))` of the
coefficients `a`. For bounded `a` the series converges absolutely and is holomorphic on
`-1 < re z` (`hasSum_stepCorrection`, `differentiableOn_stepCorrection`). -/
noncomputable def stepCorrection (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n, stepCorrectionTerm a n z

/-- The `0`-th term of the step correction vanishes identically. -/
@[simp]
theorem stepCorrectionTerm_zero (a : ℕ → ℂ) : stepCorrectionTerm a 0 = 0 := by
  ext z
  simp [stepCorrectionTerm]

/-- For `n ≠ 0`, the `n`-th term of the step correction is
`a n * (∫ x in n..n+1, x ^ (-z - 1) - n ^ (-z - 1))`. -/
theorem stepCorrectionTerm_of_ne_zero (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    stepCorrectionTerm a n z =
      a n * ((∫ x in (n : ℝ)..n + 1, (x : ℂ) ^ (-z - 1)) - (n : ℂ) ^ (-z - 1)) := by
  simp only [stepCorrectionTerm, hn, ↓reduceIte]

/-- Each term of the step correction is entire in `z`. -/
theorem differentiable_stepCorrectionTerm (a : ℕ → ℂ) (n : ℕ) :
    Differentiable ℂ (stepCorrectionTerm a n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hint : Differentiable ℂ fun z : ℂ ↦ ∫ x in (n : ℝ)..n + 1, (x : ℂ) ^ (-z - 1) := by
    have hsubst := intervalIntegral_ofReal_cpow_neg_sub_one hn' (v := n + 1) (by positivity)
    simp_rw [hsubst]
    simpa using differentiable_intervalIntegral_mul_cexp_neg_mul (f := fun _ ↦ (1 : ℂ))
      (a := Real.log n) (b := Real.log (n + 1)) intervalIntegrable_const
  have hpow : Differentiable ℂ fun z : ℂ ↦ (n : ℂ) ^ (-z - 1) :=
    (differentiable_id.neg.sub_const 1).const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))
  have h : stepCorrectionTerm a n =
      fun z ↦ a n * ((∫ x in (n : ℝ)..n + 1, (x : ℂ) ^ (-z - 1)) - (n : ℂ) ^ (-z - 1)) :=
    funext (stepCorrectionTerm_of_ne_zero a hn)
  rw [h]
  exact (hint.sub hpow).const_mul _

/-- **Mean value bound.** For `-2 ≤ re z`, the `n`-th term of the step correction is at most
`‖a n‖ ‖z + 1‖ n ^ (-re z - 2)`: on `[n, n + 1]` the derivative `-(z + 1) x ^ (-z - 2)` of
`x ^ (-z - 1)` has norm at most `‖z + 1‖ n ^ (-re z - 2)`. -/
theorem norm_stepCorrectionTerm_le (a : ℕ → ℂ) (n : ℕ) (hz : -2 ≤ z.re) :
    ‖stepCorrectionTerm a n z‖ ≤ ‖a n‖ * ‖z + 1‖ * (n : ℝ) ^ (-z.re - 2) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [stepCorrectionTerm_zero, Pi.zero_apply, norm_zero]
    positivity
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  set C := ‖z + 1‖ * (n : ℝ) ^ (-z.re - 2) with hC
  -- the derivative of `x ↦ x ^ (-z - 1)` on `[n, n + 1]`
  have hderiv : ∀ x ∈ Icc (n : ℝ) (n + 1), HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (-z - 1))
      ((-z - 1) * (x : ℂ) ^ (-z - 1 - 1)) x := fun x hx ↦
    (Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr
      (hn'.trans_le hx.1))).hasDerivAt.comp_ofReal
  have hderiv_le : ∀ x ∈ Icc (n : ℝ) (n + 1), ‖(-z - 1) * (x : ℂ) ^ (-z - 1 - 1)‖ ≤ C := by
    intro x hx
    have hx' : 0 < x := hn'.trans_le hx.1
    have hre : (-z - 1 - 1).re = -z.re - 2 := by simp; ring
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx', hre, show -z - 1 = -(z + 1) by ring,
      norm_neg, hC]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hn' hx.1 (by linarith))
      (norm_nonneg _)
  have hint : IntervalIntegrable (fun x : ℝ ↦ (x : ℂ) ^ (-z - 1)) volume n (n + 1) :=
    ContinuousOn.intervalIntegrable fun x hx ↦ (hderiv x (by
      rwa [uIcc_of_le (by linarith)] at hx)).continuousAt.continuousWithinAt
  have hsub : (∫ x in (n : ℝ)..n + 1, (x : ℂ) ^ (-z - 1)) - (n : ℂ) ^ (-z - 1) =
      ∫ x in (n : ℝ)..n + 1, ((x : ℂ) ^ (-z - 1) - (n : ℂ) ^ (-z - 1)) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp
  have hbound : ∀ x ∈ Ι (n : ℝ) (n + 1), ‖(x : ℂ) ^ (-z - 1) - (n : ℂ) ^ (-z - 1)‖ ≤ C := by
    intro x hx
    rw [uIoc_of_le (by linarith)] at hx
    have hx' : x ∈ Icc (n : ℝ) (n + 1) := Ioc_subset_Icc_self hx
    have hC : 0 ≤ C := by positivity
    calc ‖(x : ℂ) ^ (-z - 1) - ((n : ℝ) : ℂ) ^ (-z - 1)‖ ≤ C * ‖x - n‖ :=
          Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
            (fun y hy ↦ (hderiv y hy).hasDerivWithinAt) hderiv_le (convex_Icc _ _)
            (left_mem_Icc.mpr (by linarith)) hx'
      _ ≤ C * 1 := by
          gcongr
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith [hx.1, hx.2]
      _ = C := mul_one C
  rw [stepCorrectionTerm_of_ne_zero a hn, norm_mul, hsub, mul_assoc]
  gcongr
  calc _ ≤ C * |(n + 1 : ℝ) - n| := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = C := by simp

/-- For coefficients bounded by `M` from `n = 1` on, the step correction terms are bounded by
`M ‖z + 1‖ n ^ (-re z - 2)` on `-2 ≤ re z`. -/
private theorem norm_stepCorrectionTerm_le_of_bound (hbound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M)
    (n : ℕ) (hz : -2 ≤ z.re) :
    ‖stepCorrectionTerm a n z‖ ≤ M * ‖z + 1‖ * (n : ℝ) ^ (-z.re - 2) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 1 le_rfl)
    simp only [stepCorrectionTerm_zero, Pi.zero_apply, norm_zero]
    positivity
  exact (norm_stepCorrectionTerm_le a n hz).trans
    (by gcongr; exact hbound n (Nat.one_le_iff_ne_zero.mpr hn))

/-- For coefficients bounded from `n = 1` on, the step correction converges absolutely on
`-1 < re z`. -/
theorem summable_norm_stepCorrectionTerm (hbound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M) (hz : -1 < z.re) :
    Summable fun n ↦ ‖stepCorrectionTerm a n z‖ :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_stepCorrectionTerm_le_of_bound hbound n (by linarith))
    ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _)

/-- For coefficients bounded from `n = 1` on, the series defining the step correction converges
(absolutely) to `stepCorrection a z` on `-1 < re z`. -/
theorem hasSum_stepCorrection (hbound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M) (hz : -1 < z.re) :
    HasSum (fun n ↦ stepCorrectionTerm a n z) (stepCorrection a z) :=
  (summable_norm_stepCorrectionTerm hbound hz).of_norm.hasSum

/-- **Holomorphy of the step correction.** For coefficients bounded from `n = 1` on, the step
correction is holomorphic on the half-plane `-1 < re z`: near `z₀`, the terms are bounded
uniformly by a multiple of the summable `n ^ (-1 - ε)` for `ε = (re z₀ + 1) / 2`. -/
theorem differentiableOn_stepCorrection (hbound : ∀ n, 1 ≤ n → ‖a n‖ ≤ M) :
    DifferentiableOn ℂ (stepCorrection a) {z | -1 < z.re} := by
  intro z₀ hz₀
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 1 le_rfl)
  set ε := (z₀.re + 1) / 2
  have hz₀' : z₀.re = 2 * ε - 1 := by
    simp only [ε]
    ring
  have hε : 0 < ε := by
    have : -1 < z₀.re := hz₀
    linarith
  have hball : DifferentiableOn ℂ (stepCorrection a) (ball z₀ ε) := by
    unfold stepCorrection
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ ↦ M * (‖z₀ + 1‖ + ε) * (n : ℝ) ^ (-1 - ε))
      ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _)
      (fun n ↦ (differentiable_stepCorrectionTerm a n).differentiableOn) isOpen_ball ?_
    intro n z hz
    rw [mem_ball_iff_norm] at hz
    -- on the ball, `ε - 1 < re z` and `‖z + 1‖ < ‖z₀ + 1‖ + ε`
    have hre : |z.re - z₀.re| < ε :=
      (Complex.abs_re_le_norm (z - z₀)).trans_lt (by simpa using hz)
    have hnorm : ‖z + 1‖ ≤ ‖z₀ + 1‖ + ε := by
      have := norm_add_le (z₀ + 1) (z - z₀)
      rw [show z₀ + 1 + (z - z₀) = z + 1 by ring] at this
      linarith
    have hzre : ε - 1 < z.re := by
      rw [abs_lt] at hre
      linarith [hre.1]
    refine (norm_stepCorrectionTerm_le_of_bound hbound n (by linarith)).trans ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow (by linarith : -z.re - 2 ≠ 0), Real.zero_rpow (by linarith : -1 - ε ≠ 0)]
    have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hnorm hM)
      (Real.rpow_le_rpow_of_exponent_le hn' (by linarith)) (by positivity) (by positivity)
  exact (hball.differentiableAt (ball_mem_nhds z₀ hε)).differentiableWithinAt

/-- At `z = 0`, the `n`-th term of the step correction is `a n (log (1 + 1 / n) - 1 / n)`; for
`n = 0` both sides vanish. -/
theorem stepCorrectionTerm_apply_zero (a : ℕ → ℂ) (n : ℕ) :
    stepCorrectionTerm a n 0 = a n * (Real.log (1 + 1 / n) - 1 / n : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [stepCorrectionTerm_of_ne_zero a hn, intervalIntegral_ofReal_cpow_neg_sub_one hn'
    (by positivity), show (-0 - 1 : ℂ) = -1 by ring, Complex.cpow_neg_one]
  simp only [neg_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
    Complex.real_smul, mul_one]
  rw [← Real.log_div (by positivity) hn'.ne', add_div, div_self hn'.ne']
  push_cast
  ring

/-- **The step correction at `0`:** `stepCorrection a 0 = ∑' n, a n (log (1 + 1 / n) - 1 / n)`. -/
theorem stepCorrection_zero (a : ℕ → ℂ) :
    stepCorrection a 0 = ∑' n : ℕ, a n * (Real.log (1 + 1 / n) - 1 / n : ℝ) :=
  tsum_congr (stepCorrectionTerm_apply_zero a)

end TauCeti.LSeries
