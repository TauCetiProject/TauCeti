/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import TauCeti.Analysis.LaplaceTransform.Truncated
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Complex.HalfPlaneIdentity
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.Exp.Complex

/-!
# The step correction of a bounded Dirichlet series

For coefficients `a : ℕ → ℂ`, the step function `t ↦ a ⌊exp t⌋₊` has, at least formally,
Laplace transform `∑ n ≥ 1, a n ∫ x in n..n+1, x ^ (-z - 1)`. Comparing each integral with the
value `n ^ (-z - 1)` at the left endpoint, this differs from the shifted Dirichlet series
`∑ n ≥ 1, a n n ^ (-z - 1)` by the *step correction*
`H z = ∑ n ≥ 1, a n (∫ x in n..n+1, x ^ (-z - 1) - n ^ (-z - 1))`.

When `a` is bounded, the Dirichlet series is only guaranteed to converge absolutely for
`re z > 0`, whereas the step correction is guaranteed to be holomorphic on the larger half-plane
`-1 < re z`: by the mean value theorem its `n`-th term is at most
`‖a n‖ ‖z + 1‖ n ^ (-re z - 2)`. This is what lets the bounded-Laplace (Newman) Tauberian theorem
for the step function transfer to ordered partial sums `∑ n ≤ N, a n / n` of the Dirichlet series
at `s = 1`, where the step correction takes the absolutely convergent value
`∑ n ≥ 1, a n (log (1 + 1 / n) - 1 / n)`. For the constant sequence `a = 1`, the step correction
equals `-riemannZeta₀ (z + 1)` throughout `-1 < re z` (in particular `-γ` at `z = 0`).

## Main declarations

* `TauCeti.LSeries.stepCorrectionTerm a n z`: the `n`-th term of the step correction, zero for
  `n = 0`;
* `TauCeti.LSeries.stepCorrection a z`: the step correction `H z`;
* `TauCeti.LSeries.norm_stepCorrectionTerm_le`: the mean value bound on the terms;
* `TauCeti.LSeries.hasSum_stepCorrection`: absolute convergence for `-1 < re z`;
* `TauCeti.LSeries.differentiableOn_stepCorrection`: holomorphy on `-1 < re z`;
* `TauCeti.LSeries.stepCorrection_zero`: the value `∑ a n (log (1 + 1 / n) - 1 / n)` at `0`;
* `TauCeti.LSeries.stepCorrection_one_eq_neg_riemannZeta₀`,
  `TauCeti.LSeries.stepCorrection_one_zero`, and
  `TauCeti.LSeries.riemannZeta_eq_inv_sub_stepCorrection_one`: the step correction of constant `1`.

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

/-- The step correction is the sum of its terms (unconditionally, as a `tsum`). -/
theorem stepCorrection_def (a : ℕ → ℂ) (z : ℂ) :
    stepCorrection a z = ∑' n, stepCorrectionTerm a n z :=
  (rfl)

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
      (a := Real.log n) (b := Real.log (n + 1))
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
    -- rewrite the factor as a negation so that `norm_neg` turns its norm into `‖z + 1‖`
    have hneg : -z - 1 = -(z + 1) := by ring
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx', hre, hneg, norm_neg, hC]
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
      have hsplit : z₀ + 1 + (z - z₀) = z + 1 := by ring
      have := norm_add_le (z₀ + 1) (z - z₀)
      rw [hsplit] at this
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
  -- the exponent `-z - 1` at `z = 0`, normalised so that `Complex.cpow_neg_one` applies
  have hexp : (-0 - 1 : ℂ) = -1 := by ring
  rw [stepCorrectionTerm_of_ne_zero a hn, intervalIntegral_ofReal_cpow_neg_sub_one hn'
    (by positivity), hexp, Complex.cpow_neg_one]
  simp only [neg_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
    Complex.real_smul, mul_one]
  rw [← Real.log_div (by positivity) hn'.ne', add_div, div_self hn'.ne']
  push_cast
  ring

/-- **The step correction at `0`:** `stepCorrection a 0 = ∑' n, a n (log (1 + 1 / n) - 1 / n)`. -/
theorem stepCorrection_zero (a : ℕ → ℂ) :
    stepCorrection a 0 = ∑' n : ℕ, a n * (Real.log (1 + 1 / n) - 1 / n : ℝ) :=
  tsum_congr (stepCorrectionTerm_apply_zero a)

/-- **The step correction of constant coefficients `1`.** On `-1 < re z`,
`stepCorrection 1 z = -riemannZeta₀ (z + 1)`, where `riemannZeta₀` is the entire completion of
`ζ(s) - (s - 1)⁻¹`. -/
theorem stepCorrection_one_eq_neg_riemannZeta₀ {z : ℂ} (hz : -1 < z.re) :
    stepCorrection 1 z = -riemannZeta₀ (z + 1) := by
  have hbound : ∀ n : ℕ, 1 ≤ n → ‖(1 : ℕ → ℂ) n‖ ≤ 1 := fun _ _ ↦ by simp
  refine (differentiableOn_stepCorrection hbound).eqOn_of_eqOn_re_gt
    ((differentiable_riemannZeta₀.comp (differentiable_id.add_const 1)).neg.differentiableOn)
    (b := 0) (fun w (hw : 0 < w.re) ↦ ?_) hz
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
  have hw1 : w + 1 ≠ 1 := fun h ↦ hw0 (by linear_combination h)
  have hS : Summable fun k : ℕ ↦ 1 / ((k : ℂ) + 1) ^ (w + 1) :=
    ((summable_nat_add_iff 1).mpr
      (Complex.summable_one_div_nat_cpow (p := w + 1) |>.mpr (by simpa using hw))).congr
      fun k ↦ by simp
  have htel : Tendsto (fun N : ℕ ↦ (((N : ℂ) + 1) ^ (-w) - 1) / (-w)) atTop (𝓝 w⁻¹) := by
    have hpow : Tendsto (fun N : ℕ ↦ ((N : ℂ) + 1) ^ (-w)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (Complex.tendsto_natCast_cpow_neg_atTop hw).comp (tendsto_add_atTop_nat 1)
    simpa [div_eq_mul_inv] using (hpow.sub_const 1).div_const (-w)
  have hrhs : Tendsto (fun N : ℕ ↦ (((N : ℂ) + 1) ^ (-w) - 1) / (-w) -
      ∑ k ∈ Finset.range N, 1 / ((k : ℂ) + 1) ^ (w + 1)) atTop
        (𝓝 (-riemannZeta₀ (w + 1))) := by
    have h := htel.sub hS.hasSum.tendsto_sum_nat
    rw [← zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hw),
      riemannZeta_eq_inv_sub_add hw1, add_sub_cancel_right] at h
    simpa [sub_add_eq_sub_sub] using h
  refine tendsto_nhds_unique (((hasSum_stepCorrection hbound (by linarith)).tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)) (hrhs.congr fun N ↦ ?_)
  have hsum_int : ∑ k ∈ Finset.range N, (((k + 1 : ℕ) + 1 : ℂ) ^ (-w) / (-w) -
      ((k + 1 : ℕ) : ℂ) ^ (-w) / (-w)) = (((N : ℂ) + 1) ^ (-w) - 1) / (-w) := by
    simpa [sub_div] using Finset.sum_range_sub (fun k : ℕ ↦ ((k + 1 : ℕ) : ℂ) ^ (-w) / (-w)) N
  rw [Function.comp_apply, Finset.sum_range_succ', stepCorrectionTerm_zero, Pi.zero_apply, add_zero,
    ← hsum_int, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hnot0 : (0 : ℝ) ∉ [[((k + 1 : ℕ) : ℝ), (k + 1 : ℕ) + 1]] := by
    rw [uIcc_of_le (by linarith)]
    intro h0
    have hk_pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    linarith [h0.1]
  have hint := integral_cpow (a := ((k + 1 : ℕ) : ℝ)) (b := (k + 1 : ℕ) + 1) (r := -w - 1)
    (Or.inr ⟨fun h ↦ hw0 (by linear_combination -h), hnot0⟩)
  have hterm : ((k + 1 : ℕ) : ℂ) ^ (-w - 1) = 1 / ((k : ℂ) + 1) ^ (w + 1) := by
    have hexp2 : -w - 1 = -(w + 1) := by ring
    rw [hexp2, Complex.cpow_neg, one_div, Nat.cast_add, Nat.cast_one]
  rw [stepCorrectionTerm_of_ne_zero 1 k.succ_ne_zero, Pi.one_apply, one_mul, hint, hterm]
  have hexp1 : -w - 1 + 1 = -w := by ring
  rw [hexp1, sub_div]
  push_cast
  rfl

/-- At `z = 0`, the step correction `∑' n, (log (1 + 1 / n) - 1 / n)` equals `-γ`. -/
theorem stepCorrection_one_zero :
    stepCorrection 1 0 = -(Real.eulerMascheroniConstant : ℂ) := by
  rw [stepCorrection_one_eq_neg_riemannZeta₀ (by norm_num), zero_add, riemannZeta₀_one]

/-- On `-1 < re z` away from `z = 0`, `riemannZeta (z + 1)` equals `z⁻¹ - stepCorrection 1 z`. -/
theorem riemannZeta_eq_inv_sub_stepCorrection_one {z : ℂ} (hz : -1 < z.re) (hz₀ : z ≠ 0) :
    riemannZeta (z + 1) = z⁻¹ - stepCorrection 1 z := by
  have hz1 : z + 1 ≠ 1 := fun h ↦ hz₀ (by simpa using h)
  rw [riemannZeta_eq_inv_sub_add hz1, stepCorrection_one_eq_neg_riemannZeta₀ hz,
     add_sub_cancel_right, sub_neg_eq_add]

end TauCeti.LSeries
