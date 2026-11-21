/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Positive divided differences of the real exponential

The divided difference of the exponential is the integral of the exponential along the segment
between its arguments. In particular it is strictly positive, including when the arguments
coincide. It is jointly real analytic, including on the diagonal. These divided differences
are the scalar coefficients in the derivative of the matrix exponential at a Hermitian matrix.

At base point `0`, `dslope exp 0` is the entire extension of `(exp u - 1) / u` across `u = 0`,
with Taylor series `∑' n, u ^ n / (n + 1)!`. Integrating termwise from `0` to `y` identifies
`∫ u in 0..y, (exp u - 1) / u` with the entire-part series
`∑' n, y ^ (n + 1) / ((n + 1) * (n + 1)!)` of the exponential integral, which is therefore
continuously differentiable and strictly increasing on all of `ℝ`, with explicit partial-sum lower
bounds and geometric-tail upper bounds for `y ≥ 0`.
-/

public section

open Filter MeasureTheory Set
open scoped ContDiff Nat

namespace Real

/-- The divided difference of the exponential is its average along a segment. -/
theorem dslope_exp_eq_integral (a b : ℝ) :
    dslope exp a b = ∫ t in (0 : ℝ)..1, exp ((1 - t) * a + t * b) := by
  have heq (t : ℝ) : (1 - t) * a + t * b = a + t * (b - a) := by ring
  simp_rw [heq]
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (by fun_prop : ContinuousOn (fun t : ℝ ↦ exp (a + t * (b - a))) (Set.Icc 0 1))
    (fun t _ ↦ hasDerivAt_exp (a + t * (b - a)))
  simp only [smul_eq_mul, add_sub_cancel] at h
  by_cases hab : b = a
  · simp [hab]
  · rw [dslope_of_ne exp hab, slope_def_field, div_eq_iff (sub_ne_zero.mpr hab)]
    simpa only [mul_comm] using h.symm

/-- All divided differences of the real exponential are strictly positive. -/
theorem dslope_exp_pos (a b : ℝ) : 0 < dslope exp a b := by
  rw [dslope_exp_eq_integral]
  exact intervalIntegral.integral_pos (by norm_num) (by fun_prop)
    (fun t _ ↦ (exp_pos _).le) ⟨0, by simp, exp_pos _⟩

/-- Translating the real exponential divided difference to zero extracts the factor `exp a`. -/
theorem dslope_exp_eq_exp_mul_dslope_zero (a b : ℝ) :
    dslope exp a b = exp a * dslope exp 0 (b - a) := by
  rw [dslope_exp_eq_integral a b, dslope_exp_eq_integral 0 (b - a),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← exp_add]
  congr 1
  ring

/-- The real exponential divided difference is jointly smooth, including its removable
value at equal arguments. The regularity parameter also permits real analyticity. -/
theorem contDiff_dslope_exp (m : ℕ∞ω) :
    ContDiff ℝ m (fun p : ℝ × ℝ ↦ dslope exp p.1 p.2) := by
  have hz : ContDiff ℝ m (dslope exp 0) :=
    ((analyticOnNhd_rexp (u := Set.univ)).dslope 0).contDiff
  have h : ContDiff ℝ m (fun p : ℝ × ℝ ↦ exp p.1 * dslope exp 0 (p.2 - p.1)) :=
    (contDiff_fst.exp).mul (hz.comp (contDiff_snd.sub contDiff_fst))
  convert h using 1
  funext p
  exact dslope_exp_eq_exp_mul_dslope_zero p.1 p.2

/-- Away from `0`, `dslope exp 0 u = (exp u - 1) / u`. -/
theorem dslope_exp_zero_of_ne {u : ℝ} (hu : u ≠ 0) :
    dslope exp 0 u = (exp u - 1) / u := by
  rw [dslope_of_ne exp hu, slope_def_field, exp_zero, sub_zero]

/-- `dslope exp 0` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_dslope_exp_zero : Continuous (dslope exp 0) :=
  (contDiff_dslope_exp 0).continuous.comp (continuous_const.prodMk continuous_id)

/-- Power series for `dslope exp 0`: `∑' n, u ^ n / (n + 1)! = dslope exp 0 u` for all `u : ℝ`. -/
theorem hasSum_dslope_exp_zero (u : ℝ) :
    HasSum (fun n : ℕ ↦ u ^ n / ((n + 1)! : ℝ)) (dslope exp 0 u) := by
  by_cases hu : u = 0
  · subst hu
    rw [dslope_same, deriv_exp, exp_zero]
    simpa using hasSum_single (0 : ℕ) (f := fun n : ℕ ↦ (0 : ℝ) ^ n / ((n + 1)! : ℝ))
      (fun n hn ↦ by simp [zero_pow hn])
  · have hsumm : Summable fun n : ℕ ↦ u ^ n / ((n + 1)! : ℝ) := by
      refine .of_norm_bounded (summable_pow_div_factorial |u|) fun n ↦ ?_
      rw [norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < ((n + 1)! : ℝ))]
      refine div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg u) _) (by positivity) ?_
      exact_mod_cast Nat.factorial_le (Nat.le_succ n)
    have hexp : HasSum (fun n : ℕ ↦ u ^ n / (n ! : ℝ)) (exp u) := by
      simpa [exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div] using
        (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) u)
    have hshift : HasSum (fun n : ℕ ↦ u ^ (n + 1) / ((n + 1)! : ℝ)) (exp u - 1) := by
      simpa [Finset.sum_range_one] using (hasSum_nat_add_iff' 1).mpr hexp
    have heq : u * (∑' n : ℕ, u ^ n / ((n + 1)! : ℝ)) = exp u - 1 := by
      refine (hsumm.hasSum.mul_left u).unique ?_
      convert hshift using 1
      ext n
      rw [pow_succ']
      ring
    rw [dslope_exp_zero_of_ne hu, ← eq_div_of_mul_eq hu (mul_comm _ u ▸ heq)]
    exact hsumm.hasSum

/-- `tsum` form of `Real.hasSum_dslope_exp_zero`. -/
theorem dslope_exp_zero_eq_tsum (u : ℝ) :
    dslope exp 0 u = ∑' n : ℕ, u ^ n / ((n + 1)! : ℝ) :=
  (hasSum_dslope_exp_zero u).tsum_eq.symm

/-- The series `∑_{n ≥ 1} y^n / (n * n!)` converges absolutely for every real `y`. -/
theorem summable_pow_div_mul_factorial (y : ℝ) :
    Summable fun n : ℕ ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hdom : Summable fun n : ℕ ↦ |y| ^ (n + 1) / ((n + 1)! : ℝ) :=
    (summable_nat_add_iff 1).mpr (summable_pow_div_factorial |y|)
  refine .of_norm_bounded hdom fun n ↦ ?_
  rw [norm_eq_abs, abs_div, abs_pow, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)),
    abs_of_pos (by positivity : (0 : ℝ) < ((n + 1)! : ℝ))]
  refine div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg y) _) (by positivity) ?_
  exact le_mul_of_one_le_left (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-- Termwise integration of `dslope exp 0` on `[0, y]` yields
`∑' n, y ^ (n + 1) / ((n + 1) * (n + 1)!)`. -/
theorem integral_dslope_exp_zero_eq_tsum (y : ℝ) :
    (∫ u in (0 : ℝ)..y, dslope exp 0 u) =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hsum : HasSum (fun n : ℕ ↦ ∫ u in (0 : ℝ)..y, u ^ n / ((n + 1)! : ℝ))
      (∫ u in (0 : ℝ)..y, dslope exp 0 u) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ ↦ |y| ^ n / (n ! : ℝ))
      (fun n ↦ (by fun_prop : Continuous fun u : ℝ ↦ u ^ n / ((n + 1)! : ℝ)).aestronglyMeasurable)
      (fun n ↦ Eventually.of_forall fun u hu ↦ ?_)
      (Eventually.of_forall fun _ _ ↦ summable_pow_div_factorial |y|)
      intervalIntegrable_const
      (Eventually.of_forall fun u _ ↦ hasSum_dslope_exp_zero u)
    have habs : |u| ≤ |y| := by
      have hmem := uIoc_subset_uIcc hu
      rcases le_total 0 y with hy | hy
      · rw [uIcc_of_le hy] at hmem
        rw [abs_of_nonneg hmem.1, abs_of_nonneg hy]
        exact hmem.2
      · rw [uIcc_of_ge hy] at hmem
        rw [abs_of_nonpos hmem.2, abs_of_nonpos hy]
        linarith [hmem.1]
    rw [norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < ((n + 1)! : ℝ))]
    refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg u) habs n) (by positivity) ?_
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  rw [← hsum.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  rw [intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero,
    div_div, mul_comm]

/-- The function `u ↦ (exp u - 1) / u` is interval integrable on every closed interval `[a, b]`
(including across `0`). -/
theorem intervalIntegrable_exp_sub_one_div (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ (exp u - 1) / u) volume a b := by
  refine (continuous_dslope_exp_zero.intervalIntegrable a b).congr_ae ?_
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with u hu
  exact dslope_exp_zero_of_ne hu

/-- The entire part `∑_{n ≥ 1} y^n / (n * n!)` of the exponential integral equals
`∫ u in 0..y, (exp u - 1) / u`. -/
theorem integral_exp_sub_one_div_eq_tsum (y : ℝ) :
    (∫ u in (0 : ℝ)..y, (exp u - 1) / u) =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  rw [← integral_dslope_exp_zero_eq_tsum]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with u hu _
  exact (dslope_exp_zero_of_ne hu).symm

/-- The entire-part series `y ↦ ∑_{n ≥ 1} y^n / (n * n!)` has derivative `dslope exp 0 y` at every
real `y`. -/
theorem hasDerivAt_tsum_pow_div_mul_factorial (y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∑' n : ℕ, t ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (dslope exp 0 y) y := by
  have heq : (fun t : ℝ ↦ ∑' n : ℕ, t ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) =
      fun t ↦ ∫ u in (0 : ℝ)..t, dslope exp 0 u :=
    funext fun t ↦ (integral_dslope_exp_zero_eq_tsum t).symm
  rw [heq]
  exact intervalIntegral.integral_hasDerivAt_right
    (continuous_dslope_exp_zero.intervalIntegrable 0 y)
    continuous_dslope_exp_zero.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_dslope_exp_zero.continuousAt

/-- The entire-part series `y ↦ ∑_{n ≥ 1} y^n / (n * n!)` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_tsum_pow_div_mul_factorial :
    Continuous fun y : ℝ ↦ ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  continuous_iff_continuousAt.mpr fun y ↦ (hasDerivAt_tsum_pow_div_mul_factorial y).continuousAt

/-- The entire-part series `y ↦ ∑_{n ≥ 1} y^n / (n * n!)` is strictly increasing on all of `ℝ`. -/
theorem strictMono_tsum_pow_div_mul_factorial :
    StrictMono fun y : ℝ ↦ ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  strictMono_of_deriv_pos fun y ↦ by
    rw [(hasDerivAt_tsum_pow_div_mul_factorial y).deriv]
    exact dslope_exp_pos 0 y

/-- Monotonicity of the entire-part series `∑_{n ≥ 1} y^n / (n * n!)` on `ℝ`. -/
theorem tsum_pow_div_mul_factorial_mono {x y : ℝ} (hxy : x ≤ y) :
    (∑' n : ℕ, x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  strictMono_tsum_pow_div_mul_factorial.monotone hxy

/-- Partial-sum lower bound for the entire-part series `∑_{n ≥ 1} y^n / (n * n!)` when `y ≥ 0`. -/
theorem sum_range_le_tsum_pow_div_mul_factorial {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (∑ n ∈ Finset.range N, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  (summable_pow_div_mul_factorial y).sum_le_tsum (Finset.range N) fun _ _ ↦ by positivity

/-- Geometric-tail upper bound for the entire-part series `∑_{n ≥ 1} y^n / (n * n!)` when
`0 ≤ y < N + 2`. -/
theorem tsum_pow_div_mul_factorial_le_sum_range_add {y : ℝ} (hy : 0 ≤ y) {N : ℕ}
    (hN : y < (N : ℝ) + 2) :
    (∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      (∑ n ∈ Finset.range N, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) +
        (y ^ (N + 1) / (((N : ℝ) + 1) * ((N + 1)! : ℝ))) / (1 - y / ((N : ℝ) + 2)) := by
  let a : ℕ → ℝ := fun n ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))
  let r : ℝ := y / ((N : ℝ) + 2)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := (div_lt_one (by positivity)).mpr hN
  have hsum := summable_pow_div_mul_factorial y
  rw [← hsum.sum_add_tsum_nat_add N]
  gcongr
  have hterm : ∀ k : ℕ, a (k + N) ≤ a N * r ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep : a (k + 1 + N) ≤ a (k + N) * r := by
          dsimp only [a, r]
          rw [add_right_comm k 1 N, pow_succ, Nat.factorial_succ, Nat.cast_mul]
          rw [← mul_div_mul_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          have hcast1 : ((k + N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + k + 2 := by push_cast; ring
          have hcast2 : ((k + N : ℕ) : ℝ) + 1 = (N : ℝ) + k + 1 := by push_cast; ring
          have hcast3 : ((k + N + 1 + 1 : ℕ) : ℝ) = (N : ℝ) + k + 2 := by push_cast; ring
          rw [hcast1, hcast2, hcast3]
          have hmul_le : ((N : ℝ) + k + 1) * ((N : ℝ) + 2) ≤
              ((N : ℝ) + k + 2) * ((N : ℝ) + k + 2) := by
            nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) N]
          have hyk : 0 ≤ y ^ (k + N + 1) * y * ((k + N + 1)! : ℝ) := by positivity
          nlinarith
        calc a (k + 1 + N)
            ≤ a (k + N) * r := hstep
          _ ≤ (a N * r ^ k) * r := mul_le_mul_of_nonneg_right ih hr0
          _ = a N * r ^ (k + 1) := by rw [pow_succ, mul_assoc]
  have hgeom : Summable fun k : ℕ ↦ a N * r ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left (a N)
  calc (∑' k : ℕ, a (k + N))
      ≤ ∑' k : ℕ, a N * r ^ k := ((summable_nat_add_iff N).mpr hsum).tsum_le_tsum hterm hgeom
    _ = a N / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

end Real
