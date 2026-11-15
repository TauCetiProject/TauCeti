/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Analytic.IteratedDeriv
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference

/-!
# Exponential-Bernoulli kernel and uniform Taylor remainder for Hurwitz continuation

The Mellin-Laplace integrand for the complex Hurwitz zeta function involves the generating kernel
`F_c(z) = z * exp (-c * z) / (1 - exp (-z))`, extended across `z = 0` by `F_c(0) = 1` via
`dslope Complex.exp 0 (-z)`. Because `1 - exp (-z)` vanishes only at integer multiples of
`2 * π * I`, `dslope Complex.exp 0 (-z)` has no zeros in the open disc `Metric.ball 0 (2 * π)`, so
`(c, z) ↦ hurwitzKernel c z` is jointly analytic on `Set.univ ×ˢ Metric.ball 0 (2 * π)`.

Multiplying by `exp z - 1` yields `hurwitzKernel c z * (exp z - 1) = z * exp ((1 - c) * z)`.
Differentiating `n + 1` times at `z = 0` produces the exact finite recurrence satisfied by
`Polynomial.bernoulli` at `1 - c`, identifying the Taylor coefficients at `0` as
`hurwitzBernoulliCoeff k c = (-1) ^ k * B_k(c) / k!`.

Integrating along the Cauchy circle `|ζ| = 2` expresses the order-`M` Taylor remainder on
`Metric.ball 0 2` as `z ^ (M + 1) * hurwitzTaylorQuot M c z`, where `hurwitzTaylorQuot M` is
jointly analytic on `Set.univ ×ˢ Metric.ball 0 2`. Compactness then gives Taylor remainder bounds
`‖∂_c^d (F_c(t) - ∑_{k ≤ M} b_k(c) t^k)‖ ≤ C * t ^ (M + 1)` on `[0, 1]`, locally uniformly in
`c`.

## Main definitions and results

* `TauCeti.hurwitzKernel`: the removable generating kernel `z * exp (-c * z) / (1 - exp (-z))`.
* `TauCeti.hurwitzBernoulliCoeff`: the Taylor coefficient `(-1) ^ k * B_k(c) / k!`.
* `TauCeti.iteratedDeriv_hurwitzKernel_zero`: identification of
  `iteratedDeriv n (hurwitzKernel c) 0` with `(-1) ^ n * B_n(c)`.
* `TauCeti.hurwitzTaylorQuot` and `TauCeti.hurwitzKernel_sub_sum_eq_pow_mul_hurwitzTaylorQuot`:
  jointly analytic Cauchy remainder quotient and exact Taylor decomposition on `Metric.ball 0 2`.
* `TauCeti.exists_norm_iteratedDeriv_hurwitzTaylorQuot_le`,
  `TauCeti.exists_norm_hurwitzTaylorQuot_le`,
  `TauCeti.exists_norm_iteratedDeriv_hurwitzKernel_sub_sum_le`, and
  `TauCeti.exists_norm_hurwitzKernel_sub_sum_le`: compact-uniform Taylor quotient and remainder
  estimates on `[0, 1]`.

## References

* J. C. Lagarias and W. C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  **24** (2012), 49–84, §9.
* F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, §§24.2, 25.11.
-/

public section

open Complex Set Filter Metric
open scoped Topology Real

namespace TauCeti

/-- The exponential-Bernoulli generating kernel `z * exp (-c * z) / (1 - exp (-z))`, extended
across `z = 0` by `hurwitzKernel c 0 = 1` via `dslope Complex.exp 0 (-z)`. -/
noncomputable def hurwitzKernel (c z : ℂ) : ℂ :=
  Complex.exp (-c * z) / dslope Complex.exp 0 (-z)

/-- Defining equation for `hurwitzKernel`. -/
theorem hurwitzKernel_def (c z : ℂ) :
    hurwitzKernel c z = Complex.exp (-c * z) / dslope Complex.exp 0 (-z) := (rfl)

@[simp]
theorem hurwitzKernel_zero_right (c : ℂ) : hurwitzKernel c 0 = 1 := by
  simp [hurwitzKernel]

/-- Away from `z = 0`, `hurwitzKernel c z` equals `z * exp (-c * z) / (1 - exp (-z))`. -/
theorem hurwitzKernel_of_ne_zero (c : ℂ) {z : ℂ} (hz : z ≠ 0) :
    hurwitzKernel c z = z * Complex.exp (-c * z) / (1 - Complex.exp (-z)) := by
  have hmul : z * dslope Complex.exp 0 (-z) = 1 - Complex.exp (-z) := by
    have h := sub_smul_dslope Complex.exp 0 (-z)
    rw [sub_zero, smul_eq_mul, Complex.exp_zero] at h
    linear_combination -h
  rw [hurwitzKernel, ← hmul, mul_div_mul_left _ _ hz]

/-- On `Metric.ball 0 (2 * π)`, `hurwitzKernel c z * (exp z - 1) = z * exp ((1 - c) * z)`. -/
theorem hurwitzKernel_mul_exp_sub_one (c : ℂ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (2 * π)) :
    hurwitzKernel c z * (Complex.exp z - 1) = z * Complex.exp ((1 - c) * z) := by
  have hq : dslope Complex.exp 0 (-z) ≠ 0 := Complex.dslope_exp_ne_zero (by simpa using hz)
  have hmul : z * dslope Complex.exp 0 (-z) = 1 - Complex.exp (-z) := by
    have h := sub_smul_dslope Complex.exp 0 (-z)
    rw [sub_zero, smul_eq_mul, Complex.exp_zero] at h
    linear_combination -h
  have hexp : Complex.exp z - 1 = Complex.exp z * (1 - Complex.exp (-z)) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hadd : Complex.exp (-c * z) * Complex.exp z = Complex.exp ((1 - c) * z) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [hurwitzKernel, hexp, ← hmul, div_eq_mul_inv]
  calc Complex.exp (-c * z) * (dslope Complex.exp 0 (-z))⁻¹ *
          (Complex.exp z * (z * dslope Complex.exp 0 (-z)))
      = z * (Complex.exp (-c * z) * Complex.exp z) *
          (dslope Complex.exp 0 (-z) * (dslope Complex.exp 0 (-z))⁻¹) := by ring
    _ = z * Complex.exp ((1 - c) * z) := by rw [hadd, mul_inv_cancel₀ hq, mul_one]

/-- `(c, z) ↦ hurwitzKernel c z` is jointly analytic on `Set.univ ×ˢ Metric.ball 0 (2 * π)`. -/
theorem analyticOnNhd_hurwitzKernel :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzKernel p.1 p.2)
      (univ ×ˢ ball 0 (2 * π)) := fun p hp =>
  (((analyticAt_fst.neg).mul analyticAt_snd).cexp).div
    (AnalyticAt.comp (g := dslope Complex.exp 0) (f := fun p : ℂ × ℂ => -p.2)
      (((analyticOnNhd_cexp (u := univ)).dslope 0) (-p.2) trivial) analyticAt_snd.neg)
    (Complex.dslope_exp_ne_zero (by simpa using hp.2))

/-- For fixed `c : ℂ`, `hurwitzKernel c` is analytic on `Metric.ball 0 (2 * π)`. -/
theorem analyticOnNhd_hurwitzKernel_right (c : ℂ) :
    AnalyticOnNhd ℂ (hurwitzKernel c) (ball 0 (2 * π)) := fun z hz =>
  (analyticOnNhd_hurwitzKernel (c, z) ⟨trivial, hz⟩).comp (analyticAt_const.prod analyticAt_id)

/-- The `k`-th Taylor coefficient `(-1) ^ k * B_k(c) / k!` of `hurwitzKernel c` at `z = 0`. -/
noncomputable def hurwitzBernoulliCoeff (k : ℕ) (c : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * Polynomial.aeval c (Polynomial.bernoulli k) / k.factorial

/-- Defining equation for `hurwitzBernoulliCoeff`. -/
theorem hurwitzBernoulliCoeff_def (k : ℕ) (c : ℂ) :
    hurwitzBernoulliCoeff k c =
      (-1 : ℂ) ^ k * Polynomial.aeval c (Polynomial.bernoulli k) / k.factorial := (rfl)

/-- `hurwitzBernoulliCoeff k c` via `(Polynomial.bernoulli k).map (algebraMap ℚ ℂ)`. -/
theorem hurwitzBernoulliCoeff_eq_map_eval (k : ℕ) (c : ℂ) :
    hurwitzBernoulliCoeff k c =
      (-1 : ℂ) ^ k * ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval c /
        k.factorial := by
  rw [hurwitzBernoulliCoeff, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

/-- Each Bernoulli coefficient `c ↦ hurwitzBernoulliCoeff k c` is an entire polynomial in `c`. -/
theorem differentiable_hurwitzBernoulliCoeff (k : ℕ) :
    Differentiable ℂ (hurwitzBernoulliCoeff k) :=
  ((Polynomial.bernoulli k).differentiable_aeval.const_mul _).div_const _

@[simp]
theorem hurwitzBernoulliCoeff_zero (c : ℂ) : hurwitzBernoulliCoeff 0 c = 1 := by
  simp [hurwitzBernoulliCoeff]

/-- The linear Bernoulli Taylor coefficient is `hurwitzBernoulliCoeff 1 c = 1 / 2 - c`, pinning
the `B_1(c) = c - 1 / 2` sign convention. -/
@[simp]
theorem hurwitzBernoulliCoeff_one (c : ℂ) : hurwitzBernoulliCoeff 1 c = 1 / 2 - c := by
  rw [hurwitzBernoulliCoeff, Polynomial.bernoulli_one]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C, eq_ratCast]
  push_cast; ring

/-- The quadratic Bernoulli Taylor coefficient is `(c ^ 2 - c + 1 / 6) / 2`. -/
theorem hurwitzBernoulliCoeff_two (c : ℂ) :
    hurwitzBernoulliCoeff 2 c = (c ^ 2 - c + 1 / 6) / 2 := by
  have h := congrArg (Polynomial.aeval c) (Polynomial.sum_bernoulli 2)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    Polynomial.bernoulli_zero, Polynomial.bernoulli_one] at h
  simp only [Algebra.smul_def, map_add, map_sub, map_mul, AlgHom.commutes, eq_ratCast,
    Polynomial.aeval_monomial, Polynomial.aeval_X, Polynomial.aeval_C, map_one, zero_add] at h
  norm_num at h
  have hb2 : Polynomial.aeval c (Polynomial.bernoulli 2) = c ^ 2 - c + 1 / 6 := by
    linear_combination h / 3
  rw [hurwitzBernoulliCoeff, hb2]
  simp only [even_two, Even.neg_pow, one_pow, one_mul, Nat.factorial_two, Nat.cast_ofNat]

private theorem iteratedDeriv_hurwitzKernel_zero_eq_aeval_one_sub (m : ℕ) (c : ℂ) :
    iteratedDeriv m (hurwitzKernel c) 0 =
      Polynomial.aeval (1 - c) (Polynomial.bernoulli m) := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    have heq : (fun z => hurwitzKernel c z * (Complex.exp z - 1)) =ᶠ[𝓝 0]
        fun z => z * Complex.exp ((1 - c) * z) :=
      eventually_of_mem (ball_mem_nhds 0 Real.two_pi_pos)
        fun z hz => hurwitzKernel_mul_exp_sub_one c hz
    have hderiv := heq.iteratedDeriv_eq (m + 1)
    -- Evaluate the `(m + 1)`-st derivative of `z * exp ((1 - c) * z)` at `0` by Leibniz.
    have hrhs : iteratedDeriv (m + 1) (fun z : ℂ => z * Complex.exp ((1 - c) * z)) 0 =
        (m + 1 : ℂ) * (1 - c) ^ m := by
      rw [iteratedDeriv_fun_mul (by fun_prop) (by fun_prop)]
      simp [iteratedDeriv_fun_id_zero, iteratedDeriv_cexp_const_mul]
    -- Expand the LHS by Leibniz and compare with `Polynomial.sum_bernoulli m`.
    have hf : ContDiffAt ℂ (m + 1) (hurwitzKernel c) 0 :=
      (analyticOnNhd_hurwitzKernel_right c 0 (mem_ball_self Real.two_pi_pos)).contDiffAt
    have hg : ContDiffAt ℂ (m + 1) (fun z : ℂ => Complex.exp z - 1) 0 := by fun_prop
    rw [hrhs, iteratedDeriv_fun_mul hf hg, Finset.sum_range_succ] at hderiv
    have hterms : ∀ k ∈ Finset.range (m + 1),
        ((m + 1).choose k : ℂ) * iteratedDeriv k (hurwitzKernel c) 0 *
          iteratedDeriv (m + 1 - k) (fun z : ℂ => Complex.exp z - 1) 0 =
        ((m + 1).choose k : ℂ) * iteratedDeriv k (hurwitzKernel c) 0 := fun k hk => by
      have hne : m + 1 - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
      have hexp : iteratedDeriv (m + 1 - k) Complex.exp 0 = 1 := by
        rw [iteratedDeriv_eq_iterate, Complex.iter_deriv_exp, Complex.exp_zero]
      rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop), hexp, iteratedDeriv_const]
      simp [hne]
    have hlast : (m + 1).choose (m + 1) * iteratedDeriv (m + 1) (hurwitzKernel c) 0 *
        iteratedDeriv (m + 1 - (m + 1)) (fun z : ℂ => Complex.exp z - 1) 0 = 0 := by simp
    rw [hlast, add_zero, Finset.sum_congr rfl hterms, Finset.sum_range_succ] at hderiv
    have hbern := congrArg (Polynomial.aeval (1 - c)) (Polynomial.sum_bernoulli m)
    simp only [map_sum, Algebra.smul_def, map_mul, AlgHom.commutes, eq_ratCast,
      Rat.cast_natCast, Rat.cast_add, Rat.cast_one, Polynomial.aeval_monomial] at hbern
    rw [Finset.sum_range_succ] at hbern
    have hprev : ∑ k ∈ Finset.range m,
          ((m + 1).choose k : ℂ) * iteratedDeriv k (hurwitzKernel c) 0 =
        ∑ k ∈ Finset.range m,
          ((m + 1).choose k : ℂ) * Polynomial.aeval (1 - c) (Polynomial.bernoulli k) :=
      Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_range.mp hk)]
    have hm1 : ((m + 1).choose m : ℂ) = (m + 1 : ℂ) := by
      exact_mod_cast Nat.choose_succ_self_right m
    rw [hprev, hm1] at hderiv
    rw [hm1] at hbern
    apply mul_left_cancel₀ (by exact_mod_cast Nat.succ_ne_zero m : (m + 1 : ℂ) ≠ 0)
    linear_combination hderiv - hbern

/-- The `n`-th derivative of `hurwitzKernel c` at `0` is `(-1) ^ n * B_n(c)`. -/
theorem iteratedDeriv_hurwitzKernel_zero (n : ℕ) (c : ℂ) :
    iteratedDeriv n (hurwitzKernel c) 0 =
      (-1 : ℂ) ^ n * Polynomial.aeval c (Polynomial.bernoulli n) := by
  rw [iteratedDeriv_hurwitzKernel_zero_eq_aeval_one_sub]
  simpa [Polynomial.aeval_comp, Algebra.smul_def] using
    congrArg (Polynomial.aeval c) (Polynomial.bernoulli_comp_one_sub_X n)

/-- The Cauchy integral quotient of the order-`M` Taylor remainder of `hurwitzKernel c` on
`|ζ| = 2`: `(2 * π * I)⁻¹ * ∮ ζ in C(0, 2), hurwitzKernel c ζ / (ζ ^ (M + 1) * (ζ - z))`. -/
noncomputable def hurwitzTaylorQuot (M : ℕ) (c z : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ ζ in C(0, 2), hurwitzKernel c ζ / (ζ ^ (M + 1) * (ζ - z))

/-- Defining equation for `hurwitzTaylorQuot`. -/
theorem hurwitzTaylorQuot_def (M : ℕ) (c z : ℂ) :
    hurwitzTaylorQuot M c z =
      (2 * π * I)⁻¹ * ∮ ζ in C(0, 2), hurwitzKernel c ζ / (ζ ^ (M + 1) * (ζ - z)) := (rfl)

private theorem sphere_two_sub_ne_zero {ζ z : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 2)
    (hz : z ∈ ball (0 : ℂ) 2) : ζ - z ≠ 0 := fun h0 => by
  have h1 : ‖ζ‖ = 2 := mem_sphere_zero_iff_norm.mp hζ
  have h2 : ‖z‖ < 2 := mem_ball_zero_iff.mp hz
  rw [sub_eq_zero.mp h0] at h1
  linarith

private theorem closedBall_two_subset_ball_two_pi :
    closedBall (0 : ℂ) 2 ⊆ ball (0 : ℂ) (2 * π) := fun _ hζ => by
  rw [mem_ball_zero_iff]
  linarith [mem_closedBall_zero_iff.mp hζ, Real.two_le_pi]

private theorem continuousOn_hurwitzKernel_sphere (c : ℂ) :
    ContinuousOn (hurwitzKernel c) (sphere (0 : ℂ) 2) := fun ζ hζ =>
  (analyticOnNhd_hurwitzKernel_right c ζ
    (closedBall_two_subset_ball_two_pi (sphere_subset_closedBall hζ))).continuousAt
    |>.continuousWithinAt

/-- `(c, z) ↦ hurwitzTaylorQuot M c z` is jointly analytic on `Set.univ ×ˢ Metric.ball 0 2`. -/
theorem analyticOnNhd_hurwitzTaylorQuot (M : ℕ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzTaylorQuot M p.1 p.2) (univ ×ˢ ball 0 2) := by
  have hint : AnalyticOnNhd ℂ
      (fun q : (ℂ × ℂ) × ℂ => hurwitzKernel q.1.1 q.2 / (q.2 ^ (M + 1) * (q.2 - q.1.2)))
      ((univ ×ˢ ball 0 2) ×ˢ sphere (0 : ℂ) |(2 : ℝ)|) := fun q hq => by
    have hq2 : q.2 ∈ sphere (0 : ℂ) 2 := by simpa using hq.2
    have hball : q.2 ∈ ball (0 : ℂ) (2 * π) :=
      closedBall_two_subset_ball_two_pi (sphere_subset_closedBall hq2)
    have hnum : AnalyticAt ℂ (fun r : (ℂ × ℂ) × ℂ => hurwitzKernel r.1.1 r.2) q :=
      AnalyticAt.comp (g := fun p : ℂ × ℂ => hurwitzKernel p.1 p.2)
        (f := fun r : (ℂ × ℂ) × ℂ => (r.1.1, r.2))
        (analyticOnNhd_hurwitzKernel (q.1.1, q.2) ⟨trivial, hball⟩)
        ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
    have hden : AnalyticAt ℂ (fun r : (ℂ × ℂ) × ℂ => r.2 ^ (M + 1) * (r.2 - r.1.2)) q :=
      (analyticAt_snd.pow (M + 1)).mul (analyticAt_snd.sub (analyticAt_snd.comp analyticAt_fst))
    exact hnum.div hden (mul_ne_zero (pow_ne_zero _ (ne_of_mem_sphere hq2 two_ne_zero))
      (sphere_two_sub_ne_zero hq2 hq.1.2))
  exact (analyticOnNhd_circleIntegral hint).const_smul (c := (2 * π * I)⁻¹)

private theorem cauchy_coeff_hurwitzKernel (k : ℕ) (c z : ℂ) :
    (2 * π * I)⁻¹ * (∮ ζ in C(0, 2), z ^ k / ζ ^ (k + 1) * hurwitzKernel c ζ) =
      hurwitzBernoulliCoeff k c * z ^ k := by
  have hd : DifferentiableOn ℂ (hurwitzKernel c) (closedBall 0 (2 : NNReal)) :=
    (analyticOnNhd_hurwitzKernel_right c).differentiableOn.mono closedBall_two_subset_ball_two_pi
  have hfact := (hd.hasFPowerSeriesOnBall (R := 2) two_pos).factorial_smul z k
  rw [nsmul_eq_mul, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, iteratedDeriv_hurwitzKernel_zero] at hfact
  have hfk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hval : cauchyPowerSeries (hurwitzKernel c) 0 (2 : NNReal) k (fun _ => z) =
      hurwitzBernoulliCoeff k c * z ^ k := by
    apply mul_left_cancel₀ hfk
    rw [hfact, hurwitzBernoulliCoeff, smul_eq_mul]; field_simp
  have happly := cauchyPowerSeries_apply (hurwitzKernel c) 0 (2 : NNReal) k z
  rw [hval] at happly
  rw [happly]
  simp only [smul_eq_mul, sub_zero, NNReal.coe_ofNat]
  congr 1
  refine circleIntegral.integral_congr zero_le_two fun ζ _ => ?_
  rw [div_pow, pow_succ]; ring

/-- Exact order-`M` Taylor decomposition of `hurwitzKernel c z` on `Metric.ball 0 2`. -/
theorem hurwitzKernel_sub_sum_eq_pow_mul_hurwitzTaylorQuot (M : ℕ) (c : ℂ) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 2) :
    hurwitzKernel c z - ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c * z ^ k =
      z ^ (M + 1) * hurwitzTaylorQuot M c z := by
  have hd : DifferentiableOn ℂ (hurwitzKernel c) (closedBall 0 2) :=
    (analyticOnNhd_hurwitzKernel_right c).differentiableOn.mono closedBall_two_subset_ball_two_pi
  have hcauchy : hurwitzKernel c z =
      (2 * π * I)⁻¹ * ∮ ζ in C(0, 2), (ζ - z)⁻¹ * hurwitzKernel c ζ := by
    simpa only [smul_eq_mul] using ((hd.mono closure_ball_subset_closedBall).diffContOnCl
      |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (f := hurwitzKernel c) hz).symm
  have hint_k : ∀ k ∈ Finset.range (M + 1),
      CircleIntegrable (fun ζ => z ^ k / ζ ^ (k + 1) * hurwitzKernel c ζ) 0 2 := fun k _ =>
    ContinuousOn.circleIntegrable zero_le_two <|
      (continuousOn_const.div (continuousOn_id.pow (k + 1))
        fun _ hζ => pow_ne_zero _ (ne_of_mem_sphere hζ two_ne_zero)).mul
        (continuousOn_hurwitzKernel_sphere c)
  have hsum : (∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c * z ^ k) =
      (2 * π * I)⁻¹ * ∮ ζ in C(0, 2),
        (∑ k ∈ Finset.range (M + 1), z ^ k / ζ ^ (k + 1) * hurwitzKernel c ζ) := by
    rw [circleIntegral.integral_fun_sum hint_k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (cauchy_coeff_hurwitzKernel k c z).symm
  have hint1 : CircleIntegrable (fun ζ => (ζ - z)⁻¹ * hurwitzKernel c ζ) 0 2 :=
    ContinuousOn.circleIntegrable zero_le_two <|
      ((continuousOn_id.sub continuousOn_const).inv₀ fun _ hζ => sphere_two_sub_ne_zero hζ hz).mul
        (continuousOn_hurwitzKernel_sphere c)
  have hint2 : CircleIntegrable
      (fun ζ => ∑ k ∈ Finset.range (M + 1), z ^ k / ζ ^ (k + 1) * hurwitzKernel c ζ) 0 2 := by
    convert CircleIntegrable.sum (Finset.range (M + 1)) hint_k with ζ
    simp [Finset.sum_apply]
  rw [hcauchy, hsum, ← mul_sub, ← circleIntegral.integral_sub hint1 hint2, hurwitzTaylorQuot,
    mul_left_comm (z ^ (M + 1)), ← smul_eq_mul (a := z ^ (M + 1)), ← circleIntegral.integral_smul]
  congr 1
  refine circleIntegral.integral_congr zero_le_two fun ζ hζ => ?_
  have hζ0 : ζ ≠ 0 := ne_of_mem_sphere hζ two_ne_zero
  have hsub : ζ - z ≠ 0 := sphere_two_sub_ne_zero hζ hz
  have hgeom : ∀ K : ℕ, (ζ - z)⁻¹ - ∑ k ∈ Finset.range (K + 1), z ^ k / ζ ^ (k + 1) =
      z ^ (K + 1) / (ζ ^ (K + 1) * (ζ - z)) := fun K => by
    induction K with
    | zero => simp only [Finset.range_one, Finset.sum_singleton, pow_zero, zero_add, pow_one]
              field_simp; ring
    | succ K ih => rw [Finset.sum_range_succ, ← sub_sub, ih]; field_simp; ring
  rw [← Finset.sum_mul, ← sub_mul, hgeom M, smul_eq_mul]; ring

/-- Step relation between consecutive Taylor remainder quotients on `Metric.ball 0 2`. -/
theorem hurwitzTaylorQuot_eq_add_mul_succ (M : ℕ) (c : ℂ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 2) :
    hurwitzTaylorQuot M c z =
      hurwitzBernoulliCoeff (M + 1) c + z * hurwitzTaylorQuot (M + 1) c z := by
  have hint1 : CircleIntegrable (fun ζ => (1 : ℂ) / ζ ^ (M + 2) * hurwitzKernel c ζ) 0 2 :=
    ContinuousOn.circleIntegrable zero_le_two <|
      (continuousOn_const.div (continuousOn_id.pow (M + 2))
        fun _ hζ => pow_ne_zero _ (ne_of_mem_sphere hζ two_ne_zero)).mul
        (continuousOn_hurwitzKernel_sphere c)
  have hint2 : CircleIntegrable
      (fun ζ => z * (hurwitzKernel c ζ / (ζ ^ (M + 2) * (ζ - z)))) 0 2 :=
    ContinuousOn.circleIntegrable zero_le_two <|
      continuousOn_const.mul ((continuousOn_hurwitzKernel_sphere c).div
        ((continuousOn_id.pow (M + 2)).mul (continuousOn_id.sub continuousOn_const))
        fun _ hζ => mul_ne_zero (pow_ne_zero _ (ne_of_mem_sphere hζ two_ne_zero))
          (sphere_two_sub_ne_zero hζ hz))
  have h1 := cauchy_coeff_hurwitzKernel (M + 1) c 1
  simp only [one_pow, mul_one] at h1
  have hpull : z * ((2 * π * I)⁻¹ *
        ∮ ζ in C(0, 2), hurwitzKernel c ζ / (ζ ^ (M + 2) * (ζ - z))) =
      (2 * π * I)⁻¹ * ∮ ζ in C(0, 2), z * (hurwitzKernel c ζ / (ζ ^ (M + 2) * (ζ - z))) := by
    rw [mul_left_comm z, ← smul_eq_mul (a := z), ← circleIntegral.integral_smul]; rfl
  rw [hurwitzTaylorQuot, hurwitzTaylorQuot, ← h1, hpull, ← mul_add,
    ← circleIntegral.integral_add hint1 hint2]
  congr 1
  refine circleIntegral.integral_congr zero_le_two fun ζ hζ => ?_
  have hζ0 : ζ ≠ 0 := ne_of_mem_sphere hζ two_ne_zero
  have hsub : ζ - z ≠ 0 := sphere_two_sub_ne_zero hζ hz
  rw [pow_succ ζ (M + 1)]; field_simp; ring

/-- At `z = 0`, the order-`M` Taylor remainder quotient equals the next Taylor coefficient
`hurwitzBernoulliCoeff (M + 1) c`. -/
@[simp]
theorem hurwitzTaylorQuot_zero_right (M : ℕ) (c : ℂ) :
    hurwitzTaylorQuot M c 0 = hurwitzBernoulliCoeff (M + 1) c := by
  simpa using hurwitzTaylorQuot_eq_add_mul_succ M c (mem_ball_self two_pos)

/-- `(c, z) ↦ iteratedDeriv d (fun w => hurwitzTaylorQuot M w z) c` is jointly analytic on
`Set.univ ×ˢ Metric.ball 0 2`. -/
theorem analyticOnNhd_iteratedDeriv_hurwitzTaylorQuot (M d : ℕ) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => iteratedDeriv d (fun w => hurwitzTaylorQuot M w p.2) p.1)
      (univ ×ˢ ball 0 2) := fun p hp => by
  have hswap : AnalyticAt ℂ (fun q : ℂ × ℂ => hurwitzTaylorQuot M q.2 q.1) (p.2, p.1) :=
    AnalyticAt.comp (g := fun r : ℂ × ℂ => hurwitzTaylorQuot M r.1 r.2)
      (f := fun q : ℂ × ℂ => (q.2, q.1))
      (analyticOnNhd_hurwitzTaylorQuot M (p.1, p.2) hp) (analyticAt_snd.prod analyticAt_fst)
  exact AnalyticAt.comp
    (g := fun q : ℂ × ℂ => iteratedDeriv d (fun w => hurwitzTaylorQuot M w q.1) q.2)
    (f := fun r : ℂ × ℂ => (r.2, r.1))
    (hswap.iteratedDeriv_snd d) (analyticAt_snd.prod analyticAt_fst)

private theorem ofReal_mem_ball_two {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t : ℂ) ∈ ball (0 : ℂ) 2 := by
  rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1]; linarith [ht.2]

/-- Compact-uniform bound on `[0, 1]` for the `d`-th `c`-derivative of `hurwitzTaylorQuot M`. -/
theorem exists_norm_iteratedDeriv_hurwitzTaylorQuot_le {K : Set ℂ} (hK : IsCompact K)
    (M d : ℕ) :
    ∃ B ≥ 0, ∀ c ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv d (fun w => hurwitzTaylorQuot M w t) c‖ ≤ B := by
  let S : Set (ℂ × ℂ) := K ×ˢ (Complex.ofReal '' Icc (0 : ℝ) 1)
  have hS_comp : IsCompact S := hK.prod (isCompact_Icc.image continuous_ofReal)
  have hS_sub : S ⊆ univ ×ˢ ball 0 2 := by
    rintro ⟨_, _⟩ ⟨_, t, ht, rfl⟩; exact ⟨trivial, ofReal_mem_ball_two ht⟩
  obtain ⟨B, hB⟩ := hS_comp.exists_bound_of_continuousOn
    ((analyticOnNhd_iteratedDeriv_hurwitzTaylorQuot M d).continuousOn.mono hS_sub)
  exact ⟨max B 0, le_max_right _ _, fun c hc t ht =>
    (hB (c, t) ⟨hc, t, ht, rfl⟩).trans (le_max_left _ _)⟩

/-- Compact-uniform bound on `[0, 1]` for `hurwitzTaylorQuot M c t`. -/
theorem exists_norm_hurwitzTaylorQuot_le {K : Set ℂ} (hK : IsCompact K) (M : ℕ) :
    ∃ B ≥ 0, ∀ c ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ‖hurwitzTaylorQuot M c t‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_iteratedDeriv_hurwitzTaylorQuot_le hK M 0
  exact ⟨B, hB0, fun c hc t ht => by simpa using hB c hc t ht⟩

/-- Compact-uniform Taylor remainder estimate on `[0, 1]` after any fixed order `d` of
differentiation in the parameter `c`. -/
theorem exists_norm_iteratedDeriv_hurwitzKernel_sub_sum_le {K : Set ℂ} (hK : IsCompact K)
    (M d : ℕ) :
    ∃ C ≥ 0, ∀ c ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv d
          (fun w => hurwitzKernel w t -
            ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k w * (t : ℂ) ^ k) c‖ ≤
        C * t ^ (M + 1) := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_iteratedDeriv_hurwitzTaylorQuot_le hK M d
  refine ⟨B, hB0, fun c hc t ht => ?_⟩
  have hfun : (fun w => hurwitzKernel w t -
        ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k w * (t : ℂ) ^ k) =
      fun w => (t : ℂ) ^ (M + 1) * hurwitzTaylorQuot M w t :=
    funext fun w => hurwitzKernel_sub_sum_eq_pow_mul_hurwitzTaylorQuot M w (ofReal_mem_ball_two ht)
  rw [hfun, iteratedDeriv_const_mul_field, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg ht.1, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB c hc t ht) (pow_nonneg ht.1 _)

/-- Compact-uniform Taylor remainder estimate on `[0, 1]` for `hurwitzKernel c t`. -/
theorem exists_norm_hurwitzKernel_sub_sum_le {K : Set ℂ} (hK : IsCompact K) (M : ℕ) :
    ∃ C ≥ 0, ∀ c ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖hurwitzKernel c t -
          ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c * (t : ℂ) ^ k‖ ≤
        C * t ^ (M + 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedDeriv_hurwitzKernel_sub_sum_le hK M 0
  exact ⟨C, hC0, fun c hc t ht => by simpa using hC c hc t ht⟩

end TauCeti

end
