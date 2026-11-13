/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Tricomi's entire incomplete Gamma function

Tricomi's function `γ*(a, z) = e^{−z} 𝐌(1, a + 1, z)` (DLMF 8.5.2), where
`𝐌(1, b, z) = ∑ zⁿ / Γ(b + n)` is Mathlib's regularized Kummer function
`Complex.regularizedHGFun {1} {b}`, is the normalization of the lower incomplete Gamma function
that is entire in both the parameter `a` and the argument `z`: classically
`γ(a, z) = Γ(a) z^a γ*(a, z)`, and `γ*` absorbs both the branch of `z^a` and the poles of `Γ`.
It is the base from which the complex incomplete Gamma functions, the exponential integrals and
the error function (`erf z = z γ*(1/2, z²)`) are built.

## Main definitions

* `Complex.tricomiIncompleteGamma a z` — Tricomi's function `γ*(a, z)`.

## Main results

* `Complex.hasSum_tricomiIncompleteGamma` — the series
  `γ*(a, z) = e^{−z} ∑ zᵏ / Γ(a + k + 1)` (DLMF 8.7.1), for all `a` and `z`;
* `Complex.hasSum_tricomiIncompleteGamma_of_ne_neg_natCast` — the series
  `γ*(a, z) = Γ(a)⁻¹ ∑ (−z)ᵏ / (k! (a + k))` (DLMF 8.7.1), for `a ∉ −ℕ`;
* `Complex.tricomiIncompleteGamma_eq_integral` — the integral
  `γ*(a, z) = Γ(a)⁻¹ ∫₀¹ t^{a−1} e^{−zt} dt` (DLMF 8.2.7), for `0 < Re a`;
* `Complex.tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one` — the
  recurrence `γ*(a, z) = z γ*(a + 1, z) + e^{−z} / Γ(a + 1)` in the parameter (DLMF §8.8);
* `Complex.tricomiIncompleteGamma_zero_right`, `tricomiIncompleteGamma_neg_natCast`,
  `tricomiIncompleteGamma_zero_left`, `tricomiIncompleteGamma_one_left` — the special values
  `γ*(a, 0) = 1 / Γ(a + 1)` (DLMF 8.4.2), `γ*(−n, z) = zⁿ` (DLMF 8.4.12), `γ*(0, z) = 1` and
  `γ*(1, z) = (1 − e^{−z}) / z` for `z ≠ 0`;
* `Complex.hasDerivAt_tricomiIncompleteGamma` — `∂γ*(a, z)/∂z = −a γ*(a + 1, z)`, so that
  `γ*(a, ·)` is entire (`differentiable_tricomiIncompleteGamma`);
* `Complex.differentiable_tricomiIncompleteGamma_left` — `γ*(·, z)` is entire;
* `Complex.tricomiIncompleteGamma_ode` — the differential equation
  `z w'' + (a + 1 + z) w' + a w = 0` (DLMF 8.2.14).

## Implementation

Mathlib's convention `Γ(−n) = 0` makes `1 / Γ` entire, so the series 8.7.1 in its first form holds
for every `a` with no case split.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.2](https://dlmf.nist.gov/8.2),
  [§8.4](https://dlmf.nist.gov/8.4), [§8.5](https://dlmf.nist.gov/8.5),
  [§8.7](https://dlmf.nist.gov/8.7) and [§8.8](https://dlmf.nist.gov/8.8).
* F. G. Tricomi, *Sulla funzione gamma incompleta*, Ann. Mat. Pura Appl. (4) 31 (1950).
-/

public section

noncomputable section

open Complex Filter Finset Set MeasureTheory
open scoped Nat Topology Interval

namespace Complex

/-- Tricomi's entire incomplete Gamma function `γ*(a, z) = e^{−z} 𝐌(1, a + 1, z)` (DLMF 8.5.2),
written through Mathlib's regularized Kummer function `𝐌(1, b, z) = ∑ zⁿ / Γ(b + n)`. It is
entire in each of `a` and `z`; for `a ∉ −ℕ` and `z` off the cut, the lower incomplete Gamma
function is `γ(a, z) = Γ(a) z^a γ*(a, z)`. -/
def tricomiIncompleteGamma (a z : ℂ) : ℂ :=
  cexp (-z) * regularizedHGFun {1} {a + 1} z

/-- Unfolding `tricomiIncompleteGamma` to Mathlib's regularized Kummer function. -/
theorem tricomiIncompleteGamma_def (a z : ℂ) :
    tricomiIncompleteGamma a z = cexp (-z) * regularizedHGFun {1} {a + 1} z := (rfl)

/-- The power series of Tricomi's function (DLMF 8.7.1):
`γ*(a, z) = e^{−z} ∑ zᵏ / Γ(a + k + 1)`, for all `a` and `z`. -/
theorem hasSum_tricomiIncompleteGamma (a z : ℂ) :
    HasSum (fun k : ℕ => cexp (-z) * z ^ k / Gamma (a + k + 1)) (tricomiIncompleteGamma a z) := by
  rw [tricomiIncompleteGamma_def]
  refine ((hasSum_regularizedHGFun (a := {1}) (b := {a + 1}) (by simp) z).mul_left
    (cexp (-z))).congr_fun fun k => ?_
  rw [regularizedHGFunCoeff_one_singleton, add_right_comm, div_eq_mul_inv]
  ring

/-- The recurrence of Tricomi's function in its parameter (DLMF §8.8):
`γ*(a, z) = z γ*(a + 1, z) + e^{−z} / Γ(a + 1)`. -/
theorem tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one (a z : ℂ) :
    tricomiIncompleteGamma a z =
      z * tricomiIncompleteGamma (a + 1) z + cexp (-z) / Gamma (a + 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_tricomiIncompleteGamma a z)
  have h' := (hasSum_tricomiIncompleteGamma (a + 1) z).mul_left z
  simp only [range_one, sum_singleton, CharP.cast_eq_zero, add_zero, pow_zero, mul_one] at h
  rw [← sub_eq_iff_eq_add, h.unique (h'.congr_fun fun k => ?_)]
  push_cast
  ring_nf

/-- The value of Tricomi's function at `z = 0` (DLMF 8.4.2): `γ*(a, 0) = 1 / Γ(a + 1)`. This is
`0` at `a ∈ {−1, −2, …}`. -/
@[simp]
theorem tricomiIncompleteGamma_zero_right (a : ℂ) :
    tricomiIncompleteGamma a 0 = (Gamma (a + 1))⁻¹ := by
  simp [tricomiIncompleteGamma_def]

/-- At `a = 0`, Tricomi's function is identically `1`. -/
@[simp]
theorem tricomiIncompleteGamma_zero_left (z : ℂ) : tricomiIncompleteGamma 0 z = 1 := by
  have hexp : HasSum (fun k : ℕ => z ^ k / k !) (cexp z) :=
    Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp z
  refine (hasSum_tricomiIncompleteGamma 0 z).unique ?_
  have h := hexp.mul_left (cexp (-z))
  rw [← Complex.exp_add, neg_add_cancel, exp_zero] at h
  refine h.congr_fun fun k => ?_
  rw [zero_add, Gamma_nat_eq_factorial, mul_div_assoc]

/-- At a nonpositive integer parameter, Tricomi's function is a monomial (DLMF 8.4.12):
`γ*(−n, z) = zⁿ`. -/
@[simp]
theorem tricomiIncompleteGamma_neg_natCast (n : ℕ) (z : ℂ) :
    tricomiIncompleteGamma (-n) z = z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one]
    have h : -((n + 1 : ℕ) : ℂ) + 1 = -n := by push_cast; ring
    rw [h, ih, Gamma_neg_nat_eq_zero, div_zero, add_zero, pow_succ']

/-- At `a = 1`, Tricomi's function is `γ*(1, z) = (1 − e^{−z}) / z` for `z ≠ 0`; at `z = 0` it
is `γ*(1, 0) = 1` by `tricomiIncompleteGamma_zero_right`. -/
theorem tricomiIncompleteGamma_one_left {z : ℂ} (hz : z ≠ 0) :
    tricomiIncompleteGamma 1 z = (1 - cexp (-z)) / z := by
  have h := tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one 0 z
  rw [tricomiIncompleteGamma_zero_left, zero_add, Gamma_one, div_one] at h
  rw [eq_div_iff hz]
  linear_combination -h

/-! ### Differentiability in the argument -/

/-- The derivative of Tricomi's function in its argument:
`∂γ*(a, z)/∂z = −a γ*(a + 1, z)`. -/
theorem hasDerivAt_tricomiIncompleteGamma (a z : ℂ) :
    HasDerivAt (tricomiIncompleteGamma a) (-a * tricomiIncompleteGamma (a + 1) z) z := by
  have hcard : ({1} : Multiset ℂ).card ≤ ({a + 1} : Multiset ℂ).card := by simp
  -- the derivative of `𝐌(1, a + 1, ·)` is `𝐌(1, a + 1, ·) − a 𝐌(1, a + 2, ·)`, termwise
  have hM : deriv (regularizedHGFun {1} {a + 1}) z =
      regularizedHGFun {1} {a + 1} z - a * regularizedHGFun {1} {a + 1 + 1} z := by
    refine (hasSum_deriv_regularizedHGFun hcard z).unique ?_
    refine ((hasSum_regularizedHGFun hcard z).sub
      ((hasSum_regularizedHGFun (b := {a + 1 + 1}) (by simp) z).mul_left a)).congr_fun fun k => ?_
    simp only [regularizedHGFunCoeff_one_singleton]
    rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a + 1 + k)]
    push_cast
    ring_nf
  have hd := ((analyticAt_regularizedHGFun_of_card_le hcard z).differentiableAt.hasDerivAt)
  rw [hM] at hd
  convert ((hasDerivAt_neg z).cexp).mul hd using 1
  · exact funext (tricomiIncompleteGamma_def a)
  · rw [tricomiIncompleteGamma_def]
    ring

/-- The derivative of Tricomi's function in its argument, as a function:
`∂γ*(a, ·)/∂z = −a γ*(a + 1, ·)`. -/
@[simp]
theorem deriv_tricomiIncompleteGamma (a : ℂ) :
    deriv (tricomiIncompleteGamma a) = fun z => -a * tricomiIncompleteGamma (a + 1) z :=
  funext fun z => (hasDerivAt_tricomiIncompleteGamma a z).deriv

/-- Tricomi's function is entire in its argument. -/
theorem differentiable_tricomiIncompleteGamma (a : ℂ) :
    Differentiable ℂ (tricomiIncompleteGamma a) :=
  fun z => (hasDerivAt_tricomiIncompleteGamma a z).differentiableAt

/-- The differential equation of Tricomi's function (DLMF 8.2.14):
`z w'' + (a + 1 + z) w' + a w = 0` for `w = γ*(a, ·)`. -/
theorem tricomiIncompleteGamma_ode (a z : ℂ) :
    z * deriv (deriv (tricomiIncompleteGamma a)) z +
      (a + 1 + z) * deriv (tricomiIncompleteGamma a) z + a * tricomiIncompleteGamma a z = 0 := by
  have h2 : deriv (deriv (tricomiIncompleteGamma a)) z =
      -a * (-(a + 1) * tricomiIncompleteGamma (a + 1 + 1) z) := by
    rw [deriv_tricomiIncompleteGamma]
    exact ((hasDerivAt_tricomiIncompleteGamma (a + 1) z).const_mul (-a)).deriv
  have h₀ := tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one a z
  have h₁ := tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one (a + 1) z
  have hΓ := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a + 1)
  rw [h2, deriv_tricomiIncompleteGamma]
  simp only [div_eq_mul_inv] at h₀ h₁
  linear_combination a * h₀ - a * (a + 1) * h₁ + a * cexp (-z) * hΓ

/-! ### Entirety in the parameter -/

/- Entirety in `a` is proved first on the half-plane `0 < Re a`, by the Weierstrass M-test with
the bound `Complex.norm_inv_Gamma_add_natCast_le`, and then carried to the whole plane by the
recurrence in `a`, as Mathlib does for `Complex.differentiable_one_div_Gamma`. -/

/-- Tricomi's function is holomorphic in its parameter on the half-plane `0 < Re a`. -/
private theorem differentiableAt_tricomiIncompleteGamma_left_of_re_pos (z : ℂ) {a₀ : ℂ}
    (ha₀ : 0 < a₀.re) : DifferentiableAt ℂ (fun a => tricomiIncompleteGamma a z) a₀ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall a₀ a₀.re).exists_bound_of_continuousOn
    (differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)).continuous.continuousOn
  have hre : ∀ a ∈ Metric.ball a₀ a₀.re, 0 < a.re := fun a ha => by
    have := (abs_re_le_norm (a - a₀)).trans_lt (by rwa [← dist_eq_norm])
    rw [sub_re, abs_lt] at this
    linarith
  have hsum : Summable fun k : ℕ => C * ‖z‖ ^ k / k ! := by
    simpa [mul_div_assoc] using (Real.summable_pow_div_factorial ‖z‖).mul_left C
  have hM := differentiableOn_tsum_of_summable_norm hsum
    (F := fun (k : ℕ) a => (Gamma (a + 1 + k))⁻¹ * z ^ k) (U := Metric.ball a₀ a₀.re)
    (fun k => ((differentiable_one_div_Gamma.comp
      ((differentiable_id.add_const 1).add_const _)).mul_const _).differentiableOn)
    Metric.isOpen_ball (fun k a ha => ?_)
  · have heq : (fun a => tricomiIncompleteGamma a z) =
        fun a => cexp (-z) * ∑' k : ℕ, (Gamma (a + 1 + k))⁻¹ * z ^ k := by
      ext a
      rw [tricomiIncompleteGamma_def,
        ← (hasSum_regularizedHGFun (b := {a + 1}) (by simp) z).tsum_eq]
      simp
    rw [heq]
    exact ((hM _ (Metric.mem_ball_self ha₀)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self ha₀))).const_mul _
  · have h1 : 1 ≤ (a + 1).re := by rw [add_re, one_re]; linarith [hre a ha]
    have hCa : ‖(Gamma (a + 1))⁻¹‖ ≤ C := hC a (Metric.ball_subset_closedBall ha)
    rw [norm_mul, norm_pow, mul_comm, mul_div_assoc, ← mul_div_assoc]
    calc ‖z‖ ^ k * ‖(Gamma (a + 1 + k))⁻¹‖ ≤ ‖z‖ ^ k * (‖(Gamma (a + 1))⁻¹‖ / k !) := by
          gcongr
          exact Complex.norm_inv_Gamma_add_natCast_le h1 k
      _ ≤ ‖z‖ ^ k * (C / k !) := by gcongr
      _ = C * ‖z‖ ^ k / k ! := by ring

/-- Tricomi's function is entire in its parameter. -/
theorem differentiable_tricomiIncompleteGamma_left (z : ℂ) :
    Differentiable ℂ fun a => tricomiIncompleteGamma a z := by
  intro a
  obtain ⟨n, hn⟩ := exists_nat_gt (-a.re)
  induction n generalizing a with
  | zero => exact differentiableAt_tricomiIncompleteGamma_left_of_re_pos z (by simpa using hn)
  | succ n ih =>
    have hrec : (fun a => tricomiIncompleteGamma a z) =
        fun a => z * tricomiIncompleteGamma (a + 1) z + cexp (-z) * (Gamma (a + 1))⁻¹ :=
      funext fun a => by
        rw [tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one, div_eq_mul_inv]
    have h := ih (a + 1) (by rw [add_re, one_re]; push_cast at hn; linarith)
    rw [hrec]
    exact ((h.comp a (differentiableAt_id.add_const 1)).const_mul z).add
      ((differentiable_one_div_Gamma.comp (differentiable_id.add_const 1) a).const_mul _)

/-! ### The series in powers of `−z` and the integral -/

/- The second form of 8.7.1 is the Cauchy product of the first with the exponential series, and
the integral 8.2.7 follows from it by termwise integration. -/

/-- The power series of Tricomi's function in `−z` (DLMF 8.7.1): for `a ∉ −ℕ`,
`γ*(a, z) = Γ(a)⁻¹ ∑ (−z)ᵏ / (k! (a + k))`. -/
theorem hasSum_tricomiIncompleteGamma_of_ne_neg_natCast {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n)
    (z : ℂ) :
    HasSum (fun k : ℕ => (Gamma a)⁻¹ * ((-z) ^ k / (k ! * (a + k))))
      (tricomiIncompleteGamma a z) := by
  have hexp : HasSum (fun k : ℕ => (-z) ^ k / k !) (cexp (-z)) :=
    Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp (-z)
  have hM := hasSum_regularizedHGFun (a := {1}) (b := {a + 1}) (by simp) z
  have hnorm := summable_norm_regularizedHGFun (a := {1}) (b := {a + 1}) (by simp) z
  have h := hasSum_sum_range_mul_of_summable_norm (NormedSpace.norm_expSeries_div_summable (-z))
    hnorm
  rw [hexp.tsum_eq, hM.tsum_eq, ← tricomiIncompleteGamma_def] at h
  refine h.congr_fun fun m => ?_
  have hterm : ∀ i ∈ range (m + 1), (-z) ^ i / i ! *
      (regularizedHGFunCoeff {1} {a + 1} (m - i) * z ^ (m - i)) =
        z ^ m * ((-1 : ℂ) ^ i / (i ! * Gamma (a + (m - i : ℕ) + 1))) := fun i hi => by
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rw [regularizedHGFunCoeff_one_singleton, neg_pow, ← pow_mul_pow_sub z hi', add_right_comm]
    ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_range_neg_one_pow_div_factorial_mul_Gamma ha, neg_pow]
  ring

/-- Tricomi's integral (DLMF 8.2.7): for `0 < Re a`,
`γ*(a, z) = Γ(a)⁻¹ ∫₀¹ t^{a−1} e^{−zt} dt`. -/
theorem tricomiIncompleteGamma_eq_integral {a : ℂ} (ha : 0 < a.re) (z : ℂ) :
    tricomiIncompleteGamma a z =
      (Gamma a)⁻¹ * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * cexp (-(z * t)) := by
  have ha' : ∀ n : ℕ, a ≠ -n := fun n h => by
    have := congr_arg re h
    rw [neg_re, natCast_re] at this
    linarith [n.cast_nonneg (α := ℝ)]
  -- integrate the exponential series termwise
  have hint : HasSum (fun k : ℕ => (-z) ^ k / (k ! * (a + k)))
      (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * cexp (-(z * t))) := by
    have hterm : ∀ k : ℕ, ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * ((-(z * t)) ^ k / k !) =
        (-z) ^ k / (k ! * (a + k)) := fun k => by
      have hcongr : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 →
          (t : ℂ) ^ (a - 1) * ((-(z * t)) ^ k / k !) = (-z) ^ k / k ! * (t : ℂ) ^ (a - 1 + k) :=
        Eventually.of_forall fun t ht => by
          rw [uIoc_of_le (zero_le_one' ℝ)] at ht
          have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.1.ne'
          rw [cpow_add _ _ ht0, cpow_natCast, neg_mul_eq_neg_mul, mul_pow]
          ring
      have hak : a + k ≠ 0 := fun h => by
        have := congr_arg re h
        rw [add_re, natCast_re, zero_re] at this
        linarith [k.cast_nonneg (α := ℝ)]
      have hre : -1 < (a - 1 + k).re := by
        rw [add_re, sub_re, one_re, natCast_re]
        linarith [k.cast_nonneg (α := ℝ)]
      rw [intervalIntegral.integral_congr_ae hcongr, intervalIntegral.integral_const_mul,
        integral_cpow (Or.inl hre), show a - 1 + (k : ℂ) + 1 = a + k by ring, ofReal_one, one_cpow,
        ofReal_zero, zero_cpow hak, sub_zero]
      field_simp
    have hbound : ∀ k : ℕ, ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 →
        ‖(t : ℂ) ^ (a - 1) * ((-(z * t)) ^ k / k !)‖ ≤ t ^ (a.re - 1) * (‖z‖ ^ k / k !) :=
      fun k => Eventually.of_forall fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1, sub_re, one_re, norm_div, norm_pow,
          norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht.1.le _)
        have hzt : ‖z‖ * t ≤ ‖z‖ := mul_le_of_le_one_right (norm_nonneg z) ht.2
        have hzt₀ : 0 ≤ ‖z‖ * t := mul_nonneg (norm_nonneg z) ht.1.le
        gcongr
    convert intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k t => t ^ (a.re - 1) * (‖z‖ ^ k / k !)) (fun k => ?_) hbound
      (Eventually.of_forall fun t _ => (Real.summable_pow_div_factorial ‖z‖).mul_left _) ?_
      (Eventually.of_forall fun t _ => ?_) using 1
    · exact funext fun k => (hterm k).symm
    · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc)
      refine ContinuousOn.mul (fun t ht => ?_) (Continuous.continuousOn (by fun_prop))
      rw [uIoc_of_le zero_le_one] at ht
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr ht.1.ne')).continuousWithinAt
    · simp_rw [tsum_mul_left]
      exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_const _
    · exact (Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp (-(z * t)) :
        HasSum (fun k : ℕ => (-(z * t)) ^ k / k !) (cexp (-(z * t)))).mul_left _
  exact (hasSum_tricomiIncompleteGamma_of_ne_neg_natCast ha' z).unique (hint.mul_left _)

end Complex
