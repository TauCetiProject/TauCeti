/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Truncated Laplace transforms and the estimates of Newman's contour argument

Let `f : ℝ → ℂ` be bounded by `M` on `[0, ∞)`. Newman's Tauberian theorem compares the
Laplace transform `G z = ∫ t in Ici 0, f t * exp (-z t)` with its truncations
`G_T z = ∫ t in 0..T, f t * exp (-z t)` against the kernel `exp (T z) (1 + z² / R²) / z` on
the circle `‖z‖ = R`. This file proves the analytic input of that comparison:

* each truncation `G_T` is entire, and the full transform `G` is holomorphic on `0 < re z`,
  being a locally uniform limit of truncations;
* the tail bound `‖G z - G_T z‖ ≤ M exp (-T re z) / re z` for `0 < re z`, and the bound
  `‖G_T z‖ ≤ M exp (-T re z) / (-re z)` for `re z < 0`;
* on the circle `‖z‖ = R` the kernel factor satisfies `‖1 + z² / R²‖ = 2 |re z| / R`, so that
  both integrands of the contour argument are bounded by `2 M / R²`, uniformly in `T`;
* Cauchy's formula for the entire function `G_T`: its kernel integral over the full circle
  is `2πi ∫ t in 0..T, f t`.

The factor `1 + z² / R²` cancels the small denominator `re z` exactly on the circle, which is
what makes the estimates independent of `T`.

## References

* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
* D. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104
  (1997), 705–708.
-/

public section

open Filter MeasureTheory Set Metric
open scoped Topology Real Complex Interval

namespace TauCeti.LSeries

variable {f : ℝ → ℂ} {M T : ℝ}

/-- The modulus of the Laplace kernel `exp (-z t)` at a real time `t`. -/
private lemma norm_cexp_neg_mul_ofReal (z : ℂ) (t : ℝ) :
    ‖cexp (-z * t)‖ = Real.exp (-z.re * t) := by
  simp [Complex.norm_exp]

/-- The modulus of the growth factor `exp (T z)` of Newman's kernel. -/
private lemma norm_cexp_ofReal_mul (T : ℝ) (z : ℂ) :
    ‖cexp (T * z)‖ = Real.exp (T * z.re) := by
  simp [Complex.norm_exp]

/-- **Truncated Laplace transforms are entire.** If `f` is interval integrable on `[a, b]`, then
`z ↦ ∫ t in a..b, f t * exp (-z t)` is complex differentiable everywhere. -/
theorem differentiable_intervalIntegral_mul_cexp_neg_mul {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    Differentiable ℂ fun z : ℂ ↦ ∫ t in a..b, f t * cexp (-z * t) := by
  intro z₀
  -- On `Ι a b` we have `|t| ≤ C` and, for `z` within distance `1` of `z₀`, `‖exp (-z t)‖ ≤ K`;
  -- so the `z`-derivative `-t f t exp (-z t)` of the integrand is dominated by `C * K * ‖f t‖`.
  set C := max |a| |b|
  set K := Real.exp ((‖z₀‖ + 1) * C)
  have habs : ∀ t ∈ Ι a b, |t| ≤ C := by
    intro t ht
    rcases le_total a b with hab | hab
    · rw [uIoc_of_le hab] at ht
      exact abs_le_max_abs_abs ht.1.le ht.2
    · rw [uIoc_of_ge hab] at ht
      exact (abs_le_max_abs_abs ht.1.le ht.2).trans_eq (max_comm _ _)
  have hexp : ∀ t ∈ Ι a b, ∀ z ∈ ball z₀ 1, ‖cexp (-z * t)‖ ≤ K := by
    intro t ht z hz
    rw [norm_cexp_neg_mul_ofReal]
    refine Real.exp_le_exp.mpr ?_
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_sub_norm_le z z₀
      rw [mem_ball_iff_norm] at hz
      linarith
    calc -z.re * t ≤ |z.re| * |t| := (le_abs_self _).trans_eq (by rw [abs_mul, abs_neg])
      _ ≤ (‖z₀‖ + 1) * C :=
          mul_le_mul ((Complex.abs_re_le_norm z).trans hz') (habs t ht) (abs_nonneg _)
            (by positivity)
  have hcont : ∀ z : ℂ, Continuous fun t : ℝ ↦ cexp (-z * t) := fun z ↦ by fun_prop
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun z t ↦ f t * (cexp (-z * t) * (-(t : ℂ))))
    (bound := fun t ↦ C * K * ‖f t‖) (ball_mem_nhds z₀ one_pos)
    (.of_forall fun z ↦ hf.def'.aestronglyMeasurable.mul (hcont z).aestronglyMeasurable)
    (hf.mul_continuousOn (hcont z₀).continuousOn)
    (hf.def'.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ ↦
      cexp (-z₀ * t) * (-(t : ℂ))).aestronglyMeasurable)
    (.of_forall fun t ht z hz ↦ ?_) (hf.norm.const_mul _)
    (.of_forall fun t _ z _ ↦ ?_)).2.differentiableAt
  · rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    calc ‖f t‖ * (‖cexp (-z * t)‖ * |t|) ≤ ‖f t‖ * (K * C) := by
          gcongr
          exacts [hexp t ht z hz, habs t ht]
      _ = C * K * ‖f t‖ := by ring
  · have h := ((hasDerivAt_id' z).neg.mul_const (t : ℂ)).cexp.const_mul (f t)
    simpa using h

/-- For `0 < re z`, the Laplace integrand of a function bounded on `[0, ∞)` is integrable there. -/
theorem integrableOn_mul_cexp_neg_mul (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ ↦ f t * cexp (-z * t)) (Ici 0) := by
  refine Integrable.mono' (((integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (exp_neg_integrableOn_Ioi 0 hz)).const_mul M)
    (hf.mul (by fun_prop : Continuous fun t : ℝ ↦ cexp (-z * t)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ici fun t ht ↦ ?_)
  rw [norm_mul, norm_cexp_neg_mul_ofReal]
  exact mul_le_mul_of_nonneg_right (hbound t ht) (Real.exp_pos _).le

/-- **Tail bound.** For `0 < re z` and `0 ≤ T`, the Laplace transform of a function bounded by
`M` on `[0, ∞)` differs from its truncation at `T` by at most `M exp (-T re z) / re z`. -/
theorem norm_integral_sub_intervalIntegral_mul_cexp_neg_mul_le
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) {z : ℂ} (hz : 0 < z.re) (hT : 0 ≤ T) :
    ‖(∫ t in Ici (0 : ℝ), f t * cexp (-z * t)) - ∫ t in (0 : ℝ)..T, f t * cexp (-z * t)‖ ≤
      M * Real.exp (-z.re * T) / z.re := by
  have hint := integrableOn_mul_cexp_neg_mul hf hbound hz
  rw [integral_Ici_eq_integral_Ioi, ← intervalIntegral.integral_interval_add_Ioi
    ((integrableOn_Ici_iff_integrableOn_Ioi).mp hint) (hint.mono_set (Ioi_subset_Ici hT)),
    add_sub_cancel_left]
  calc ‖∫ t in Ioi T, f t * cexp (-z * t)‖ ≤ ∫ t in Ioi T, M * Real.exp (-z.re * t) := by
        refine norm_integral_le_of_norm_le ((integrableOn_exp_mul_Ioi (by linarith) T).const_mul M)
          (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_)
        rw [norm_mul, norm_cexp_neg_mul_ofReal]
        exact mul_le_mul_of_nonneg_right (hbound t (hT.trans (le_of_lt ht))) (Real.exp_pos _).le
    _ = M * Real.exp (-z.re * T) / z.re := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith), neg_div_neg_eq, mul_div_assoc]

/-- **Left half-plane bound.** For `re z < 0` and `0 ≤ T`, the truncated Laplace transform of a
function bounded by `M` on `[0, T]` is at most `M exp (-T re z) / (-re z)`. -/
theorem norm_intervalIntegral_mul_cexp_neg_mul_le_of_re_neg
    (hbound : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ M) {z : ℂ} (hz : z.re < 0) (hT : 0 ≤ T) :
    ‖∫ t in (0 : ℝ)..T, f t * cexp (-z * t)‖ ≤ M * Real.exp (-z.re * T) / -z.re := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0 ⟨le_rfl, hT⟩)
  have hg : IntegrableOn (fun t : ℝ ↦ M * Real.exp (-z.re * t)) (Iic T) :=
    (integrableOn_exp_mul_Iic (by linarith) T).const_mul M
  calc ‖∫ t in (0 : ℝ)..T, f t * cexp (-z * t)‖
      ≤ ∫ t in (0 : ℝ)..T, M * Real.exp (-z.re * t) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hT (.of_forall fun t ht ↦ ?_)
          ((by fun_prop : Continuous fun t : ℝ ↦ M * Real.exp (-z.re * t)).intervalIntegrable _ _)
        rw [norm_mul, norm_cexp_neg_mul_ofReal]
        exact mul_le_mul_of_nonneg_right (hbound t (Ioc_subset_Icc_self ht)) (Real.exp_pos _).le
    _ ≤ ∫ t in Iic T, M * Real.exp (-z.re * t) := by
        rw [intervalIntegral.integral_of_le hT]
        exact setIntegral_mono_set hg (.of_forall fun t ↦ by positivity)
          (.of_forall fun t ht ↦ (Ioc_subset_Iic_self ht : t ∈ Iic T))
    _ = M * Real.exp (-z.re * T) / -z.re := by
        rw [integral_const_mul, integral_exp_mul_Iic (by linarith), mul_div_assoc]

/-- **Holomorphy of the Laplace transform.** If `f` is bounded on `[0, ∞)`, its Laplace transform
`z ↦ ∫ t in Ici 0, f t * exp (-z t)` is complex differentiable on the half-plane `0 < re z`. -/
theorem differentiableOn_integral_mul_cexp_neg_mul
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) :
    DifferentiableOn ℂ (fun z : ℂ ↦ ∫ t in Ici (0 : ℝ), f t * cexp (-z * t)) {z | 0 < z.re} := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0 (mem_Ici.mpr le_rfl))
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  -- The truncations at `n : ℕ` converge to the transform uniformly on each `{c < re z}`.
  have hloc (n : ℕ) : IntervalIntegrable f volume 0 n := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le n.cast_nonneg).mpr
      (Integrable.mono' (integrableOn_const measure_Ioc_lt_top.ne (C := M))
        (hf.mono_set (Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self))
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ hbound t (le_of_lt ht.1)))
  refine TendstoLocallyUniformlyOn.differentiableOn (φ := atTop)
    (F := fun (n : ℕ) (z : ℂ) ↦ ∫ t in (0 : ℝ)..n, f t * cexp (-z * t)) ?_
    (.of_forall fun n ↦
      (differentiable_intervalIntegral_mul_cexp_neg_mul (hloc n)).differentiableOn) hopen
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε z₀ hz₀
  have hc : 0 < z₀.re / 2 := half_pos hz₀
  refine ⟨{z | z₀.re / 2 < z.re}, mem_nhdsWithin_of_mem_nhds
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (half_lt_self hz₀)), ?_⟩
  have hlim : Tendsto (fun n : ℕ ↦ M * Real.exp (-(z₀.re / 2) * n) / (z₀.re / 2)) atTop (𝓝 0) := by
    have := ((Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg
      (neg_lt_zero.mpr hc))).const_mul M).div_const (z₀.re / 2)
    simpa using this
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hn
  calc _ ≤ M * Real.exp (-z.re * n) / z.re :=
        norm_integral_sub_intervalIntegral_mul_cexp_neg_mul_le hf hbound (hc.trans hz) n.cast_nonneg
    _ ≤ M * Real.exp (-(z₀.re / 2) * n) / (z₀.re / 2) := by
        gcongr

/-- On the circle `‖z‖ = R`, the factor `1 + z² / R²` of Newman's kernel has modulus
`2 |re z| / R`. -/
theorem norm_one_add_sq_div_sq_of_norm_eq {z : ℂ} {R : ℝ} (hz : ‖z‖ = R) (hR : 0 < R) :
    ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ = 2 * |z.re| / R := by
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  -- On the circle `R² = z * conj z`, so `R² + z² = z * (conj z + z) = z * 2 re z`.
  have hR2 : (R : ℂ) ^ 2 = z * (starRingEnd ℂ) z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; push_cast; ring
  have hkey : 1 + z ^ 2 / (R : ℂ) ^ 2 = z * (z + (starRingEnd ℂ) z) / (R : ℂ) ^ 2 := by
    field_simp
    rw [hR2]
    ring
  rw [hkey, Complex.add_conj]
  simp only [norm_div, norm_mul, norm_pow, hz, Complex.norm_real, Real.norm_eq_abs,
    abs_two, abs_of_pos hR]
  field_simp

/-- **Right-arc integrand bound.** On the circle `‖z‖ = R` with `0 < re z`, the difference
between the Laplace transform of a function bounded by `M` on `[0, ∞)` and its truncation at
`T ≥ 0`, multiplied by Newman's kernel `exp (T z) (1 + z² / R²) / z`, is at most `2 M / R²`. -/
theorem norm_integral_sub_intervalIntegral_mul_kernel_le
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) {z : ℂ} {R : ℝ} (hz : ‖z‖ = R) (hR : 0 < R)
    (hre : 0 < z.re) (hT : 0 ≤ T) :
    ‖((∫ t in Ici (0 : ℝ), f t * cexp (-z * t)) - ∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) *
        cexp (T * z) * (1 + z ^ 2 / (R : ℂ) ^ 2) / z‖ ≤ 2 * M / R ^ 2 := by
  rw [norm_div, norm_mul, norm_mul, norm_cexp_ofReal_mul, norm_one_add_sq_div_sq_of_norm_eq hz hR,
    hz, abs_of_pos hre]
  calc _ ≤ M * Real.exp (-z.re * T) / z.re * Real.exp (T * z.re) * (2 * z.re / R) / R := by
        gcongr
        exact norm_integral_sub_intervalIntegral_mul_cexp_neg_mul_le hf hbound hre hT
    _ = 2 * M / R ^ 2 := by
        have he : Real.exp (T * z.re) = (Real.exp (-z.re * T))⁻¹ := by
          rw [← Real.exp_neg]; ring_nf
        have hre0 : z.re ≠ 0 := hre.ne'
        rw [he]
        field_simp

/-- **Left-arc integrand bound.** On the circle `‖z‖ = R` with `re z < 0`, the truncation at
`T ≥ 0` of the Laplace transform of a function bounded by `M` on `[0, T]`, multiplied by
Newman's kernel `exp (T z) (1 + z² / R²) / z`, is at most `2 M / R²`. -/
theorem norm_intervalIntegral_mul_kernel_le_of_re_neg
    (hbound : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ M) {z : ℂ} {R : ℝ} (hz : ‖z‖ = R) (hR : 0 < R)
    (hre : z.re < 0) (hT : 0 ≤ T) :
    ‖(∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) * cexp (T * z) * (1 + z ^ 2 / (R : ℂ) ^ 2) / z‖ ≤
      2 * M / R ^ 2 := by
  rw [norm_div, norm_mul, norm_mul, norm_cexp_ofReal_mul, norm_one_add_sq_div_sq_of_norm_eq hz hR,
    hz, abs_of_neg hre]
  have hre' : 0 < -z.re := neg_pos.mpr hre
  calc _ ≤ M * Real.exp (-z.re * T) / -z.re * Real.exp (T * z.re) * (2 * -z.re / R) / R := by
        gcongr
        exact norm_intervalIntegral_mul_cexp_neg_mul_le_of_re_neg hbound hre hT
    _ = 2 * M / R ^ 2 := by
        have he : Real.exp (T * z.re) = (Real.exp (-z.re * T))⁻¹ := by
          rw [← Real.exp_neg]; ring_nf
        have hre0 : z.re ≠ 0 := hre.ne
        rw [he]
        field_simp

/-- **Cauchy's formula for a truncated transform.** For `R > 0`, the integral of the truncated
Laplace transform against Newman's kernel `exp (T z) (1 + z² / R²) / z` over the circle
`‖z‖ = R` is `2πi` times its value at `0`, namely `2πi ∫ t in 0..T, f t`. -/
theorem circleIntegral_intervalIntegral_mul_kernel (hf : IntervalIntegrable f volume 0 T)
    {R : ℝ} (hR : 0 < R) :
    (∮ z in C(0, R), (∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) * cexp (T * z) *
        (1 + z ^ 2 / (R : ℂ) ^ 2) / z) = 2 * π * Complex.I * ∫ t in (0 : ℝ)..T, f t := by
  have hd : Differentiable ℂ fun z : ℂ ↦
      (∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) * cexp (T * z) * (1 + z ^ 2 / (R : ℂ) ^ 2) :=
    ((differentiable_intervalIntegral_mul_cexp_neg_mul hf).mul (by fun_prop)).mul (by fun_prop)
  have h := hd.differentiableOn.circleIntegral_sub_inv_smul (c := 0) (R := R)
    (w := 0) (mem_ball_self hR)
  simp only [sub_zero, smul_eq_mul, neg_zero, zero_mul, Complex.exp_zero, mul_one, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero, mul_zero] at h
  simpa only [inv_mul_eq_div, mul_comm] using h

end TauCeti.LSeries
