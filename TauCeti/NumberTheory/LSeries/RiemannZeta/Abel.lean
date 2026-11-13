/-
Copyright (c) 2026 Matteo Cipollina and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# The ordinary Abel integral for the Riemann zeta function

For `0 < re s` and `s ≠ 1`, partial summation and analytic continuation give
`ζ(s) = s / (s - 1) - s ∫₁^∞ {t} t^(-s - 1) dt`. The fractional-part kernel has absolute integral
at most `1 / re s`, giving `‖ζ(s)‖ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / re s`.

The identity on `re s > 1` specializes Mathlib's `LSeries_eq_mul_integral` to constant
coefficients. Mathlib's Mellin analyticity theorem treats the fractional part restricted to
`[1, ∞)`, a bounded measurable function that vanishes near zero. The identity theorem then
compares the entire pole-cleared zeta function `riemannZeta₁` with the pole-cleared integral.
No value at `s = 1` is identified with its meromorphic germ.

This is the ordinary fractional-part formula; the alternating-series integral in
`TauCeti.NumberTheory.LSeries.RiemannZeta` includes the different factor `1 - 2 ^ (1 - s)`.

## Provenance

The ordinary formula and its quantitative use are formalized in PNT+, the project of
Alex Kontorovich and Terence Tao. Matteo Cipollina's `RiemannZetaAbelKernel` and
`RiemannZetaAbelContinuation` provide its fractional-part integral formulation. This proof
reuses Mathlib's Mellin and Abel APIs rather than copying the fork's parameter-integral and
finite partial-sum infrastructure.
-/

public section

open Set Filter Topology MeasureTheory Complex Asymptotics
open scoped Topology

namespace TauCeti

private theorem norm_fract_kernel_le {s : ℂ} {t : ℝ} (ht : 1 < t) :
    ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ t ^ (-(s.re + 1)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht)]
  simp only [neg_re, add_re, one_re, norm_real, Real.norm_eq_abs, Int.abs_fract]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
    (Int.fract_lt_one t).le

private theorem fract_kernel_integrable (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  apply Integrable.mono'
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one)
    (measurable_fract.complex_ofReal.mul
      (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_fract_kernel_le ht

private theorem fract_integral_bound (s : ℂ) (hs : 0 < s.re) :
    ‖∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ 1 / s.re := by
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), t ^ (-(s.re + 1)) := by
      apply norm_integral_le_of_norm_le
        (integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_fract_kernel_le ht
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      ring

private theorem fract_integral_differentiableAt (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (fun z ↦ ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1))) s := by
  let f : ℝ → ℂ := (Ici (1 : ℝ)).indicator (fun t ↦ ((Int.fract t : ℝ) : ℂ))
  have hmeas : AEStronglyMeasurable f volume :=
    (measurable_fract.complex_ofReal.indicator measurableSet_Ici).aestronglyMeasurable
  have hbound (t : ℝ) : ‖f t‖ ≤ 1 := by
    dsimp only [f]
    by_cases ht : t ∈ Ici (1 : ℝ)
    · rw [indicator_of_mem ht]
      simpa only [norm_real, Real.norm_eq_abs, Int.abs_fract] using (Int.fract_lt_one t).le
    · simp only [indicator_of_notMem ht, norm_zero, zero_le_one]
  have hlocal : LocallyIntegrableOn f (Ioi (0 : ℝ)) := by
    have H : LocallyIntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioi (0 : ℝ)) :=
      (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ))).locallyIntegrable.locallyIntegrableOn _
    apply H.mono hmeas ?_
    filter_upwards [] with t
    simpa only [norm_one] using hbound t
  have htop : f =O[atTop] (fun t : ℝ ↦ t ^ (-(0 : ℝ))) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with t
    simpa only [neg_zero, Real.rpow_zero, norm_one, one_mul] using hbound t
  have hbot : f =O[𝓝[>] (0 : ℝ)] (fun t : ℝ ↦ t ^ (-((-s).re - 1))) := by
    apply IsBigO.of_bound 0
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    simp only [f, indicator_of_notMem (show t ∉ Ici (1 : ℝ) from not_le.mpr ht.2), norm_zero,
      zero_mul, le_refl]
  have H := (mellin_differentiableAt_of_isBigO_rpow hlocal htop
    (by simpa using hs) hbot (sub_one_lt (-s).re)).comp s differentiableAt_id.neg
  have heq (z : ℂ) : mellin f (-z) =
      ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
    rw [mellin]
    simp_rw [f, ← indicator_smul]
    rw [setIntegral_indicator measurableSet_Ici,
      inter_eq_right.mpr (Ici_subset_Ioi.mpr zero_lt_one), integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [smul_eq_mul, neg_add', mul_comm]
  simpa only [Function.comp_def, heq] using H

private theorem abel_initial (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s *
      ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hO : (fun n : ℕ ↦ ∑ _k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop]
      (fun n ↦ (n : ℝ) ^ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    simp
  have H := LSeries_eq_mul_integral (1 : ℕ → ℂ) (by norm_num : (0 : ℝ) ≤ 1) hs
    (LSeriesSummable_one_iff.mpr hs) hO
  rw [LSeries_one_eq_riemannZeta hs] at H
  simp only [Pi.one_apply] at H
  have hfloor : (fun t : ℝ ↦ (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ)) *
      (t : ℂ) ^ (-(s + 1))) =ᵐ[volume.restrict (Ioi 1)]
      (fun t : ℝ ↦ (t : ℂ) ^ (-s) -
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    have ht0 : 0 ≤ t := by linarith
    have hf : (⌊t⌋₊ : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      have hr : (⌊t⌋₊ : ℝ) = t - Int.fract t := by
        rw [natCast_floor_eq_intCast_floor ht0]
        linarith [Int.self_sub_floor t]
      exact_mod_cast hr
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, hf,
      sub_mul]
    congr 1
    calc
      (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ)^1 * (t : ℂ)^(-(s + 1)) := by rw [Complex.cpow_one]
      _ = (t : ℂ)^(1 + (-(s + 1))) := (Complex.cpow_add _ _ (ofReal_ne_zero.mpr (by linarith))).symm
      _ = _ := by congr 1; ring
  rw [integral_congr_ae hfloor, integral_sub
    (integrableOn_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one)
      (fract_kernel_integrable s (zero_lt_one.trans hs)),
    integral_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one] at H
  simp only [ofReal_one, one_cpow] at H
  rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq] at H
  rw [H]
  ring

/-- The ordinary Abel integral for `ζ` on the punctured right half-plane. The value at the pole
is excluded: `riemannZeta 1` is a totalized value, while this formula represents its pole germ. -/
theorem riemannZeta_eq_sub_integral_fract {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s *
      ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  let G : ℂ → ℂ := fun z ↦ z - z * (z - 1) *
    ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1))
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hG : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.re} := by
    intro z hz
    apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re}) ?_ (hopen.mem_nhds hz)
    intro w hw
    exact (differentiableAt_id.sub ((differentiableAt_id.mul
      (differentiableAt_id.sub_const 1)).mul
      (fract_integral_differentiableAt w hw))).differentiableWithinAt
  have hZ : AnalyticOnNhd ℂ riemannZeta₁ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hopen
  have heq : G =ᶠ[𝓝 (2 : ℂ)] riemannZeta₁ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hz1 : z ≠ 1 := by intro h; subst z; norm_num at hz
    have H := abel_initial z hz
    rw [riemannZeta_eq_inv_sub_mul hz1] at H
    dsimp only [G]
    have hz' := sub_ne_zero.mpr hz1
    field_simp [hz'] at H
    linear_combination -H
  have H := hG.eqOn_of_preconnected_of_eventuallyEq hZ
    (convex_halfSpace_re_gt 0).isPreconnected (by norm_num) heq hs
  rw [riemannZeta_eq_inv_sub_mul hs1]
  dsimp only [G] at H
  have hs' := sub_ne_zero.mpr hs1
  field_simp [hs']
  linear_combination -H

/-- The ordinary Abel integral bounds `ζ` by its pole term and `‖s‖ / re s`. -/
theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / s.re := by
  rw [riemannZeta_eq_sub_integral_fract hs hs1, show s / (s - 1) = 1 + (s - 1)⁻¹ by
    field_simp [sub_ne_zero.mpr hs1]; ring]
  calc
    _ ≤ ‖1 + (s - 1)⁻¹‖ + ‖s‖ * ‖∫ t in Ioi (1 : ℝ),
        ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ := by
      simpa only [norm_mul] using norm_sub_le (1 + (s - 1)⁻¹)
        (s * ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
    _ ≤ (1 + ‖(s - 1)⁻¹‖) + ‖s‖ * (1 / s.re) :=
      add_le_add (by simpa using norm_add_le (1 : ℂ) (s - 1)⁻¹)
        (mul_le_mul_of_nonneg_left (fract_integral_bound s hs) (norm_nonneg s))
    _ = _ := by ring

end TauCeti
