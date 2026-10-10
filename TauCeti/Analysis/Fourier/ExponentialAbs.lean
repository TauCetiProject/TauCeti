/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.Fourier.Inversion

/-!
# The exponential Fourier transform of the two-sided absolute exponential

This file collects the scalar exponential Fourier-transform prerequisites of the
Haagerup--Zsidó reciprocal kernel: the two-sided Laplace transform with an
oscillatory factor, its Fourier normalization, the associated decay estimates,
and the integrability certificates for the two-sided exponential.

This is a topic split of `ForTauCeti/Analysis/Fourier/HaagerupZsidoKernel.lean`;
declarations are moved verbatim and remain in the `TauCeti.HaagerupZsido`
namespace.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti` at Davis--Kahan
  commit `f35ffc0`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace MeasureTheory

/-- An even function is integrable on the line iff it is integrable on the
positive half-line. -/
theorem integrable_iff_integrableOn_Ioi_of_even {g : ℝ → ℝ}
    (heven : ∀ t, g (-t) = g t) :
    Integrable g ↔ IntegrableOn g (Set.Ioi 0) := by
  refine ⟨fun hg => hg.integrableOn, fun hg => ?_⟩
  have hIic : IntegrableOn g (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    have m : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, heven, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)) hg
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hg

end MeasureTheory

namespace TauCeti
namespace HaagerupZsido

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform

noncomputable section

/-- A two-sided Laplace transform with an oscillatory factor.  This elementary
identity is used both for the Cauchy kernel in Poisson summation and for the
final Fourier transform computation. -/
theorem integral_cexp_neg_mul_abs_mul_cexp
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (∫ t : ℝ,
        Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
          Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) =
      ((2 * y) / (y ^ 2 + x ^ 2) : ℝ) := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
      Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))
  let aNeg : ℂ := (y : ℂ) + (x : ℂ) * Complex.I
  let aPos : ℂ := (-y : ℝ) + (x : ℂ) * Complex.I
  have haNeg : 0 < aNeg.re := by simp [aNeg, hy]
  have haPos : aPos.re < 0 := by simp [aPos, hy]
  have hfNeg : Set.EqOn f (fun t : ℝ => Complex.exp (aNeg * t)) (Set.Iic 0) := by
    intro t ht
    dsimp only [f]
    rw [abs_of_nonpos ht, ← Complex.exp_add]
    congr 1
    simp only [aNeg]
    push_cast
    ring
  have hfPos : Set.EqOn f (fun t : ℝ => Complex.exp (aPos * t)) (Set.Ioi 0) := by
    intro t ht
    dsimp only [f]
    rw [abs_of_pos ht, ← Complex.exp_add]
    congr 1
    simp only [aPos]
    push_cast
    ring
  have hintNeg : IntegrableOn f (Set.Iic 0) :=
    (integrableOn_exp_mul_complex_Iic haNeg 0).congr_fun hfNeg.symm measurableSet_Iic
  have hintPos : IntegrableOn f (Set.Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi haPos 0).congr_fun hfPos.symm measurableSet_Ioi
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change ∫ t, f t = _
  rw [← intervalIntegral.integral_Iic_add_Ioi hintNeg hintPos]
  calc
    (∫ t in Set.Iic 0, f t) + ∫ t in Set.Ioi 0, f t =
        (∫ (t : ℝ) in Set.Iic 0, Complex.exp (aNeg * (t : ℂ))) +
          ∫ (t : ℝ) in Set.Ioi 0, Complex.exp (aPos * (t : ℂ)) := by
      congr 1
      · exact setIntegral_congr_fun measurableSet_Iic hfNeg
      · exact setIntegral_congr_fun measurableSet_Ioi hfPos
    _ = (1 : ℂ) / aNeg - (1 : ℂ) / aPos := by
      rw [integral_exp_mul_complex_Iic haNeg,
        integral_exp_mul_complex_Ioi haPos]
      simp
      ring
    _ = ((2 * y) / (y ^ 2 + x ^ 2) : ℝ) := by
      have hden : y ^ 2 + x ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg x]
      apply Complex.ext
      · rw [Complex.sub_re, Complex.div_re, Complex.div_re, Complex.ofReal_re]
        simp only [aNeg, aPos, Complex.normSq_apply, Complex.one_re, Complex.one_im,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        field_simp [hden]
        ring
      · rw [Complex.sub_im, Complex.div_im, Complex.div_im, Complex.ofReal_im]
        simp only [aNeg, aPos, Complex.normSq_apply, Complex.one_re, Complex.one_im,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        field_simp [hden]
        ring

/-- Fourier transform of the two-sided exponential in Mathlib's normalization. -/
theorem fourier_cexp_neg_two_pi_mul_abs
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    𝓕 (fun t : ℝ =>
        Complex.exp ((-(2 * Real.pi * y * |t|) : ℝ) : ℂ)) x =
      ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hscale : 0 < 2 * Real.pi * y := by positivity
  calc
    (∫ t : ℝ,
        Complex.exp (↑(-2 * Real.pi * t * x) * Complex.I) •
          Complex.exp ((-(2 * Real.pi * y * |t|) : ℝ) : ℂ)) =
        ∫ t : ℝ,
          Complex.exp ((-((2 * Real.pi * y) * |t|) : ℝ) : ℂ) *
            Complex.exp ((((t * (-2 * Real.pi * x) : ℝ) : ℂ) * Complex.I)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hphase :
          Complex.exp (↑(-2 * Real.pi * t * x) * Complex.I) =
            Complex.exp ((((t * (-2 * Real.pi * x) : ℝ) : ℂ) * Complex.I)) := by
        congr 1
        push_cast
        ring
      simp only [smul_eq_mul, hphase]
      ring
    _ = (((2 * (2 * Real.pi * y)) /
          ((2 * Real.pi * y) ^ 2 + (-2 * Real.pi * x) ^ 2) : ℝ) : ℂ) :=
      integral_cexp_neg_mul_abs_mul_cexp (-2 * Real.pi * x) hscale
    _ = ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ) := by
      norm_cast
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hden : y ^ 2 + x ^ 2 ≠ 0 := by
        nlinarith [sq_nonneg x]
      field_simp [hpi, hden]
      norm_num
      ring

/-- Two-sided exponentials decay faster than every real inverse power. -/
theorem cexp_neg_mul_abs_isLittleO_rpow_cocompact
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (fun x : ℝ => Complex.exp ((-(a * |x|) : ℝ) : ℂ))
      =o[cocompact ℝ] (fun x : ℝ => |x| ^ s) := by
  apply IsLittleO.of_norm_left
  simp only [Complex.norm_exp, Complex.ofReal_re]
  rw [cocompact_eq_atBot_atTop, isLittleO_sup]
  constructor
  · have h := (isLittleO_exp_neg_mul_rpow_atTop ha s).comp_tendsto
      tendsto_neg_atBot_atTop
    refine h.congr' ?_ ?_
    · filter_upwards [eventually_lt_atBot 0] with x hx
      simp [abs_of_neg hx]
    · filter_upwards [eventually_lt_atBot 0] with x hx
      simp [abs_of_neg hx]
  · refine (isLittleO_exp_neg_mul_rpow_atTop ha s).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp [abs_of_pos hx]
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp [abs_of_pos hx]

/-- The Cauchy function occurring as the transform has quadratic decay. -/
theorem cauchy_fourier_isBigO_rpow_neg_two
    {y : ℝ} (hy : 0 < y) :
    (fun x : ℝ => ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ))
      =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  refine IsBigO.of_bound (y / Real.pi) ?_
  filter_upwards [isCompact_Icc.compl_mem_cocompact] with x hx
  have hxabs : 1 ≤ |x| := by
    have hnle : ¬ |x| ≤ 1 := by
      simpa only [mem_compl_iff, mem_Icc, abs_le] using hx
    exact (lt_of_not_ge hnle).le
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hxabs
  have hsum_pos : 0 < y ^ 2 + x ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hx0, sq_nonneg y]
  have hquot_nonneg : 0 ≤ y / (Real.pi * (y ^ 2 + x ^ 2)) := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hquot_nonneg,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg (abs_nonneg x), Real.rpow_two, sq_abs]
  calc
    y / (Real.pi * (y ^ 2 + x ^ 2)) =
        (y / Real.pi) / (y ^ 2 + x ^ 2) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ (y / Real.pi) / x ^ 2 := by
      exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_ne_zero hx0)
        (by nlinarith [sq_nonneg y])
    _ = (y / Real.pi) * (x ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- Two-sided integrability of a symmetric exponential. -/
private theorem integrable_exp_neg_mul_abs {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ => Real.exp (-y * |t|)) := by
  refine (integrable_iff_integrableOn_Ioi_of_even (fun t => by rw [abs_neg])).mpr ?_
  apply (exp_neg_integrableOn_Ioi 0 hy).congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [abs_of_pos (show (0 : ℝ) < t from ht)]

/-- Integrability of the modulated two-sided exponential. -/
theorem integrable_cexp_neg_mul_abs_mul_cexp (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ =>
      Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) := by
  apply (integrable_exp_neg_mul_abs hy).mono'
  · exact (by fun_prop : Measurable fun t : ℝ =>
      Complex.exp ((-(y * |t|) : ℝ) : ℂ) *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_exp,
      Complex.ofReal_re, neg_mul]

end

end HaagerupZsido
end TauCeti
