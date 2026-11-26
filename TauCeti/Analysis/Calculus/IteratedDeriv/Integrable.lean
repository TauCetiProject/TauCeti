/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrability and Landau–Kolmogorov `L¹` inequality for the first derivative

If a `C²` function `f : ℝ → E` into a real normed space has integrable zeroth and second
derivatives on `ℝ`, then its first derivative is automatically integrable as well, and satisfies
the sharp `L¹` Landau–Kolmogorov inequality

`∫ t, ‖deriv f t‖ ≤ h⁻¹ * (∫ t, ‖f t‖) + (h / 2) * (∫ t, ‖iteratedDeriv 2 f t‖)`

for every `h > 0`, hence

`(∫ t, ‖deriv f t‖) ^ 2 ≤ 2 * (∫ t, ‖f t‖) * (∫ t, ‖iteratedDeriv 2 f t‖)`.

The proof uses the symmetric second-order integral identity on `[t - h, t + h]`:

`f (t + h) - f (t - h) = (2 * h) • deriv f t + ∫ α in 0..h, ∫ β in 0..α, (f''(t + β) - f''(t - β))`.

Estimating in `ℝ≥0∞` via Tonelli's theorem and translation invariance of Lebesgue measure yields
the extended-nonnegative inequality without assuming integrability in advance, which simultaneously
proves `Integrable (deriv f)` and the sharp real-valued `L¹` bounds. Passing to
`UniformSpace.Completion E` removes any completeness assumption on `E`.

## Main declarations

* `ContDiff.ofReal_mul_lintegral_eNorm_deriv_le`: the `ℝ≥0∞` Landau–Kolmogorov inequality
  `ENNReal.ofReal h * ∫⁻ t, ‖deriv f t‖ₑ ≤ (∫⁻ t, ‖f t‖ₑ) +`
  `ENNReal.ofReal (h ^ 2 / 2) * ∫⁻ t, ‖iteratedDeriv 2 f t‖ₑ`
  for every `C²` function and step size `h ≥ 0`, with no integrability or completeness assumptions.
* `ContDiff.integrable_deriv`: if `f` is `C²` and `f`, `iteratedDeriv 2 f` are integrable on `ℝ`,
  then `deriv f` is integrable on `ℝ`.
* `ContDiff.integrable_deriv_of_norm_le_div_one_add_sq`: if `f` is `C²` and `f`,
  `iteratedDeriv 2 f` are dominated by `A / (1 + t ^ 2)`, then `deriv f` is integrable on `ℝ`.
* `ContDiff.integrable_iteratedDeriv_of_le_two`: convenience form bundling integrability of
  `iteratedDeriv k f` for all `k ≤ 2`.
* `ContDiff.integral_norm_deriv_le`: step-parameterized `L¹` bound for `h > 0`.
* `ContDiff.sq_integral_norm_deriv_le` and `ContDiff.integral_norm_deriv_le_sqrt`: the sharp
  `L¹` Landau–Kolmogorov inequalities with constant `2` (resp. `√2`).

## References

* E. Landau, *Einige Ungleichungen für zweimal differentiierbare Funktionen*, Proc. London Math.
  Soc. (2) 13 (1914), 43–49.
* A. N. Kolmogorov, *On inequalities between the upper bounds of the successive derivatives of an
  arbitrary function on an infinite interval*, Uch. Zap. Moskov. Gos. Univ. 30 (1939), 3–13.
* A. Kontorovich, T. Tao, *Prime Number Theorem And ...*, Lemma 3.1.7 (integrability of `f'` from
  integrability of `f` and `f''`).
-/

public section

open MeasureTheory Set UniformSpace
open scoped ENNReal

namespace ContDiff

private theorem measurable_lintegral_Ioc_add_sub {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun p : ℝ × ℝ ↦ ∫⁻ β in Ioc (0 : ℝ) p.2, (g (p.1 + β) + g (p.1 - β)) := by
  have hmeas : Measurable fun q : (ℝ × ℝ) × ℝ ↦
      if 0 < q.2 ∧ q.2 ≤ q.1.2 then g (q.1.1 + q.2) + g (q.1.1 - q.2) else 0 := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
    · exact (hg.comp ((measurable_fst.comp measurable_fst).add measurable_snd)).add
        (hg.comp ((measurable_fst.comp measurable_fst).sub measurable_snd))
  have heq : (fun p : ℝ × ℝ ↦ ∫⁻ β in Ioc (0 : ℝ) p.2, (g (p.1 + β) + g (p.1 - β))) =
      fun p : ℝ × ℝ ↦ ∫⁻ β : ℝ,
        if 0 < β ∧ β ≤ p.2 then g (p.1 + β) + g (p.1 - β) else 0 := by
    ext ⟨t, α⟩
    rw [← lintegral_indicator measurableSet_Ioc]
    congr 1 with β
    simp [Set.indicator, Set.mem_Ioc]
  rw [heq]
  exact hmeas.lintegral_prod_right

private theorem lintegral_double_Ioc_add_sub {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    {h : ℝ} (hh : 0 ≤ h) :
    ∫⁻ t, ∫⁻ α in Ioc (0 : ℝ) h, ∫⁻ β in Ioc (0 : ℝ) α, (g (t + β) + g (t - β)) =
      ENNReal.ofReal (h ^ 2) * ∫⁻ t, g t := by
  have h1 : (∫⁻ t, ∫⁻ α in Ioc (0 : ℝ) h, ∫⁻ β in Ioc (0 : ℝ) α, (g (t + β) + g (t - β))) =
      ∫⁻ α in Ioc (0 : ℝ) h, ∫⁻ t, ∫⁻ β in Ioc (0 : ℝ) α, (g (t + β) + g (t - β)) :=
    lintegral_lintegral_swap (measurable_lintegral_Ioc_add_sub hg).aemeasurable
  rw [h1]
  have hinner (α : ℝ) :
      ∫⁻ t, ∫⁻ β in Ioc (0 : ℝ) α, (g (t + β) + g (t - β)) =
        ENNReal.ofReal α * (2 * ∫⁻ t, g t) := by
    have hmeas : AEMeasurable (fun p : ℝ × ℝ ↦ g (p.1 + p.2) + g (p.1 - p.2))
        (volume.prod (volume.restrict (Ioc 0 α))) :=
      ((hg.comp (measurable_fst.add measurable_snd)).add
        (hg.comp (measurable_fst.sub measurable_snd))).aemeasurable
    rw [lintegral_lintegral_swap hmeas]
    have hshift (β : ℝ) : ∫⁻ t, (g (t + β) + g (t - β)) = 2 * ∫⁻ t, g t := by
      have hm : Measurable (fun t : ℝ ↦ g (t + β)) := hg.comp (measurable_id.add_const β)
      rw [lintegral_add_left hm (fun t ↦ g (t - β)), lintegral_add_right_eq_self g β]
      have hsub : ∫⁻ t, g (t - β) = ∫⁻ t, g t := by
        simpa only [sub_eq_add_neg] using lintegral_add_right_eq_self g (-β)
      rw [hsub, two_mul]
    simp_rw [hshift]
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
  have hint_id : ∫⁻ α in Ioc (0 : ℝ) h, ENNReal.ofReal α = ENNReal.ofReal (h ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (continuous_id'.intervalIntegrable 0 h).1
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with _ hα using hα.1.le),
      ← intervalIntegral.integral_of_le hh, integral_id, zero_pow two_ne_zero, sub_zero]
  calc
    ∫⁻ α in Ioc (0 : ℝ) h, ∫⁻ t, ∫⁻ β in Ioc (0 : ℝ) α, (g (t + β) + g (t - β))
      = ∫⁻ α in Ioc (0 : ℝ) h, ENNReal.ofReal α * (2 * ∫⁻ t, g t) := by
          refine setLIntegral_congr_fun measurableSet_Ioc fun α _ ↦ hinner α
    _ = (∫⁻ α in Ioc (0 : ℝ) h, ENNReal.ofReal α) * (2 * ∫⁻ t, g t) :=
          lintegral_mul_const _ ENNReal.measurable_ofReal
    _ = ENNReal.ofReal (h ^ 2 / 2) * (2 * ∫⁻ t, g t) := by
          rw [hint_id]
    _ = (ENNReal.ofReal (h ^ 2 / 2) * ENNReal.ofReal 2) * ∫⁻ t, g t := by
          rw [ENNReal.ofReal_ofNat, mul_assoc]
    _ = ENNReal.ofReal (h ^ 2) * ∫⁻ t, g t := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring

private theorem deriv_add_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : ContDiff ℝ 2 f) (t α : ℝ) :
    deriv f (t + α) = deriv f t + ∫ β in (0 : ℝ)..α, iteratedDeriv 2 f (t + β) := by
  have hd2 : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by norm_num)
  have hc2 : Continuous (iteratedDeriv 2 f) := hf.continuous_iteratedDeriv 2 le_rfl
  have hderiv2 (x : ℝ) : HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (hd2 x).hasDerivAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := α)
    (f := fun β ↦ deriv f (t + β)) (f' := fun β ↦ iteratedDeriv 2 f (t + β))
    (fun β _ ↦ by
      have hc := (hderiv2 (t + β)).scomp β ((hasDerivAt_id β).const_add t)
      simpa only [Function.comp_def, one_smul] using hc)
    ((hc2.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
  simp only [add_zero] at hftc
  rw [hftc, add_sub_cancel]

private theorem deriv_sub_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : ContDiff ℝ 2 f) (t α : ℝ) :
    deriv f (t - α) = deriv f t - ∫ β in (0 : ℝ)..α, iteratedDeriv 2 f (t - β) := by
  have hd2 : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by norm_num)
  have hc2 : Continuous (iteratedDeriv 2 f) := hf.continuous_iteratedDeriv 2 le_rfl
  have hderiv2 (x : ℝ) : HasDerivAt (deriv f) (iteratedDeriv 2 f x) x := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (hd2 x).hasDerivAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := α)
    (f := fun β ↦ deriv f (t - β)) (f' := fun β ↦ -iteratedDeriv 2 f (t - β))
    (fun β _ ↦ by
      have hc := (hderiv2 (t - β)).scomp β ((hasDerivAt_id β).const_sub t)
      simpa only [Function.comp_def, neg_one_smul] using hc)
    ((hc2.comp (continuous_const.sub continuous_id)).neg.intervalIntegrable _ _)
  simp only [sub_zero, intervalIntegral.integral_neg] at hftc
  have hneg := congrArg (-·) hftc
  simp only [neg_neg, neg_sub] at hneg
  rw [hneg]
  abel

private theorem sub_eq_smul_add_double_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} (hf : ContDiff ℝ 2 f) (t h : ℝ) :
    f (t + h) - f (t - h) = (2 * h) • deriv f t +
      ∫ α in (0 : ℝ)..h, ∫ β in (0 : ℝ)..α,
        (iteratedDeriv 2 f (t + β) - iteratedDeriv 2 f (t - β)) := by
  have hd1 : Differentiable ℝ f := hf.differentiable (by decide)
  have hc1 : Continuous (deriv f) := hf.continuous_deriv (by decide)
  have hc2 : Continuous (iteratedDeriv 2 f) := hf.continuous_iteratedDeriv 2 le_rfl
  have hdiff : f (t + h) - f (t - h) = ∫ α in (0 : ℝ)..h, (deriv f (t + α) + deriv f (t - α)) := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := h)
      (f := fun α ↦ f (t + α) - f (t - α))
      (f' := fun α ↦ deriv f (t + α) + deriv f (t - α))
      (fun α _ ↦ by
        have hp : HasDerivAt (fun x ↦ f (t + x)) (deriv f (t + α)) α := by
          simpa only [Function.comp_def, one_smul] using
            (hd1 (t + α)).hasDerivAt.scomp α ((hasDerivAt_id α).const_add t)
        have hm : HasDerivAt (fun x ↦ f (t - x)) (-deriv f (t - α)) α := by
          simpa only [Function.comp_def, neg_one_smul] using
            (hd1 (t - α)).hasDerivAt.scomp α ((hasDerivAt_id α).const_sub t)
        simpa only [sub_neg_eq_add] using hp.fun_sub hm)
      (((hc1.comp (continuous_const.add continuous_id)).add
        (hc1.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _)
    simp only [add_zero, sub_zero, sub_self] at hftc
    exact hftc.symm
  have hsum (α : ℝ) : deriv f (t + α) + deriv f (t - α) = (2 : ℝ) • deriv f t +
      ∫ β in (0 : ℝ)..α, (iteratedDeriv 2 f (t + β) - iteratedDeriv 2 f (t - β)) := by
    have hp : IntervalIntegrable (fun β ↦ iteratedDeriv 2 f (t + β)) volume 0 α :=
      (hc2.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
    have hm : IntervalIntegrable (fun β ↦ iteratedDeriv 2 f (t - β)) volume 0 α :=
      (hc2.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
    rw [deriv_add_eq hf t α, deriv_sub_eq hf t α, intervalIntegral.integral_sub hp hm,
      two_smul ℝ (deriv f t)]
    abel
  have hint_inner : IntervalIntegrable
      (fun α ↦ ∫ β in (0 : ℝ)..α, (iteratedDeriv 2 f (t + β) - iteratedDeriv 2 f (t - β)))
      volume 0 h := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact intervalIntegral.continuous_primitive (fun a b ↦
      ((hc2.comp (continuous_const.add continuous_id)).sub
        (hc2.comp (continuous_const.sub continuous_id))).intervalIntegrable a b) 0
  rw [hdiff]
  simp_rw [hsum]
  rw [intervalIntegral.integral_add intervalIntegrable_const hint_inner]
  simp only [intervalIntegral.integral_const, sub_zero, smul_smul, mul_comm h 2]

private theorem eNorm_deriv_pointwise_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} (hf : ContDiff ℝ 2 f)
    {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    ENNReal.ofReal (2 * h) * ‖deriv f t‖ₑ ≤
      ‖f (t + h)‖ₑ + ‖f (t - h)‖ₑ +
        ∫⁻ α in Ioc (0 : ℝ) h, ∫⁻ β in Ioc (0 : ℝ) α,
          (‖iteratedDeriv 2 f (t + β)‖ₑ + ‖iteratedDeriv 2 f (t - β)‖ₑ) := by
  have heq : (2 * h) • deriv f t = f (t + h) - f (t - h) -
      ∫ α in (0 : ℝ)..h, ∫ β in (0 : ℝ)..α,
        (iteratedDeriv 2 f (t + β) - iteratedDeriv 2 f (t - β)) :=
    eq_sub_of_add_eq (sub_eq_smul_add_double_integral hf t h).symm
  have hnorm_smul : ENNReal.ofReal (2 * h) * ‖deriv f t‖ₑ = ‖(2 * h) • deriv f t‖ₑ := by
    rw [eNorm_smul, Real.eNorm_eq_ofReal_abs, abs_of_nonneg (by linarith)]
  rw [hnorm_smul, heq]
  refine eNorm_sub_le.trans (add_le_add eNorm_sub_le ?_)
  rw [intervalIntegral.integral_of_le hh]
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  rw [intervalIntegral.integral_of_le hα.1.le]
  exact (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun _ ↦ eNorm_sub_le)

private theorem two_mul_lintegral_eNorm_deriv_le_complete {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} (hf : ContDiff ℝ 2 f)
    {h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal (2 * h) * (∫⁻ t, ‖deriv f t‖ₑ) ≤
      2 * (∫⁻ t, ‖f t‖ₑ) + ENNReal.ofReal (h ^ 2) * (∫⁻ t, ‖iteratedDeriv 2 f t‖ₑ) := by
  have hc0 : Continuous (fun t ↦ ‖f t‖ₑ) := hf.continuous.eNorm
  have hc1 : Continuous (fun t ↦ ‖deriv f t‖ₑ) := (hf.continuous_deriv (by decide)).eNorm
  have hc2 : Continuous (fun t ↦ ‖iteratedDeriv 2 f t‖ₑ) :=
    (hf.continuous_iteratedDeriv 2 le_rfl).eNorm
  have hm_plus : Measurable (fun t : ℝ ↦ ‖f (t + h)‖ₑ) :=
    hc0.measurable.comp (measurable_id.add_const h)
  have hm_minus : Measurable (fun t : ℝ ↦ ‖f (t - h)‖ₑ) :=
    hc0.measurable.comp (measurable_id.sub_const h)
  have hm_sum : Measurable (fun t : ℝ ↦ ‖f (t + h)‖ₑ + ‖f (t - h)‖ₑ) :=
    hm_plus.add hm_minus
  rw [← lintegral_const_mul _ hc1.measurable]
  refine (lintegral_mono (eNorm_deriv_pointwise_le hf hh)).trans ?_
  rw [lintegral_add_left hm_sum
      (fun t ↦ ∫⁻ α in Ioc (0 : ℝ) h, ∫⁻ β in Ioc (0 : ℝ) α,
        (‖iteratedDeriv 2 f (t + β)‖ₑ + ‖iteratedDeriv 2 f (t - β)‖ₑ)),
    lintegral_add_left hm_plus (fun t ↦ ‖f (t - h)‖ₑ),
    lintegral_add_right_eq_self (fun t ↦ ‖f t‖ₑ) h]
  have hsub : ∫⁻ t, ‖f (t - h)‖ₑ = ∫⁻ t, ‖f t‖ₑ := by
    simpa only [sub_eq_add_neg] using lintegral_add_right_eq_self (fun t ↦ ‖f t‖ₑ) (-h)
  rw [hsub, ← two_mul, lintegral_double_Ioc_add_sub hc2.measurable hh]

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Extended-nonnegative Landau–Kolmogorov inequality for a `C²` function `f : ℝ → E` and any
step `h ≥ 0`:
`ENNReal.ofReal h * ∫⁻ t, ‖deriv f t‖ₑ ≤ (∫⁻ t, ‖f t‖ₑ) +`
`ENNReal.ofReal (h ^ 2 / 2) * ∫⁻ t, ‖iteratedDeriv 2 f t‖ₑ`.
Neither integrability nor completeness of `E` is assumed. -/
theorem ofReal_mul_lintegral_eNorm_deriv_le {f : ℝ → E} (hf : ContDiff ℝ 2 f)
    {h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal h * (∫⁻ t, ‖deriv f t‖ₑ) ≤
      (∫⁻ t, ‖f t‖ₑ) + ENNReal.ofReal (h ^ 2 / 2) * (∫⁻ t, ‖iteratedDeriv 2 f t‖ₑ) := by
  let F : E →L[ℝ] Completion E := Completion.toComplL
  have hFf : ContDiff ℝ 2 (F ∘ f) := F.contDiff.comp hf
  have hd1 (t : ℝ) : deriv (F ∘ f) t = F (deriv f t) :=
    (F.hasFDerivAt.comp_hasDerivAt t (hf.differentiable (by decide) t).hasDerivAt).deriv
  have hd2_diff : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by norm_num)
  have hd2 (t : ℝ) : iteratedDeriv 2 (F ∘ f) t = F (iteratedDeriv 2 f t) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one]
    have hcomp : deriv (F ∘ f) = F ∘ deriv f := funext hd1
    rw [hcomp]
    exact (F.hasFDerivAt.comp_hasDerivAt t (hd2_diff t).hasDerivAt).deriv
  have hcomp_ineq := two_mul_lintegral_eNorm_deriv_le_complete hFf hh
  simp_rw [Function.comp_apply, hd1, hd2] at hcomp_ineq
  simp only [F, Completion.coe_toComplL, Completion.eNorm_coe] at hcomp_ineq
  have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hcancel (a : ℝ≥0∞) : (2 : ℝ≥0∞)⁻¹ * (2 * a) = a := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel h2ne0 h2top, one_mul]
  have h2sq : ENNReal.ofReal (h ^ 2) = 2 * ENNReal.ofReal (h ^ 2 / 2) := by
    rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul zero_le_two]
    congr 1; ring
  calc ENNReal.ofReal h * (∫⁻ t, ‖deriv f t‖ₑ)
      = (2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (2 * h) * (∫⁻ t, ‖deriv f t‖ₑ)) := by
          rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, mul_assoc, hcancel]
    _ ≤ (2 : ℝ≥0∞)⁻¹ * (2 * (∫⁻ t, ‖f t‖ₑ) +
          ENNReal.ofReal (h ^ 2) * (∫⁻ t, ‖iteratedDeriv 2 f t‖ₑ)) := by gcongr
    _ = (∫⁻ t, ‖f t‖ₑ) + ENNReal.ofReal (h ^ 2 / 2) * (∫⁻ t, ‖iteratedDeriv 2 f t‖ₑ) := by
          rw [h2sq, mul_add, mul_assoc 2, hcancel, hcancel]

/-- If a `C²` function `f : ℝ → E` and its second derivative `iteratedDeriv 2 f` are integrable
on `ℝ`, then its first derivative `deriv f` is also integrable on `ℝ`. -/
theorem integrable_deriv {f : ℝ → E} (hf : ContDiff ℝ 2 f)
    (h0 : Integrable f) (h2 : Integrable (iteratedDeriv 2 f)) :
    Integrable (deriv f) := by
  refine ⟨(hf.continuous_deriv (by decide)).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hstep := hf.ofReal_mul_lintegral_eNorm_deriv_le (h := 1) zero_le_one
  rw [ENNReal.ofReal_one, one_mul] at hstep
  exact hstep.trans_lt
    (ENNReal.add_lt_top.mpr ⟨h0.2, ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2.2⟩)

/-- If a `C²` function `f : ℝ → E` into a real normed space satisfies
`‖f t‖, ‖iteratedDeriv 2 f t‖ ≤ A / (1 + t ^ 2)` for all `t : ℝ`, then `deriv f` is integrable
on `ℝ` (first part of Kontorovich–Tao, Lemma 3.1.7). -/
theorem integrable_deriv_of_norm_le_div_one_add_sq {f : ℝ → E} (hf : ContDiff ℝ 2 f) {A : ℝ}
    (h0 : ∀ t : ℝ, ‖f t‖ ≤ A / (1 + t ^ 2))
    (h2 : ∀ t : ℝ, ‖iteratedDeriv 2 f t‖ ≤ A / (1 + t ^ 2)) :
    Integrable (deriv f) := by
  have hm2 : AEStronglyMeasurable (iteratedDeriv 2 f) :=
    (hf.continuous_iteratedDeriv 2 le_rfl).aestronglyMeasurable
  exact hf.integrable_deriv
    (hf.continuous.aestronglyMeasurable.integrable_of_norm_le_div_one_add_sq (ae_of_all _ h0))
    (hm2.integrable_of_norm_le_div_one_add_sq (ae_of_all _ h2))

/-- Convenience form bundling integrability of `iteratedDeriv k f` for all `k ≤ 2` from
integrability of `f` and `iteratedDeriv 2 f`. -/
theorem integrable_iteratedDeriv_of_le_two {f : ℝ → E} (hf : ContDiff ℝ 2 f)
    (h0 : Integrable f) (h2 : Integrable (iteratedDeriv 2 f)) :
    ∀ k ≤ 2, Integrable (iteratedDeriv k f) := by
  intro k hk
  interval_cases k
  · simpa only [iteratedDeriv_zero] using h0
  · simpa only [iteratedDeriv_one] using hf.integrable_deriv h0 h2
  · exact h2

/-- Step-parameterized `L¹` Landau–Kolmogorov bound: for every `h > 0`,
`∫ t, ‖deriv f t‖ ≤ h⁻¹ * (∫ t, ‖f t‖) + (h / 2) * (∫ t, ‖iteratedDeriv 2 f t‖)`. -/
theorem integral_norm_deriv_le {f : ℝ → E} (hf : ContDiff ℝ 2 f)
    (h0 : Integrable f) (h2 : Integrable (iteratedDeriv 2 f)) {h : ℝ} (hh : 0 < h) :
    ∫ t, ‖deriv f t‖ ≤
      h⁻¹ * (∫ t, ‖f t‖) + (h / 2) * (∫ t, ‖iteratedDeriv 2 f t‖) := by
  have h1 : Integrable (deriv f) := hf.integrable_deriv h0 h2
  have hlin := hf.ofReal_mul_lintegral_eNorm_deriv_le hh.le
  have hfin2 : ENNReal.ofReal (h ^ 2 / 2) * (∫⁻ t, ‖iteratedDeriv 2 f t‖ₑ) ≠ ⊤ :=
    ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2.2)
  have hfin : (∫⁻ t, ‖f t‖ₑ) +
      ENNReal.ofReal (h ^ 2 / 2) * (∫⁻ t, ‖iteratedDeriv 2 f t‖ₑ) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h0.2.ne, hfin2⟩
  have hreal := ENNReal.toReal_mono hfin hlin
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hh.le,
    ENNReal.toReal_add h0.2.ne hfin2, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  rw [← integral_norm_eq_lintegral_eNorm h1.aestronglyMeasurable,
    ← integral_norm_eq_lintegral_eNorm h0.aestronglyMeasurable,
    ← integral_norm_eq_lintegral_eNorm h2.aestronglyMeasurable] at hreal
  have hdiv := (div_le_div_iff_of_pos_right hh).mpr hreal
  rw [mul_div_cancel_left₀ _ hh.ne'] at hdiv
  refine hdiv.trans_eq ?_
  field_simp

/-- Sharp `L¹` Landau–Kolmogorov inequality:
`(∫ t, ‖deriv f t‖) ^ 2 ≤ 2 * (∫ t, ‖f t‖) * (∫ t, ‖iteratedDeriv 2 f t‖)`. -/
theorem sq_integral_norm_deriv_le {f : ℝ → E} (hf : ContDiff ℝ 2 f)
    (h0 : Integrable f) (h2 : Integrable (iteratedDeriv 2 f)) :
    (∫ t, ‖deriv f t‖) ^ 2 ≤ 2 * (∫ t, ‖f t‖) * (∫ t, ‖iteratedDeriv 2 f t‖) :=
  TauCeti.sq_le_two_mul_of_forall_pos
    (integral_nonneg fun _ ↦ norm_nonneg _)
    (fun _ hr ↦ hf.integral_norm_deriv_le h0 h2 hr)

/-- Square-root form of the sharp `L¹` Landau–Kolmogorov inequality:
`∫ t, ‖deriv f t‖ ≤ √(2 * (∫ t, ‖f t‖) * (∫ t, ‖iteratedDeriv 2 f t‖))`. -/
theorem integral_norm_deriv_le_sqrt {f : ℝ → E} (hf : ContDiff ℝ 2 f)
    (h0 : Integrable f) (h2 : Integrable (iteratedDeriv 2 f)) :
    ∫ t, ‖deriv f t‖ ≤ √(2 * (∫ t, ‖f t‖) * (∫ t, ‖iteratedDeriv 2 f t‖)) :=
  Real.le_sqrt_of_sq_le (hf.sq_integral_norm_deriv_le h0 h2)

end General

end ContDiff
