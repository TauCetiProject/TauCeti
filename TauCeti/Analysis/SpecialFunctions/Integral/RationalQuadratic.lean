/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import TauCeti.Analysis.Fourier.HaagerupZsido.Defs
public import TauCeti.Analysis.Fourier.Poisson.CauchyLattice

/-!
# Rational quadratic integrals

This file collects the elementary Cauchy-type integrals over the positive
half-line: the single- and repeated-pole integrals, the two-quadratic integral,
the reciprocal step-difference telescoping series, and the integral of the
hyperbolic weight against a difference of adjacent resolvents.

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

namespace TauCeti
namespace HaagerupZsido

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform

noncomputable section

/-- Integrability of a rescaled Cauchy kernel. -/
private theorem integrable_inv_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    Integrable (fun x : ℝ => (c ^ 2 + x ^ 2)⁻¹) := by
  have hcomp := integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hc)
  have hscaled := hcomp.const_mul (c⁻¹ ^ 2)
  apply hscaled.congr
  filter_upwards [] with x
  have hden : c ^ 2 + x ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hc, sq_nonneg x]
  have hbase : 1 + (c⁻¹ * x) ^ 2 ≠ 0 := by positivity
  field_simp [hc, hden, hbase]

/-- Integral of a Cauchy kernel over the positive half-line. -/
private theorem integral_Ioi_inv_sq_add_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ in Set.Ioi 0, (c ^ 2 + x ^ 2)⁻¹) =
      Real.pi / (2 * c) := by
  have hchange := integral_comp_mul_left_Ioi
    (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 (inv_pos.mpr hc)
  have hleft :
      (∫ x : ℝ in Set.Ioi 0, (1 + (c⁻¹ * x) ^ 2)⁻¹) =
        c ^ 2 * ∫ x : ℝ in Set.Ioi 0, (c ^ 2 + x ^ 2)⁻¹ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    have hden : c ^ 2 + x ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_pos hc, sq_nonneg x]
    have hbase : 1 + (c⁻¹ * x) ^ 2 ≠ 0 := by positivity
    field_simp [hc.ne', hden, hbase]
  rw [hleft] at hchange
  simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero,
    sub_zero, inv_inv, smul_eq_mul] at hchange
  field_simp [hc.ne'] at hchange ⊢
  nlinarith

/-- The repeated-pole Cauchy integral needed when the two positive parameters
coincide. -/
private theorem integral_Ioi_sq_div_sq_add_sq_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ in Set.Ioi 0, x ^ 2 / (c ^ 2 + x ^ 2) ^ 2) =
      Real.pi / (4 * c) := by
  let g : ℝ → ℝ := (id : ℝ → ℝ) / fun x => c ^ 2 + x ^ 2
  let g' : ℝ → ℝ := fun x =>
    (1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1))) /
      (c ^ 2 + x ^ 2) ^ 2
  have hderiv (x : ℝ) := by
    have hden : c ^ 2 + x ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_pos hc, sq_nonneg x]
    exact (hasDerivAt_id x).div ((hasDerivAt_pow 2 x).const_add (c ^ 2)) hden
  have hCauchy : Integrable (fun x : ℝ => (c ^ 2 + x ^ 2)⁻¹) :=
    integrable_inv_sq_add_sq hc.ne'
  have hDerivInt : Integrable g' := by
    apply hCauchy.mono'
    · dsimp only [g']
      have hnum : Continuous (fun x : ℝ =>
          1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1))) := by
        fun_prop
      have hden : Continuous (fun x : ℝ => (c ^ 2 + x ^ 2) ^ 2) := by
        fun_prop
      exact (hnum.div hden fun x => pow_ne_zero _ (by
        nlinarith [sq_pos_of_pos hc, sq_nonneg x])).aestronglyMeasurable
    · filter_upwards [] with x
      have hden : 0 < c ^ 2 + x ^ 2 := by
        nlinarith [sq_pos_of_pos hc, sq_nonneg x]
      have habs : |c ^ 2 - x ^ 2| ≤ c ^ 2 + x ^ 2 := by
        rw [abs_sub_le_iff]
        constructor <;> nlinarith [sq_nonneg c, sq_nonneg x]
      dsimp only [g']
      have hnum : 1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1)) =
          c ^ 2 - x ^ 2 := by norm_num; ring
      rw [hnum]
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hden]
      calc
        |c ^ 2 - x ^ 2| / (c ^ 2 + x ^ 2) ^ 2 ≤
            (c ^ 2 + x ^ 2) / (c ^ 2 + x ^ 2) ^ 2 :=
          div_le_div_of_nonneg_right habs (sq_nonneg _)
        _ = (c ^ 2 + x ^ 2)⁻¹ := by
          field_simp [hden.ne']
  have hgTop : Tendsto g atTop (nhds 0) := by
    have hInv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have hDen : Tendsto (fun x : ℝ => c ^ 2 * x⁻¹ ^ 2 + 1) atTop (nhds 1) := by
      simpa using ((hInv.pow 2).const_mul (c ^ 2)).add tendsto_const_nhds
    have hQuot := hInv.div hDen one_ne_zero
    norm_num only [zero_div] at hQuot
    apply hQuot.congr'
    filter_upwards [eventually_gt_atTop 0] with x hx
    dsimp only [g]
    have hx0 : x ≠ 0 := hx.ne'
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change x⁻¹ / (c ^ 2 * x⁻¹ ^ 2 + 1) = x / (c ^ 2 + x ^ 2)
    field_simp [hx0]
  have hDerivIntegral : (∫ x : ℝ in Set.Ioi 0, g' x) = 0 := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := 0) (m := 0) (fun x _ => hderiv x) hDerivInt.integrableOn hgTop
    simpa [g, g'] using h
  calc
    (∫ x : ℝ in Set.Ioi 0, x ^ 2 / (c ^ 2 + x ^ 2) ^ 2) =
        ∫ x : ℝ in Set.Ioi 0,
          (1 / 2 : ℝ) * (c ^ 2 + x ^ 2)⁻¹ - (1 / 2 : ℝ) * g' x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      dsimp only [g']
      have hnum : 1 * (c ^ 2 + x ^ 2) - x * ((2 : ℝ) * x ^ (2 - 1)) =
          c ^ 2 - x ^ 2 := by norm_num; ring
      rw [hnum]
      have hden : c ^ 2 + x ^ 2 ≠ 0 := by
        nlinarith [sq_pos_of_pos hc, sq_nonneg x]
      field_simp [hden]
      ring
    _ = (1 / 2 : ℝ) * (∫ x : ℝ in Set.Ioi 0, (c ^ 2 + x ^ 2)⁻¹) -
        (1 / 2 : ℝ) * ∫ x : ℝ in Set.Ioi 0, g' x := by
      rw [integral_sub (hCauchy.const_mul _).integrableOn
        (hDerivInt.const_mul _).integrableOn, integral_const_mul, integral_const_mul]
    _ = Real.pi / (4 * c) := by
      rw [integral_Ioi_inv_sq_add_sq hc, hDerivIntegral]
      field_simp [hc.ne']
      ring

/-- The elementary two-Cauchy-denominator integral. -/
private theorem integral_Ioi_sq_div_two_quadratics
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    (∫ y : ℝ in Set.Ioi 0,
        y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2))) =
      Real.pi / (2 * (a + c)) := by
  rcases ha.eq_or_lt with rfl | haPos
  · calc
      (∫ y : ℝ in Set.Ioi 0,
          y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + 0 ^ 2))) =
          ∫ y : ℝ in Set.Ioi 0, (c ^ 2 + y ^ 2)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        have hy0 : y ≠ 0 := hy.ne'
        have hcden : c ^ 2 + y ^ 2 ≠ 0 := by
          nlinarith [sq_pos_of_pos hc, sq_nonneg y]
        field_simp [hy0, hcden]
        ring
      _ = Real.pi / (2 * c) := integral_Ioi_inv_sq_add_sq hc
      _ = Real.pi / (2 * (0 + c)) := by ring
  · by_cases hac : a = c
    · subst a
      calc
        (∫ y : ℝ in Set.Ioi 0,
            y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + c ^ 2))) =
            ∫ y : ℝ in Set.Ioi 0, y ^ 2 / (c ^ 2 + y ^ 2) ^ 2 := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y _
          ring_nf
        _ = Real.pi / (4 * c) := integral_Ioi_sq_div_sq_add_sq_sq hc
        _ = Real.pi / (2 * (c + c)) := by ring
    · have hdiff : c ^ 2 - a ^ 2 ≠ 0 := by
        rw [sub_ne_zero]
        intro hsq
        rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
        · exact hac h.symm
        · nlinarith
      have hCInt : Integrable (fun y : ℝ => (c ^ 2 + y ^ 2)⁻¹) :=
        integrable_inv_sq_add_sq hc.ne'
      have hAInt : Integrable (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) :=
        integrable_inv_sq_add_sq haPos.ne'
      calc
        (∫ y : ℝ in Set.Ioi 0,
            y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2))) =
            ∫ y : ℝ in Set.Ioi 0,
              (c ^ 2 / (c ^ 2 - a ^ 2)) * (c ^ 2 + y ^ 2)⁻¹ -
                (a ^ 2 / (c ^ 2 - a ^ 2)) * (a ^ 2 + y ^ 2)⁻¹ := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y _
          have hcden : c ^ 2 + y ^ 2 ≠ 0 := by
            nlinarith [sq_pos_of_pos hc, sq_nonneg y]
          have haden : a ^ 2 + y ^ 2 ≠ 0 := by
            nlinarith [sq_pos_of_pos haPos, sq_nonneg y]
          field_simp [hdiff, hcden, haden]
          ring
        _ = (c ^ 2 / (c ^ 2 - a ^ 2)) *
              (∫ y : ℝ in Set.Ioi 0, (c ^ 2 + y ^ 2)⁻¹) -
            (a ^ 2 / (c ^ 2 - a ^ 2)) *
              ∫ y : ℝ in Set.Ioi 0, (a ^ 2 + y ^ 2)⁻¹ := by
          rw [integral_sub (hCInt.const_mul _).integrableOn
            (hAInt.const_mul _).integrableOn, integral_const_mul, integral_const_mul]
        _ = (c ^ 2 / (c ^ 2 - a ^ 2)) * (Real.pi / (2 * c)) -
            (a ^ 2 / (c ^ 2 - a ^ 2)) * (Real.pi / (2 * a)) := by
          rw [integral_Ioi_inv_sq_add_sq hc, integral_Ioi_inv_sq_add_sq haPos]
        _ = Real.pi / (2 * (a + c)) := by
          have hsum : a + c ≠ 0 := by positivity
          field_simp [hdiff, hc.ne', haPos.ne', hsum]
          ring

/-- Integrability of the nonnegative rational kernel used in the telescoping
argument. -/
private theorem integrable_sq_div_two_quadratics
    (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ℝ =>
      y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2))) := by
  have hCauchy : Integrable (fun y : ℝ => (c ^ 2 + y ^ 2)⁻¹) :=
    integrable_inv_sq_add_sq hc.ne'
  apply hCauchy.mono'
  · exact (by fun_prop : Measurable (fun y : ℝ =>
      y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)))).aestronglyMeasurable
  · filter_upwards [] with y
    by_cases hy : y = 0
    · subst y
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
        zero_div, norm_zero, add_zero, inv_nonneg]
      positivity
    · have hySq : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      have hC : 0 < y ^ 2 + c ^ 2 := by positivity
      have hA : 0 < y ^ 2 + a ^ 2 := by positivity
      have hquot : 0 ≤ y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hquot]
      calc
        y ^ 2 / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)) ≤
            (y ^ 2 + a ^ 2) / ((y ^ 2 + c ^ 2) * (y ^ 2 + a ^ 2)) :=
          div_le_div_of_nonneg_right (by nlinarith [sq_nonneg a]) (by positivity)
        _ = (c ^ 2 + y ^ 2)⁻¹ := by
          field_simp [hC.ne', hA.ne']
          ring

/-- The elementary reciprocal series telescopes by steps of two. -/
private theorem hasSum_reciprocal_step_difference
    {a : ℝ} (ha : 0 ≤ a) :
    HasSum (fun n : ℕ =>
      (a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) (a + 1)⁻¹ := by
  let u : ℕ → ℝ := fun n => (a + 2 * n + 1)⁻¹
  have hnonneg : ∀ n : ℕ, 0 ≤ u n - u (n + 1) := by
    intro n
    dsimp only [u]
    have hleft : 0 < a + 2 * (n : ℝ) + 1 := by positivity
    have hright : 0 < a + 2 * ((n + 1 : ℕ) : ℝ) + 1 := by positivity
    apply sub_nonneg.mpr
    exact (inv_le_inv₀ hright hleft).2 (by push_cast; linarith)
  have hfinite : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (u n - u (n + 1))) = u 0 - u N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hDenTop : Tendsto (fun n : ℕ => a + 2 * (n : ℝ) + 1) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (a + 1)
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)) using 1
    funext n
    ring
  have huZero : Tendsto u atTop (nhds 0) := by
    exact hDenTop.inv_tendsto_atTop
  rw [show (fun n : ℕ =>
      (a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) =
      fun n : ℕ => u n - u (n + 1) by
    funext n
    dsimp only [u]
    push_cast
    congr 2
    ring]
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
  convert tendsto_const_nhds.sub huZero using 1
  · funext N
    exact hfinite N
  · dsimp only [u]
    norm_num

/-- Integrating the odd-pole expansion against a difference of two adjacent
resolvents produces the elementary step-two telescoping term. -/
theorem integral_weight_mul_reciprocal_difference
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ y : ℝ in Set.Ioi 0,
        weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹)) =
      2 / (a + 1) := by
  let c : ℕ → ℝ := fun n => 2 * n + 1
  let F : ℕ → ℝ → ℝ := fun n y =>
    (4 / Real.pi) *
      (y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + a ^ 2)) -
        y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + (a + 2) ^ 2)))
  have hc (n : ℕ) : 0 < c n := by
    dsimp only [c]
    positivity
  have hFInt (n : ℕ) : IntegrableOn (F n) (Set.Ioi 0) := by
    have hA := integrable_sq_div_two_quadratics a (hc n)
    have hB := integrable_sq_div_two_quadratics (a + 2) (hc n)
    exact ((hA.sub hB).const_mul (4 / Real.pi)).integrableOn
  have hFintegral (n : ℕ) :
      (∫ y : ℝ in Set.Ioi 0, F n y) =
        2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := by
    have hA := integrable_sq_div_two_quadratics a (hc n)
    have hB := integrable_sq_div_two_quadratics (a + 2) (hc n)
    dsimp only [F]
    rw [integral_const_mul, integral_sub hA.integrableOn hB.integrableOn,
      integral_Ioi_sq_div_two_quadratics ha (hc n),
      integral_Ioi_sq_div_two_quadratics (by linarith : 0 ≤ a + 2) (hc n)]
    dsimp only [c]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hleft : a + (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have hright : a + 2 + (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have hstepLeft : a + 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have hstepRight : a + 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hpi, hleft, hright, hstepLeft, hstepRight]
    ring
  have hFnonneg (n : ℕ) {y : ℝ} (hy : y ∈ Set.Ioi (0 : ℝ)) : 0 ≤ F n y := by
    have hyPos : 0 < y := hy
    have hcommon : 0 < y ^ 2 + (c n) ^ 2 := by positivity
    have hA : 0 < y ^ 2 + a ^ 2 := by positivity
    have hAB : y ^ 2 + a ^ 2 ≤ y ^ 2 + (a + 2) ^ 2 := by
      nlinarith
    have hden :
        (y ^ 2 + (c n) ^ 2) * (y ^ 2 + a ^ 2) ≤
          (y ^ 2 + (c n) ^ 2) * (y ^ 2 + (a + 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hAB hcommon.le
    have hquot :
        y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + (a + 2) ^ 2)) ≤
          y ^ 2 / ((y ^ 2 + (c n) ^ 2) * (y ^ 2 + a ^ 2)) :=
      div_le_div_of_nonneg_left (sq_nonneg y) (mul_pos hcommon hA) hden
    dsimp only [F]
    positivity
  have hFnormIntegral (n : ℕ) :
      (∫ y : ℝ in Set.Ioi 0, ‖F n y‖) =
        2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := by
    calc
      (∫ y : ℝ in Set.Ioi 0, ‖F n y‖) =
          ∫ y : ℝ in Set.Ioi 0, F n y := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        -- names the application so the norm bound applies to it directly.
        change ‖F n y‖ = F n y
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg n hy)]
      _ = 2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := hFintegral n
  have hNormSum : Summable (fun n : ℕ => ∫ y : ℝ in Set.Ioi 0, ‖F n y‖) := by
    apply ((hasSum_reciprocal_step_difference ha).summable.mul_left (2 : ℝ)).congr
    intro n
    exact (hFnormIntegral n).symm
  have hExchange :
      (∑' n : ℕ, ∫ y : ℝ in Set.Ioi 0, F n y) =
        ∫ y : ℝ in Set.Ioi 0, ∑' n : ℕ, F n y :=
    integral_tsum_of_summable_integral_norm hFInt hNormSum
  have hPointwise {y : ℝ} (hy : 0 < y) :
      (∑' n : ℕ, F n y) =
        weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹) := by
    have hw := weight_div_eq_tsum_odd hy
    let D : ℝ := y ^ 2 *
      ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹)
    calc
      (∑' n : ℕ, F n y) =
          ∑' n : ℕ, (4 / Real.pi) *
            (y ^ 2 + (2 * n + 1) ^ 2)⁻¹ * D := by
        apply tsum_congr
        intro n
        dsimp only [F, c, D]
        have hC : y ^ 2 + (2 * (n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
        have hA : y ^ 2 + a ^ 2 ≠ 0 := by positivity
        have hB : y ^ 2 + (a + 2) ^ 2 ≠ 0 := by positivity
        field_simp [hC, hA, hB]
      _ = (4 / Real.pi) *
          ((∑' n : ℕ, (y ^ 2 + (2 * n + 1) ^ 2)⁻¹) * D) := by
        rw [← tsum_mul_right, ← tsum_mul_left]
        apply tsum_congr
        intro n
        ring
      _ = (weight y / y) * D := by
        have hw' : weight y / y =
            (4 / Real.pi) *
              ∑' n : ℕ, (y ^ 2 + (2 * (n : ℝ) + 1) ^ 2)⁻¹ := by
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hw
        rw [hw']
        ring
      _ = weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹) := by
        dsimp only [D]
        field_simp [hy.ne']
  calc
    (∫ y : ℝ in Set.Ioi 0,
        weight y * y *
          ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹)) =
        ∫ y : ℝ in Set.Ioi 0, ∑' n : ℕ, F n y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact (hPointwise hy).symm
    _ = ∑' n : ℕ, ∫ y : ℝ in Set.Ioi 0, F n y := hExchange.symm
    _ = ∑' n : ℕ,
        2 * ((a + 2 * n + 1)⁻¹ - (a + 2 * n + 3)⁻¹) := by
      apply tsum_congr
      exact hFintegral
    _ = 2 * (a + 1)⁻¹ := by
      rw [tsum_mul_left, (hasSum_reciprocal_step_difference ha).tsum_eq]
    _ = 2 / (a + 1) := by rw [div_eq_mul_inv]

end

end HaagerupZsido
end TauCeti
