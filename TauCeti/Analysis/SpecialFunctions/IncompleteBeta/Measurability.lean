/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Basic

import TauCeti.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Joint measurability of incomplete Beta functions

The regularized incomplete Beta function and its inverse are measurable jointly in both shape
parameters and their argument. This permits measurable parameter families of Beta quantiles,
including the zero values of the inverse outside the positive-shape, interior-level domain.
The incomplete Beta function retains its distinct atomic convention at first shape zero.

The integral argument follows the parameterized-indicator construction in
`TauCeti.measurable_lowerIncompleteGamma`. The inverse uses its existing sublevel-set
characterization, without requiring continuity in the shape parameters.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

/-- The regularized incomplete Beta function is jointly measurable in both shape parameters
and its argument, including its boundary convention at first shape zero. -/
@[fun_prop]
theorem measurable_regularizedIncompleteBeta :
    Measurable fun p : (ℝ × ℝ) × ℝ => regularizedIncompleteBeta p.1.1 p.1.2 p.2 := by
  have hS : MeasurableSet {q : ((ℝ × ℝ) × ℝ) × ℝ |
      q.2 ∈ Ioc 0 (min 1 (max q.1.2 0))} := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop))
  have hF : Measurable fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      (Ioc 0 (min 1 (max q.1.2 0))).indicator
        (fun t => t ^ (q.1.1.1 - 1) * (1 - t) ^ (q.1.1.2 - 1)) q.2 := by
    simp only [indicator_apply]
    exact Measurable.ite hS (by fun_prop) measurable_const
  have hI : Measurable fun p : (ℝ × ℝ) × ℝ =>
      ∫ t in (0 : ℝ)..min 1 (max p.2 0), t ^ (p.1.1 - 1) * (1 - t) ^ (p.1.2 - 1) := by
    convert (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable using 1
    funext p
    rw [intervalIntegral.integral_of_le (le_min zero_le_one (le_max_right _ _)),
      ← integral_indicator measurableSet_Ioc]
  have hM : Measurable fun p : (ℝ × ℝ) × ℝ =>
      if p.1.1 = 0 ∧ 0 < p.1.2 ∧ 0 ≤ p.2 then (1 : ℝ)
      else if 0 < p.1.1 ∧ 0 < p.1.2 then
        (∫ t in (0 : ℝ)..min 1 (max p.2 0),
          t ^ (p.1.1 - 1) * (1 - t) ^ (p.1.2 - 1)) / beta p.1.1 p.1.2 else 0 := by
    simp only [beta]
    exact Measurable.ite (by measurability) measurable_const
      (Measurable.ite (by measurability) (hI.div (by fun_prop)) measurable_const)
  convert hM using 1
  funext p
  rcases le_or_gt p.1.2 0 with hb | hb
  · simp [regularizedIncompleteBeta_eq_zero_of_nonpos_right hb, not_lt.mpr hb]
  rcases lt_trichotomy p.1.1 0 with ha | ha | ha
  · simp [regularizedIncompleteBeta_eq_zero_of_neg_left ha, ha.ne, not_lt.mpr ha.le]
  · rcases le_or_gt 0 p.2 with hx | hx
    · simp [ha, hb, hx, regularizedIncompleteBeta_zero_left]
    · simp [ha, not_le.mpr hx, regularizedIncompleteBeta_eq_zero_of_neg _ _ hx]
  · simp [ha.ne', ha, hb, regularizedIncompleteBeta_def_of_pos ha hb]

/-- The inverse regularized incomplete Beta function is jointly measurable in both shape
parameters and its level. Outside the positive-shape, interior-level domain it is zero. -/
@[fun_prop]
theorem measurable_uncurry_inverseRegularizedIncompleteBeta :
    Measurable fun p : (ℝ × ℝ) × ℝ => inverseRegularizedIncompleteBeta p.1.1 p.1.2 p.2 := by
  let V : Set ((ℝ × ℝ) × ℝ) := {p | 0 < p.1.1 ∧ 0 < p.1.2 ∧ 0 < p.2 ∧ p.2 < 1}
  have hV : MeasurableSet V := by
    dsimp [V]
    measurability
  refine measurable_of_Iic fun x => ?_
  have hpre : (fun p : (ℝ × ℝ) × ℝ =>
      inverseRegularizedIncompleteBeta p.1.1 p.1.2 p.2) ⁻¹' Iic x =
      (V ∩ {p | p.2 ≤ regularizedIncompleteBeta p.1.1 p.1.2 x}) ∪
        (Vᶜ ∩ {_p | 0 ≤ x}) := by
    ext ⟨⟨a, b⟩, u⟩
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_compl_iff,
      mem_ofPred_eq, V]
    by_cases h : 0 < a ∧ 0 < b ∧ 0 < u ∧ u < 1
    · rw [inverseRegularizedIncompleteBeta_le_iff h.1 h.2.1 h.2.2.1 h.2.2.2]
      tauto
    · rw [inverseRegularizedIncompleteBeta_eq_zero h]
      tauto
  rw [hpre]
  exact (hV.inter (measurableSet_le measurable_snd
    (measurable_regularizedIncompleteBeta.comp (measurable_fst.prodMk measurable_const)))).union
    (hV.compl.inter (MeasurableSet.const _))

end TauCeti
