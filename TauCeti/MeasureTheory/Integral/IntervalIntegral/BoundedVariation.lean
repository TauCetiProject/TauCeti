/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.BoundedVariation

import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-!
# Oscillatory interval integrals of bounded-variation functions

The second mean value theorem and Jordan decomposition control a weighted integral
by the variation of the integrand and a uniform bound on the primitive of the weight.
This estimate applies to oscillatory weights whose absolute integrals can be large.
-/

public section

open MeasureTheory Set
open scoped ENNReal

/-- The integral of a real weight against the increment from the left endpoint of a
bounded-variation function is bounded by the variation times a bound on the weight's
primitive ending at the right endpoint. -/
theorem BoundedVariationOn.norm_intervalIntegral_smul_sub_left_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {g : ℝ → ℝ} {a b C : ℝ} (hf : BoundedVariationOn f (Icc a b))
    (hab : a ≤ b) (hg : IntervalIntegrable g volume a b)
    (hC : ∀ c ∈ Icc a b, ‖∫ x in c..b, g x‖ ≤ C) :
    ‖∫ x in a..b, g x • (f x - f a)‖ ≤ C * (eVariationOn f (Icc a b)).toReal := by
  have hC₀ : 0 ≤ C := by simpa using hC b ⟨hab, le_rfl⟩
  by_cases! hE : ¬CompleteSpace E
  · simpa [intervalIntegral, integral_of_not_completeSpace hE] using
      mul_nonneg hC₀ (ENNReal.toReal_nonneg (a := eVariationOn f (Icc a b)))
  let _ := hE
  have hfi := hf.intervalIntegrable (μ := volume) (uIcc_of_le hab).subset
  have hgi : IntervalIntegrable (fun x ↦ g x • (f x - f a)) volume a b := by
    refine intervalIntegrable_iff.2 (hg.def'.smul_bdd (eVariationOn f (Icc a b)).toReal ?_ ?_)
    · exact (hfi.sub intervalIntegrable_const).def'.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
      rw [← dist_eq_norm_sub]
      exact hf.dist_le (by simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx) ⟨le_rfl, hab⟩
  obtain ⟨L, hL, hLI⟩ := exists_dual_vector'' ℝ (∫ x in a..b, g x • (f x - f a))
  have hLip : LipschitzWith 1 L := L.lipschitzWith_of_opNorm_le (by simpa using hL)
  have hv := hLip.comp_boundedVariationOn hf
  obtain ⟨p, q, hp, hq, heq, hsum⟩ :=
    hv.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'
  have hmono (w : ℝ → ℝ) (hw : MonotoneOn w (Icc a b)) :
      MonotoneOn (fun x ↦ w x - w a) (Icc a b) := fun _ hx _ hy hxy ↦
    sub_le_sub_right (hw hx hy hxy) _
  have hbound (w : ℝ → ℝ) (hw : MonotoneOn w (Icc a b)) :
      |∫ x in a..b, (w x - w a) * g x| ≤ (w b - w a) * C := by
    obtain ⟨u, hu, hueq⟩ :=
      exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn
        hab (sub_self (w a)).ge (hmono w hw) hg
    have hwab := sub_nonneg.mpr (hw ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
    rw [hueq, abs_mul, abs_of_nonneg hwab]
    exact mul_le_mul_of_nonneg_left (hC u hu) hwab
  have hint (w : ℝ → ℝ) (hw : MonotoneOn w (Icc a b)) :
      IntervalIntegrable (fun x ↦ (w x - w a) * g x) volume a b := by
    rw [intervalIntegrable_iff]
    refine (hg.def'.smul_of_top_right
      (((hmono w hw).memLp_isCompact isCompact_Icc).mono_measure
        (Measure.restrict_mono_set volume (uIcc_of_le hab ▸ uIoc_subset_uIcc)))).congr
        (.of_forall fun _ ↦ rfl)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hLI
  rw [← hLI, ← L.intervalIntegral_comp_comm hgi]
  have hdecomp (x : ℝ) : L (g x • (f x - f a)) =
      (p x - p a) * g x - (q x - q a) * g x := by
    have hf' (y : ℝ) : L (f y) = p y - q y := congrFun heq y
    simp only [map_smul, map_sub, smul_eq_mul, hf']
    ring
  simp_rw [hdecomp, intervalIntegral.integral_sub (hint p hp) (hint q hq)]
  have hV := variationOnFromTo.abs_le_eVariationOn hv (a := a) (b := b)
  have hLipV := hLip.lipschitzOnWith.comp_eVariationOn_le (mapsTo_univ f (Icc a b))
  simp only [ENNReal.coe_one, one_mul] at hLipV
  have hsum' := hsum a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩
  have hvar := (le_abs_self _).trans (hV.trans (ENNReal.toReal_mono hf hLipV))
  linarith [(le_abs_self _).trans (hbound p hp), (neg_abs_le _).trans' (neg_le_neg (hbound q hq)),
    mul_le_mul_of_nonneg_left (hsum' ▸ hvar) hC₀]
