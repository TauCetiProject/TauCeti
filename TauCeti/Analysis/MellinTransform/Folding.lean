/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.MultHaar

/-!
# Folding Mellin integrals at a reciprocal symmetry point

The involution `t ↦ a² / t` exchanges the two sides of `a` and preserves `dt / t`.
A function invariant under this reflection is integrable exactly when its upper half is,
and its integral is twice that upper integral when the cutoff is positive. Norm invariance alone
similarly bounds the Mellin transform on the imaginary axis.

For a normalized Dirichlet theta series the symmetry point is `a = 1 / √q`, and the
Mellin parameter on the critical line is `s - 1/2`. This is the normalization of
`New.integral_norm_thetaSeries_div` in the shorter GRH formalization
(<https://github.com/lsernau/grh-lean>, revision `72fead1`, `Lib/Analytic/DirichletTheta`).
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- Reciprocal reflection about a positive cutoff carries `dt / t` on the upper ray to
`dt / t` on the lower ray. -/
theorem measurePreserving_sq_div_multHaar_restrict_Ioi {a : ℝ} (ha : 0 < a) :
    MeasurePreserving (fun t : ℝ ↦ a ^ 2 / t) (multHaar.restrict (Ioi a))
      (multHaar.restrict (Ioo 0 a)) := by
  have hpres : MeasurePreserving (fun t : ℝ ↦ a ^ 2 / t) multHaar multHaar := by
    have hmul : MeasurePreserving (a ^ 2 * ·) multHaar multHaar :=
      ⟨measurable_const_mul _, map_multHaar_mul_left (sq_pos_of_pos ha)⟩
    simpa only [Function.comp_def, div_eq_mul_inv] using
      hmul.comp (⟨measurable_inv, map_multHaar_inv⟩ : MeasurePreserving Inv.inv multHaar multHaar)
  have hpre : (fun t : ℝ ↦ a ^ 2 / t) ⁻¹' Ioo 0 a = Ioi a := by
    ext t
    simp only [mem_preimage, mem_Ioo, mem_Ioi, div_pos_iff_of_pos_left (sq_pos_of_pos ha)]
    constructor
    · rintro ⟨ht, h⟩
      exact (mul_lt_mul_iff_right₀ ha).mp (by simpa only [pow_two] using (div_lt_iff₀ ht).mp h)
    · intro ht
      exact ⟨ha.trans ht, (div_lt_iff₀ (ha.trans ht)).mpr (by
        simpa only [pow_two] using (mul_lt_mul_iff_right₀ ha).mpr ht)⟩
  simpa only [hpre] using hpres.restrict_preimage (measurableSet_Ioo (a := 0) (b := a))

section Fold

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a : ℝ}

/-- In the presence of reciprocal symmetry, integrability over `dt / t` can be checked just
above the symmetry point. -/
theorem integrable_multHaar_iff_of_sq_div
    (hsym : ∀ᵐ t ∂multHaar.restrict (Ioi a), f (a ^ 2 / t) = f t) :
    Integrable f multHaar ↔ IntegrableOn f (Ioi a) multHaar := by
  by_cases hnonpos : a ≤ 0
  · have hae := ae_pos_multHaar.mono fun _ ht ↦ hnonpos.trans_lt ht
    rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae]
  have ha := lt_of_not_ge hnonpos
  refine ⟨fun h ↦ h.integrableOn, fun h ↦ ?_⟩
  have hemb : MeasurableEmbedding (fun t : ℝ ↦ a ^ 2 / t) := by
    simpa only [Function.comp_def, div_eq_mul_inv] using
      (measurableEmbedding_mulLeft₀ (pow_ne_zero 2 ha.ne')).comp measurableEmbedding_inv
  have hlow := ((measurePreserving_sq_div_multHaar_restrict_Ioi ha).integrable_comp_emb hemb
    (g := f)).mp (h.congr (Filter.EventuallyEq.symm hsym))
  have hleft : IntegrableOn f (Ioc 0 a) multHaar := by
    simpa only [IntegrableOn, Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := multHaar))] using hlow
  -- Use `(0,a]` and `(a,∞)` to cover the support of the measure.
  have hfull := hleft.union h
  rwa [Ioc_union_Ioi_eq_Ioi ha.le, IntegrableOn,
    Measure.restrict_eq_self_of_ae_mem ae_pos_multHaar] at hfull

/-- A reciprocally symmetric function has twice its upper-ray integral against `dt / t`.
If the upper-ray integral is not integrable, both Bochner integrals have the junk value zero. -/
theorem integral_multHaar_eq_two_smul_of_sq_div [NormedSpace ℝ E] (ha : 0 < a)
    (hsym : ∀ᵐ t ∂multHaar.restrict (Ioi a), f (a ^ 2 / t) = f t) :
    ∫ t, f t ∂multHaar = 2 • ∫ t in Ioi a, f t ∂multHaar := by
  by_cases h : IntegrableOn f (Ioi a) multHaar
  · have hfull := (integrable_multHaar_iff_of_sq_div hsym).mpr h
    have hlow : (∫ t in Ioc 0 a, f t ∂multHaar) = ∫ t in Ioi a, f t ∂multHaar := by
      have hp := measurePreserving_sq_div_multHaar_restrict_Ioi ha
      have hm := (hfull.integrableOn (s := Ioo 0 a)).aestronglyMeasurable
      rw [← hp.map_eq] at hm
      rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := multHaar)).symm, ← hp.map_eq,
        integral_map hp.measurable.aemeasurable hm]
      exact integral_congr_ae hsym
    calc
      _ = ∫ t in Ioc 0 a ∪ Ioi a, f t ∂multHaar := by
        rw [Ioc_union_Ioi_eq_Ioi ha.le, Measure.restrict_eq_self_of_ae_mem ae_pos_multHaar]
      _ = _ := by
        rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hfull.integrableOn h,
          hlow, two_nsmul]
  · rw [integral_undef (mt (integrable_multHaar_iff_of_sq_div hsym).mp h),
      integral_undef h, smul_zero]

end Fold

/-- A function with reciprocal symmetry in norm has an absolutely convergent Mellin transform
on the imaginary axis if its norm is integrable against `dt / t` above the symmetry point.
At any smaller cutoff, twice the tail integral of the norm bounds the transform. -/
theorem mellinConvergent_and_norm_mellin_le_of_sq_div {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E} {a b : ℝ} {z : ℂ}
    (hba : b ≤ a) (hz : z.re = 0) (hf : AEStronglyMeasurable f multHaar)
    (hsym : ∀ᵐ t ∂multHaar.restrict (Ioi a), ‖f (a ^ 2 / t)‖ = ‖f t‖)
    (htail : IntegrableOn (fun t ↦ ‖f t‖) (Ioi b) multHaar) :
    MellinConvergent f z ∧ ‖mellin f z‖ ≤ 2 * ∫ t in Ioi b, ‖f t‖ ∂multHaar := by
  have hnorm := (integrable_multHaar_iff_of_sq_div hsym).mpr
    (htail.mono_set (Ioi_subset_Ioi hba))
  have heq : (fun t : ℝ ↦ ‖(t : ℂ) ^ z • f t‖) =ᵐ[multHaar] fun t ↦ ‖f t‖ := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, hz, Real.rpow_zero, one_mul]
  refine ⟨integrable_multHaar_cpow_smul_iff.mp ?_, ?_⟩
  · have hmeas : Measurable (fun t : ℝ ↦ (t : ℂ) ^ z) := by fun_prop
    exact (integrable_norm_iff (hmeas.aestronglyMeasurable.smul hf)).mp (hnorm.congr heq.symm)
  · rw [← integral_multHaar_cpow_smul]
    calc
      _ ≤ ∫ t, ‖(t : ℂ) ^ z • f t‖ ∂multHaar := norm_integral_le_integral_norm _
      _ ≤ 2 * ∫ t in Ioi a, ‖f t‖ ∂multHaar := by
        rw [integral_congr_ae heq]
        by_cases ha : 0 < a
        · rw [integral_multHaar_eq_two_smul_of_sq_div ha hsym, two_nsmul, two_mul]
        · have hae := ae_pos_multHaar.mono fun _ ht ↦ (le_of_not_gt ha).trans_lt ht
          rw [Measure.restrict_eq_self_of_ae_mem hae]
          exact le_mul_of_one_le_left (integral_nonneg fun _ ↦ norm_nonneg _) one_le_two
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set htail (ae_of_all _ fun _ ↦ norm_nonneg _)
          (Filter.Eventually.of_forall (Ioi_subset_Ioi hba))) zero_le_two

end TauCeti
