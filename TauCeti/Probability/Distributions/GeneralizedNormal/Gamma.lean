/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedGamma.PDF
public import TauCeti.Probability.Distributions.GeneralizedNormal.Affine
public import TauCeti.Probability.Distributions.Rademacher

/-!
# The Rademacher–Gamma construction of a generalized normal law

If `ε` is Rademacher and `G` is an independent unit-rate Gamma variable of shape `p⁻¹`,
then `m + s * ε * G ^ p⁻¹` has the generalized normal law of location `m`, scale `s`, and
shape `p`, for positive `s` and `p`. This identifies the density-defined law with a
construction from independent variables, through both a product-measure pushforward and
a `HasLaw` theorem.

The positive magnitude has the generalized gamma law with parameters `(p⁻¹, p, s)`.
Its equally weighted mixture with its reflection has the generalized normal density;
translation supplies the location parameter.

## References

* S. Nadarajah, *A generalized normal distribution*, Journal of Applied Statistics 32(7),
  685–694 (2005).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {s p : ℝ}

private theorem half_generalizedGammaPDF_eq (hs : 0 < s) (hp : 0 < p) {x : ℝ}
    (hx : x ≠ 0) :
    (1 / 2 : ℝ≥0∞) * generalizedGammaPDF p⁻¹ p s x +
        (1 / 2 : ℝ≥0∞) * generalizedGammaPDF p⁻¹ p s (-x) =
      generalizedNormalPDF 0 s p x := by
  have hcoef : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hcoef, generalizedNormalPDF_of_pos hs hp]
  simp only [generalizedGammaPDF_eq_ofReal,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_add
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (generalizedGammaPDFReal_nonneg _ _ _ _))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (generalizedGammaPDFReal_nonneg _ _ _ _))]
  congr 1
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [generalizedGammaPDFReal_of_nonpos hx.le,
      generalizedGammaPDFReal_of_pos (inv_pos.mpr hp) hp.ne' hs (neg_pos.mpr hx)]
    simp only [abs_of_pos hp, inv_mul_cancel₀ hp.ne', sub_self, rpow_zero, mul_one,
      sub_zero, abs_of_neg (div_neg_of_neg_of_pos hx hs), neg_div]
    ring
  · rw [generalizedGammaPDFReal_of_pos (inv_pos.mpr hp) hp.ne' hs hx,
      generalizedGammaPDFReal_of_nonpos (neg_nonpos.mpr hx.le)]
    simp only [abs_of_pos hp, inv_mul_cancel₀ hp.ne', sub_self, rpow_zero, mul_one,
      sub_zero, abs_of_pos (div_pos hx hs)]
    ring

/-- Symmetrizing a generalized gamma magnitude of shape `p⁻¹` and power `p` gives the centered
generalized normal law. This includes the invalid-parameter zero laws. -/
theorem generalizedNormalMeasure_eq_add_map_neg (s p : ℝ) :
    generalizedNormalMeasure 0 s p =
      (1 / 2 : ℝ≥0∞) • generalizedGammaMeasure p⁻¹ p s +
        (1 / 2 : ℝ≥0∞) • (generalizedGammaMeasure p⁻¹ p s).map (fun x : ℝ ↦ -x) := by
  by_cases h : 0 < s ∧ 0 < p
  swap
  · have hgamma : ¬ (0 < p⁻¹ ∧ p ≠ 0 ∧ 0 < s) := by
      rintro ⟨hpinv, _, hs⟩
      exact h ⟨hs, inv_pos.mp hpinv⟩
    simp [generalizedNormalMeasure_of_not_pos h,
      generalizedGammaMeasure_of_not_valid hgamma]
  obtain ⟨hs, hp⟩ := h
  have hneg : (generalizedGammaMeasure p⁻¹ p s).map (fun x : ℝ ↦ -x) =
      volume.withDensity (fun x ↦ generalizedGammaPDF p⁻¹ p s (-x)) := by
    have h := map_affine_withDensity_volume (a := 0) (b := -1)
      (generalizedGammaPDF p⁻¹ p s) (by norm_num)
    simp only [zero_add, neg_one_mul] at h
    rw [generalizedGammaMeasure_eq_withDensity, h]
    congr 1
    ext x
    simp [div_neg]
  have hnegmeas : Measurable (fun x : ℝ ↦ generalizedGammaPDF p⁻¹ p s (-x)) :=
    (measurable_generalizedGammaPDF _ _ _).comp measurable_neg
  rw [hneg, generalizedGammaMeasure_eq_withDensity,
    ← withDensity_smul _ (measurable_generalizedGammaPDF _ _ _),
    ← withDensity_smul _ hnegmeas,
    ← withDensity_add_left (by fun_prop), generalizedNormalMeasure_eq_withDensity]
  apply withDensity_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  exact (half_generalizedGammaPDF_eq hs hp hx).symm

/-- An independent Rademacher sign and unit-rate Gamma variable of shape `p⁻¹` construct a
generalized normal variable by `m + s * ε * G ^ p⁻¹`. -/
@[simp]
theorem map_rademacher_prod_gammaMeasure_generalizedNormalMeasure (m : ℝ)
    (hs : 0 < s) (hp : 0 < p) :
    (rademacherMeasure.prod (gammaMeasure p⁻¹ 1)).map
        (fun z : ℝ × ℝ ↦ m + s * z.1 * z.2 ^ p⁻¹) = generalizedNormalMeasure m s p := by
  have hcenter :
      (rademacherMeasure.prod (gammaMeasure p⁻¹ 1)).map
          (fun z : ℝ × ℝ ↦ s * z.1 * z.2 ^ p⁻¹) = generalizedNormalMeasure 0 s p := by
    rw [rademacherMeasure_eq]
    simp (disch := fun_prop) only [Measure.add_prod, Measure.prod_smul_left,
      Measure.map_add, Measure.map_smul, Measure.dirac_prod, Measure.map_map]
    have hneg : (fun z : ℝ × ℝ ↦ s * z.1 * z.2 ^ p⁻¹) ∘ Prod.mk (-1) =
        (fun x : ℝ ↦ -x) ∘ (fun x : ℝ ↦ s * x ^ p⁻¹) := by
      ext x
      simp
    have hpos : (fun z : ℝ × ℝ ↦ s * z.1 * z.2 ^ p⁻¹) ∘ Prod.mk 1 =
        fun x : ℝ ↦ s * x ^ p⁻¹ := by
      ext x
      simp
    rw [hneg, hpos, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← generalizedGammaMeasure_of_valid (inv_pos.mpr hp) hp.ne' hs,
      generalizedNormalMeasure_eq_add_map_neg]
    simp only [ENNReal.smul_def]
    simp [add_comm]
  have htranslate := generalizedNormalMeasure_map_affine 0 s p m (c := 1) one_ne_zero
  simp only [mul_zero, add_zero, abs_one, one_mul] at htranslate
  rw [← htranslate, ← hcenter, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

end TauCeti.Probability

namespace ProbabilityTheory.IndepFun

open TauCeti.Probability

/-- Independent Rademacher and Gamma variables give a generalized normal variable after
multiplying the sign by the scaled Gamma power. -/
theorem hasLaw_generalizedNormalMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ε G : Ω → ℝ} {m s p : ℝ}
    (h : IndepFun ε G P) (hs : 0 < s) (hp : 0 < p)
    (hε : HasLaw ε rademacherMeasure P) (hG : HasLaw G (gammaMeasure p⁻¹ 1) P) :
    HasLaw (fun ω ↦ m + s * ε ω * G ω ^ p⁻¹) (generalizedNormalMeasure m s p) P := by
  have _ := hε.isProbabilityMeasure
  rw [← map_rademacher_prod_gammaMeasure_generalizedNormalMeasure m hs hp]
  exact (hasLaw_map (X := fun z : ℝ × ℝ ↦ m + s * z.1 * z.2 ^ p⁻¹)
    (by fun_prop)).fun_comp (h.hasLaw_prod hε hG)

end ProbabilityTheory.IndepFun
