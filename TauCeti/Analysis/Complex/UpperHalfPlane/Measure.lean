/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The invariant measure on `ℍ` and the Lebesgue measure on `ℂ`

Comparison of Mathlib's invariant measure `volume : Measure ℍ` (`dx dy / y²`) with the
pullback of the Lebesgue measure along the embedding `ℍ ↪ ℂ`: the two are mutually
absolutely continuous, since the density `(Im τ)⁻²` is everywhere positive. Consequently
the invariant measure is positive on nonempty open sets, and preimages of Lebesgue-null
subsets of `ℂ` are null in `ℍ`.

## Main results

* `UpperHalfPlane.volume_absolutelyContinuous_comap`,
  `UpperHalfPlane.comap_absolutelyContinuous_volume`: mutual absolute continuity.
* the `IsOpenPosMeasure` instance for `volume : Measure ℍ`.
* `UpperHalfPlane.volume_preimage_coe_null`: preimages of Lebesgue-null sets are null.
* the `NullSingletonClass` instance for `volume : Measure ℍ`: points, hence countable sets, are
  null.
* `UpperHalfPlane.volume_setOf_re_mem_Ico_and_lt_im`: for `A > 0`, the region
  `{a ≤ re z < b, A < im z}` has invariant measure `ENNReal.ofReal ((b - a) / A)`.

Split out of the Petersson inner-product development ported from the AINTLIB
`LeanModularForms` project
(<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>,
`Modularforms/PeterssonInnerProduct.lean`, Chris Birkbeck).
-/

public section

noncomputable section

open MeasureTheory Measure Set

open scoped NNReal ENNReal

namespace UpperHalfPlane

/-- The pullback of the Lebesgue measure along `ℍ ↪ ℂ` is positive on nonempty open sets. -/
instance : IsOpenPosMeasure (Measure.comap UpperHalfPlane.coe (volume : Measure ℂ)) :=
  IsOpenPosMeasure.comap volume isOpenEmbedding_coe

/-- The invariant measure is absolutely continuous w.r.t. the pullback of the Lebesgue
measure along `ℍ ↪ ℂ`. -/
theorem volume_absolutelyContinuous_comap :
    (volume : Measure ℍ) ≪ Measure.comap UpperHalfPlane.coe volume := by
  rw [volume_def]
  exact withDensity_absolutelyContinuous _ _

/-- The pullback of the Lebesgue measure along `ℍ ↪ ℂ` is absolutely continuous w.r.t. the
invariant measure, since the density `(Im τ)⁻²` is everywhere positive on `ℍ`. -/
theorem comap_absolutelyContinuous_volume :
    Measure.comap UpperHalfPlane.coe (volume : Measure ℂ) ≪ (volume : Measure ℍ) := by
  rw [volume_def]
  refine withDensity_absolutelyContinuous' ?_ (ae_of_all _ fun τ ↦ ?_)
  · exact (measurable_coe_nnreal_ennreal.comp (by fun_prop)).aemeasurable
  · have h1 : (1 / NNReal.mk τ.im τ.im_pos.le : ℝ≥0) ≠ 0 := by
      rw [one_div, ne_eq, inv_eq_zero]
      exact fun h ↦ τ.im_pos.ne' (congrArg NNReal.toReal h)
    exact ENNReal.coe_ne_zero.mpr (pow_ne_zero _ h1)

/-- The invariant measure gives positive mass to nonempty open sets. -/
instance : IsOpenPosMeasure (volume : Measure ℍ) :=
  comap_absolutelyContinuous_volume.isOpenPosMeasure

/-- If a subset of `ℂ` has zero Lebesgue measure, its preimage in `ℍ` has zero invariant
measure. -/
theorem volume_preimage_coe_null {S : Set ℂ} (hS : volume S = 0) :
    (volume : Measure ℍ) (UpperHalfPlane.coe ⁻¹' S) = 0 := by
  refine volume_absolutelyContinuous_comap ?_
  rw [isOpenEmbedding_coe.measurableEmbedding.comap_apply]
  exact measure_mono_null (image_preimage_subset _ _) hS

/-- Points of `ℍ` have zero invariant measure. -/
instance : NullSingletonClass (volume : Measure ℍ) where
  measure_singleton τ := by
    have h := volume_preimage_coe_null (measure_singleton (τ : ℂ))
    rwa [← image_singleton, isOpenEmbedding_coe.injective.preimage_image] at h

/-- The region of `ℍ` lying above the height `A > 0` and over the interval `[a, b)` has invariant
measure `ENNReal.ofReal ((b - a) / A)`, which is zero when `b ≤ a`. -/
theorem volume_setOf_re_mem_Ico_and_lt_im (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    volume {z : ℍ | z.re ∈ Ico a b ∧ A < z.im} = ENNReal.ofReal ((b - a) / A) := by
  -- the inner integral `∫_A^∞ y⁻² dy = A⁻¹`
  have hinner : ∫⁻ y in Ioi A, (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal A⁻¹ := by
    have hint := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hA
    have hval : ∫ y in Ioi A, y ^ (-2 : ℝ) = A⁻¹ := by
      convert integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hA using 1
      norm_num [Real.rpow_neg_one]
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦
        Real.rpow_nonneg (hA.trans hy).le _)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy : 0 < y := hA.trans hy
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [Real.rpow_neg hy.le, Real.nnnorm_of_nonneg hy.le]
  have himage : (↑) '' {z : ℍ | z.re ∈ Ico a b ∧ A < z.im} =
      Complex.measurableEquivRealProd ⁻¹' (Ico a b ×ˢ Ioi A) := by
    ext w
    refine ⟨?_, fun hw ↦ ⟨⟨w, hA.trans hw.2⟩, hw, rfl⟩⟩
    rintro ⟨z, hz, rfl⟩
    exact hz
  rw [volume_eq_lintegral, himage]
  refine (Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ ↦ (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) _).trans ?_
  rw [Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
  simp only
  rw [hinner, setLIntegral_const, Real.volume_Ico, ← ENNReal.ofReal_mul (inv_nonneg.mpr hA.le),
    div_eq_mul_inv, mul_comm]

end UpperHalfPlane
