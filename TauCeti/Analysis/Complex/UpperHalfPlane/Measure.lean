/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals

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
* `UpperHalfPlane.volume_setOf_re_mem_and_lt_im`: for `A > 0`, the region
  `{re z ∈ S, A < im z}` has invariant measure `volume S * ENNReal.ofReal A⁻¹`.

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
  refine withDensity_absolutelyContinuous' (Measurable.aemeasurable (by fun_prop))
    (ae_of_all _ fun τ ↦ ?_)
  simp [← NNReal.coe_ne_zero, τ.im_ne_zero]

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

/-- The region of `ℍ` lying above the height `A > 0` and over a set `S` of real parts has
invariant measure `volume S * ENNReal.ofReal A⁻¹`. -/
theorem volume_setOf_re_mem_and_lt_im (S : Set ℝ) {A : ℝ} (hA : 0 < A) :
    volume {z : ℍ | z.re ∈ S ∧ A < z.im} = volume S * ENNReal.ofReal A⁻¹ := by
  have himage : (↑) '' {z : ℍ | z.re ∈ S ∧ A < z.im} =
      Complex.measurableEquivRealProd ⁻¹' (S ×ˢ Ioi A) := by
    ext w
    refine ⟨?_, fun hw ↦ ⟨⟨w, hA.trans hw.2⟩, by simpa using hw, rfl⟩⟩
    rintro ⟨z, hz, rfl⟩
    simpa using hz
  rw [volume_eq_lintegral, himage]
  refine (Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ ↦ (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) _).trans ?_
  rw [Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
  simp only
  rw [TauCeti.lintegral_Ioi_inv_sq hA, setLIntegral_const, mul_comm]

end UpperHalfPlane
