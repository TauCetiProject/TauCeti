/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NormDet
public import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz

import TauCeti.Analysis.Fredholm.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Coarea for surjective linear maps

For a surjective linear map between finite-dimensional real inner product spaces, integration
along its affine fibers disintegrates volume. The fiber measure is normalized Euclidean
Hausdorff measure of dimension equal to the kernel dimension, and the coarea factor is
`LinearMap.normDet` of the adjoint. All integrals are extended nonnegative integrals, so no
finite-volume or integrability assumption is needed.

The proof uses Mathlib's orthogonal decomposition and its volume normalization. Transverse
change of variables uses the injective Lipschitz area formula
`LipschitzWith.lintegral_image_eq_lintegral_normDet_fderiv_mul` from
`TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz`. This is the linear model for the
coarea formula, and includes projections onto subspaces of arbitrary dimension.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §3.4.
-/

public noncomputable section

open MeasureTheory Measure Set Function
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {L : E →L[ℝ] F}

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- The Hausdorff integral on a linear fiber is the volume integral on any translate of the
kernel parametrizing that fiber. This also holds for weights without a measurability assumption. -/
@[simp]
theorem lintegral_linear_fiber {x : E} (f : E → ℝ≥0∞) :
    ∫⁻ z in L ⁻¹' {L x}, f z ∂μHE[Module.finrank ℝ L.ker] =
      ∫⁻ z : L.ker, f (x + z) := by
  let i : L.ker → E := fun z ↦ x + z
  have hi : Isometry i := (isometry_add_left x).comp isometry_subtype_coe
  have hrange : range i = L ⁻¹' {L x} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      simp [i]
    · intro hy
      refine ⟨⟨y - x, ?_⟩, by simp [i]⟩
      simpa using sub_eq_zero.mpr (mem_singleton_iff.mp hy)
  rw [← hrange, ← hi.map_euclideanHausdorffMeasure,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact hi.isClosedEmbedding.measurableEmbedding.lintegral_map f

/-- **Linear coarea.** For a surjective linear map, volume weighted by the norm determinant
of the adjoint equals the iterated integral over the target and its Hausdorff-measured fibers.
The weight need only be Lebesgue measurable, and both sides may be infinite. -/
theorem lintegral_coarea_linear (hL : Surjective L) {f : E → ℝ≥0∞}
    (hf : AEMeasurable f (volume : Measure E)) :
    ENNReal.ofReal L.adjoint.normDet * ∫⁻ x, f x ∂(volume : Measure E) =
      ∫⁻ y : F, ∫⁻ x in L ⁻¹' {y}, f x ∂μHE[Module.finrank ℝ L.ker]
        ∂(volume : Measure F) := by
  let R := (L.orthogonalKerEquivRange L.range.closed_of_finiteDimensional).trans
    (LinearIsometryEquiv.ofTop F L.range (LinearMap.range_eq_top.mpr hL)).toContinuousLinearEquiv
  let H : F → ℝ≥0∞ := fun y ↦
    ∫⁻ x in L ⁻¹' {y}, f x ∂μHE[Module.finrank ℝ L.ker]
  have harea :=
    R.toContinuousLinearMap.lipschitzWith.lintegral_image_eq_lintegral_normDet_fderiv_mul
      MeasurableSet.univ R.injective.injOn H
  have hchange : (∫⁻ y, H y ∂(volume : Measure F)) = ENNReal.ofReal L.adjoint.normDet *
      ∫⁻ u : L.kerᗮ, H (R u) := by
    have hrange : range R.toContinuousLinearMap = univ := R.surjective.range_eq
    have hJ : R.toContinuousLinearMap.toLinearMap.normDet = L.adjoint.normDet := by
      have hR : R.toContinuousLinearMap.toLinearMap = L.toLinearMap.domRestrict L.kerᗮ := by
        ext u
        simp [R]
      rw [hR]
      exact normDet_domRestrict_orthogonal_ker L hL
    simp only [image_univ, hrange, restrict_univ,
      R.toContinuousLinearMap.fderiv, hJ,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      R.toLinearEquiv.finrank_eq,
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at harea
    simpa only [ContinuousLinearEquiv.coe_coe] using harea
  rw [hchange]
  congr 1
  let e := L.kerᗮ.measurableEquivProd (0 : E)
  have he : MeasurePreserving e (volume : Measure E) (volume.prod volume) := by
    simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, volume_eq_prod] using
      L.kerᗮ.measurePreserving_measurableEquivProd (0 : E)
  have hp := hf.comp_quasiMeasurePreserving he.symm.quasiMeasurePreserving
  rw [← he.symm.lintegral_comp_emb e.symm.measurableEmbedding f]
  trans ∫⁻ u : L.kerᗮ, ∫⁻ v : L.kerᗮᗮ, f (e.symm (u, v))
  · exact lintegral_prod _ hp
  apply lintegral_congr
  intro u
  have hRu : R u = L u := by simp [R]
  rw [hRu]
  simp only [H, lintegral_linear_fiber]
  simp only [e, Submodule.measurableEquivProd_symm_apply, vadd_eq_add, add_zero]
  have hperp : L.kerᗮᗮ = L.ker := Submodule.orthogonal_orthogonal L.ker
  rw [hperp]

omit [FiniteDimensional ℝ F] in
/-- For a Borel measurable nonnegative weight, its integral along each linear fiber is a
Borel measurable function of the target point. -/
theorem measurable_lintegral_linear_fiber (hL : Surjective L) {f : E → ℝ≥0∞}
    (hf : Measurable f) :
    Measurable (fun y : F ↦ ∫⁻ x in L ⁻¹' {y}, f x ∂μHE[Module.finrank ℝ L.ker]) := by
  let : FiniteDimensional ℝ F := Module.Finite.of_surjective L.toLinearMap hL
  let R := (L.orthogonalKerEquivRange L.range.closed_of_finiteDimensional).trans
    (LinearIsometryEquiv.ofTop F L.range (LinearMap.range_eq_top.mpr hL)).toContinuousLinearEquiv
  have hcoord (y : F) :
      (∫⁻ x in L ⁻¹' {y}, f x ∂μHE[Module.finrank ℝ L.ker]) =
        ∫⁻ z : L.ker, f ((R.symm y : E) + z) := by
    have hR (u : L.kerᗮ) : R u = L u := by simp [R]
    have hy : L (R.symm y : E) = y := by
      rw [← hR]
      exact R.apply_symm_apply y
    conv_lhs => rw [← hy]
    exact lintegral_linear_fiber f
  simp_rw [hcoord]
  apply Measurable.lintegral_prod_right'
    (f := fun p : F × L.ker ↦ f ((R.symm p.1 : E) + p.2))
  apply hf.comp
  fun_prop

/-- Ambient almost-everywhere equality descends to Hausdorff-almost-everywhere equality
on almost every fiber of a surjective linear map. -/
theorem ae_ae_eq_linear_fiber (hL : Surjective L) {G : Type*} {f g : E → G}
    (hfg : f =ᵐ[volume] g) :
    ∀ᵐ y : F ∂volume, f =ᵐ[μHE[Module.finrank ℝ L.ker].restrict (L ⁻¹' {y})] g := by
  let s := toMeasurable (volume : Measure E) {x | f x ≠ g x}
  have hs : MeasurableSet s := measurableSet_toMeasurable _ _
  have hnull : volume s = 0 := by
    simpa only [s, measure_toMeasurable] using (ae_iff.mp hfg)
  have hco := lintegral_coarea_linear hL (measurable_one.indicator hs).aemeasurable
  have hzero : (∫⁻ y : F, ∫⁻ x in L ⁻¹' {y}, s.indicator 1 x
      ∂μHE[Module.finrank ℝ L.ker]) = 0 := by
    simpa only [lintegral_indicator_one hs, hnull, mul_zero] using hco.symm
  have hae := (lintegral_eq_zero_iff
    (measurable_lintegral_linear_fiber hL (measurable_one.indicator hs))).mp hzero
  filter_upwards [hae] with y hy
  apply ae_iff.mpr
  apply measure_mono_null (subset_toMeasurable (volume : Measure E) _)
  simpa only [lintegral_indicator_one hs, Pi.zero_apply, s] using hy

/-- A Lebesgue measurable nonnegative weight has a Lebesgue measurable fiber integral.
No finiteness assumption is imposed on either integral. -/
theorem aemeasurable_lintegral_linear_fiber (hL : Surjective L) {f : E → ℝ≥0∞}
    (hf : AEMeasurable f volume) :
    AEMeasurable
      (fun y : F ↦ ∫⁻ x in L ⁻¹' {y}, f x ∂μHE[Module.finrank ℝ L.ker]) volume := by
  apply (measurable_lintegral_linear_fiber hL hf.measurable_mk).aemeasurable.congr
  filter_upwards [ae_ae_eq_linear_fiber hL hf.ae_eq_mk] with y hy
  exact (lintegral_congr_ae hy).symm

/-- A Lebesgue measurable set is Hausdorff measurable on almost every linear fiber.
This permits null modifications of Borel representatives before taking sections. -/
theorem ae_nullMeasurableSet_linear_fiber (hL : Surjective L) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    ∀ᵐ y : F ∂volume,
      NullMeasurableSet s (μHE[Module.finrank ℝ L.ker].restrict (L ⁻¹' {y})) := by
  filter_upwards [ae_ae_eq_linear_fiber hL hs.toMeasurable_ae_eq] with y hy
  exact (measurableSet_toMeasurable volume s).nullMeasurableSet.congr hy

/-- Coarea for Lebesgue measurable sets under a surjective linear map. The fibers carry
normalized Hausdorff measure in the kernel dimension, including zero-dimensional kernels. -/
theorem volume_coarea_linear (hL : Surjective L) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    ENNReal.ofReal L.adjoint.normDet * volume s =
      ∫⁻ y : F, μHE[Module.finrank ℝ L.ker] (s ∩ L ⁻¹' {y}) := by
  have hco := lintegral_coarea_linear (f := s.indicator 1) hL
    (aemeasurable_one.indicator₀ hs)
  rw [lintegral_indicator_one₀ hs] at hco
  refine hco.trans (lintegral_congr_ae ?_)
  filter_upwards [ae_nullMeasurableSet_linear_fiber hL hs] with y hy
  rw [lintegral_indicator_one₀ hy, restrict_apply₀ hy]

end TauCeti
