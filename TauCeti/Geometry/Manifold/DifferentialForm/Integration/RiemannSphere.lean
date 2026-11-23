/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Measure
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Parametrization
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Measure
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The Fubini–Study form has total integral one

The Riemann sphere `OnePoint ℂ`, regarded as a real surface through its holomorphic charts, carries
the canonical orientation of its complex structure (`TauCeti.complexManifoldOrientation`), in which
every holomorphic chart is positively oriented. This file proves that the Fubini–Study form
`ω_FS` (`OnePoint.fubiniStudyForm`) integrates to `1` over the sphere with this orientation
(`OnePoint.integralTopForm_fubiniStudyForm`): `∫ ω_FS = 1`. This is the normalization with which
symplectic areas on the sphere are measured. The sphere of area `a` carries `a • ω_FS`, whose
integral is then `a` by `TauCeti.integralTopForm_smul`, and the opposite orientation gives `-1`
by `TauCeti.integralTopForm_neg`.

The integral is computed through the inclusion `ℂ → OnePoint ℂ`, the inverse of the affine chart.
It parametrizes the sphere minus the single point `∞`, a null set; its derivative is the identity
of `ℂ` (`OnePoint.hasMFDerivAt_coe`), so it is positively oriented, and on the oriented basis
`(1, i)` of `ℂ` the form `ω_FS` takes the value of the Fubini–Study density
`ρ(z) = 1 / (π (1 + |z|²)²)`. The integral of the form is therefore the integral of `ρ` over the
plane, which is `1` (`OnePoint.integral_fubiniStudyDensity`).

The same computation without orientations shows that the measure `|ω_FS|` of the form gives the
sphere total mass one (`OnePoint.measure_fubiniStudyForm_univ`): in the affine chart it is
Lebesgue measure with density `ρ`, and the remaining point `∞` is null.

## Main results

* `OnePoint.integralTopForm_fubiniStudyForm`: the Fubini–Study form integrates to `1` over the
  Riemann sphere with its complex orientation.
* `OnePoint.measure_fubiniStudyForm_univ`: its measure gives the sphere total mass one.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Section 2 (the Fubini–Study metric, normalized so that a line has area one).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 16 (integration of top forms over parametrizations).
-/

public section

noncomputable section

open Set Filter MeasureTheory Module TauCeti
open scoped Manifold TauCeti.ComplexManifold

namespace OnePoint

attribute [local instance] Complex.finrank_real_complex_fact

/-- **The Fubini–Study form has total integral one.** Over the Riemann sphere with the canonical
orientation of its complex structure, reindexed from `Fin (2 * finrank ℂ ℂ)` to `Fin 2`, the
Fubini–Study form `ω_FS` integrates to `1`. -/
theorem integralTopForm_fubiniStudyForm :
    integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
      (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      fubiniStudyForm.val = 1 := by
  obtain ⟨l, hl⟩ := ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
    (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))).exists_lift
  have hc : IsCompact (_root_.tsupport (α := ℂ [⋀^Fin 2]→L[ℝ] ℝ) fubiniStudyForm.val) :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  have hrefl : (ContinuousLinearEquiv.refl ℝ ℂ).toLinearEquiv = LinearEquiv.refl ℝ ℂ :=
    LinearEquiv.ext fun _ ↦ rfl
  -- The inclusion `ℂ → OnePoint ℂ`, with the identity as derivative, parametrizes the sphere
  -- minus `∞` and is positively oriented.
  have h := integralTopForm_eq_oriented_parametrization l Complex.basisOneI fubiniStudyForm.val
    (fubiniStudyForm.isSmoothForm.integrableTopForm hc Complex.basisOneI) MeasurableSet.univ
    (Set.countable_singleton (∞ : OnePoint ℂ)).isNullSet
    (by rw [Set.image_univ, compl_infty]) coe_injective.injOn
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ ℂ) (fun z _ ↦ hasMFDerivAt_coe z)
    (fun z _ ↦ by
      rw [← Manifold.Orientation.orientationAt_mk, hl,
        orientationAt_reindex_complexManifoldOrientation_complex]
      exact (congrArg (fun f ↦ Orientation.map (Fin 2) f Complex.basisOneI.orientation)
        hrefl).trans (by rw [Orientation.map_refl, Equiv.refl_apply, Complex.orientation]))
  have hvol : Complex.basisOneI.addHaar = volume := by
    rw [← Complex.toBasis_orthonormalBasisOneI, OrthonormalBasis.addHaar_eq_volume]
  rw [← hl, h.2, Measure.restrict_univ, hvol]
  -- On the basis `(1, i)` the form is the Fubini–Study density.
  refine (integral_congr_ae (ae_of_all _ fun z ↦ ?_)).trans integral_fubiniStudyDensity
  have hz := (SmoothBundleForm.eval₂_apply fubiniStudyForm (z : OnePoint ℂ) (1 : ℂ)
    Complex.I).symm.trans (eval₂_fubiniStudyForm_coe z 1 Complex.I)
  simp only [map_one, one_mul, Complex.I_im, mul_one] at hz
  convert hz using 2
  funext i
  refine (ContinuousLinearEquiv.refl_apply ℝ ℂ _).trans ?_
  fin_cases i <;> simp

/-- **The Fubini–Study form has total area one.** The measure `|ω_FS|` of the Fubini–Study form
gives the Riemann sphere measure `1`: in the affine chart it is Lebesgue measure with density
`ρ(z) = 1 / (π (1 + |z|²)²)`, which integrates to one (`OnePoint.integral_fubiniStudyDensity`),
and the remaining point `∞` is null. -/
theorem measure_fubiniStudyForm_univ {m : MeasurableSpace (OnePoint ℂ)}
    [BorelSpace (OnePoint ℂ)] :
    RoughForm.measure fubiniStudyForm.val (univ : Set (OnePoint ℂ)) = 1 := by
  set e := extChartAt 𝓘(ℝ, ℂ) ((0 : ℂ) : OnePoint ℂ)
  have hsrc : e.source = {∞}ᶜ := by
    simp [e, affineChart_source]
  have himage : e '' {∞}ᶜ = univ :=
    eq_univ_of_forall fun y ↦ ⟨(y : OnePoint ℂ), coe_ne_infty y, by simp [e]⟩
  -- In the affine chart the coefficient on a basis `b` is `ρ` times the area of `b`.
  have hcoef (y : ℂ) (b : Basis (Fin 2) ℝ ℂ) :
      RoughForm.inChartAt fubiniStudyForm.val ((0 : ℂ) : OnePoint ℂ) y b =
        fubiniStudyDensity y * Complex.orientation.volumeForm b := by
    have h := RoughForm.inChartAt_chart_apply fubiniStudyForm.val _
      (by simp [e] : ((y : ℂ) : OnePoint ℂ) ∈ e.source) b
    simp only [extChartAt_coe, Function.comp_apply, chartAt_coe, affineChart_coe,
      modelWithCornersSelf_coe, id_eq] at h
    refine h.trans ((SmoothBundleForm.apply_eq_eval₂ _ _ _).trans ?_)
    rw [eval₂_fubiniStudyForm_tangentCoordChange (by simp), ← Orientation.volumeFormL_apply,
      Complex.orientation_volumeFormL_apply]
    simp
  -- Lebesgue measure of `ℂ` is the Haar measure of `b` scaled by the area of `b`.
  have hvol (b : Basis (Fin 2) ℝ ℂ) :
      (volume : Measure ℂ) = ENNReal.ofReal |Complex.orientation.volumeForm b| • b.addHaar := by
    rw [Complex.orientation.abs_volumeForm_apply_eq_sqrt_det_gram, b.volume_eq_smul_addHaar]
  have hint : Integrable fubiniStudyDensity :=
    Integrable.of_integral_ne_zero (by rw [integral_fubiniStudyDensity]; exact one_ne_zero)
  set b := finBasisOfFinrankEq ℝ ℂ Complex.finrank_real_complex
  calc RoughForm.measure fubiniStudyForm.val univ
      = RoughForm.measure fubiniStudyForm.val {∞}ᶜ := by
        rw [← compl_union_self {(∞ : OnePoint ℂ)}, measure_union disjoint_compl_left
          (measurableSet_singleton _), measure_singleton, add_zero]
    -- In the affine chart, `|ω_FS|` is the density `ρ` against Lebesgue measure.
    _ = ∫⁻ z, ENNReal.ofReal (fubiniStudyDensity z) := by
        rw [RoughForm.measure_apply_of_subset _ (measurableSet_singleton _).compl hsrc.ge,
          himage, Measure.restrict_univ]
        simp_rw [hcoef, abs_mul, abs_of_pos (fubiniStudyDensity_pos _),
          ENNReal.ofReal_mul (fubiniStudyDensity_pos _).le]
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hvol b, lintegral_smul_measure,
          smul_eq_mul, mul_comm]
    _ = 1 := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun z ↦ (fubiniStudyDensity_pos z).le),
          integral_fubiniStudyDensity, ENNReal.ofReal_one]

end OnePoint
