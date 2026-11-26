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
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Integrals over the Riemann sphere, and the total integral of the Fubini–Study form

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

The same parametrization computes the integral of every integrable top form `φ`: it is the
planar integral of the coefficient `z ↦ φ z ![1, i]` of `φ` in the affine coordinate
(`OnePoint.integralTopForm_eq_integral_apply_coe`), which is integrable
(`OnePoint.integrable_apply_coe`). For instance, the symplectic area of a map of the Riemann
sphere is the planar integral of its area density in the affine coordinate.

The same computation without orientations shows that the measure `|ω_FS|` of the form gives the
sphere total mass one (`OnePoint.measure_fubiniStudyForm_univ`): in the affine chart it is
Lebesgue measure with density `ρ`, and the remaining point `∞` is null.

## Main results

* `OnePoint.integralTopForm_eq_integral_apply_coe`, `OnePoint.integrable_apply_coe`: top forms on
  the Riemann sphere are integrated in the affine coordinate.
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

/-- On the oriented basis `(1, i)` of `ℂ`, the Fubini–Study form at a finite point `z` takes the
value `ρ(z)` of the Fubini–Study density. -/
private theorem fubiniStudyForm_coe_basisOneI (z : ℂ) :
    fubiniStudyForm.val (z : OnePoint ℂ) Complex.basisOneI = fubiniStudyDensity z := by
  have hz := (SmoothBundleForm.eval₂_apply fubiniStudyForm (z : OnePoint ℂ) (1 : ℂ)
    Complex.I).symm.trans (eval₂_fubiniStudyForm_coe z 1 Complex.I)
  simp only [map_one, one_mul, Complex.I_im, mul_one] at hz
  refine (congrArg _ (funext fun i ↦ ?_)).trans hz
  fin_cases i <;> simp

/-- The inclusion `ℂ → OnePoint ℂ`, with the identity as derivative, parametrizes the sphere minus
the null set `{∞}` and is positively oriented for the complex orientation. So an integrable top
form `φ` has integrable coefficient `z ↦ φ z ![1, i]` on the plane, and its integral is the
integral of that coefficient. -/
private theorem integrable_and_integralTopForm_eq_integral {φ : RoughForm 𝓘(ℝ, ℂ) (OnePoint ℂ) ℝ 2}
    (hφ : IntegrableTopForm φ) :
    Integrable (fun z : ℂ ↦ φ (z : OnePoint ℂ) ![(1 : ℂ), Complex.I]) ∧
      integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))) φ =
        ∫ z : ℂ, φ (z : OnePoint ℂ) ![(1 : ℂ), Complex.I] := by
  obtain ⟨l, hl⟩ := ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
    (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))).exists_lift
  have hrefl : (ContinuousLinearEquiv.refl ℝ ℂ).toLinearEquiv = LinearEquiv.refl ℝ ℂ :=
    LinearEquiv.ext fun _ ↦ rfl
  have h := integralTopForm_eq_oriented_parametrization l Complex.basisOneI φ hφ
    MeasurableSet.univ (Set.countable_singleton (∞ : OnePoint ℂ)).isNullSet
    (by rw [Set.image_univ, compl_infty]) coe_injective.injOn
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ ℂ) (fun z _ ↦ hasMFDerivAt_coe z)
    (fun z _ ↦ by
      rw [← Manifold.Orientation.orientationAt_mk, hl,
        orientationAt_reindex_complexManifoldOrientation_complex]
      exact (congrArg (fun f ↦ Orientation.map (Fin 2) f Complex.basisOneI.orientation)
        hrefl).trans (by rw [Orientation.map_refl, Equiv.refl_apply, Complex.orientation]))
  rw [← hl]
  simp only [Measure.restrict_univ, Complex.addHaar_basisOneI, integrableOn_univ,
    Complex.coe_basisOneI] at h
  -- The identity of `ℂ` carries the basis `(1, i)` to the tangent vectors `![1, i]`.
  exact h

/-- **Integrals over the Riemann sphere in the affine coordinate.** The coefficient
`z ↦ φ z ![1, i]` of an integrable top form `φ` on the Riemann sphere in the affine coordinate is
integrable over the plane. -/
theorem integrable_apply_coe {φ : RoughForm 𝓘(ℝ, ℂ) (OnePoint ℂ) ℝ 2}
    (hφ : IntegrableTopForm φ) :
    Integrable (fun z : ℂ ↦ φ (z : OnePoint ℂ) ![(1 : ℂ), Complex.I]) :=
  (integrable_and_integralTopForm_eq_integral hφ).1

/-- **Integrals over the Riemann sphere in the affine coordinate.** Over the Riemann sphere with
the canonical orientation of its complex structure, reindexed from `Fin (2 * finrank ℂ ℂ)` to
`Fin 2`, the integral of an integrable top form `φ` is the planar integral of its coefficient
`z ↦ φ z ![1, i]` in the affine coordinate. The point `∞` missed by the affine coordinate is a
null set. -/
theorem integralTopForm_eq_integral_apply_coe {φ : RoughForm 𝓘(ℝ, ℂ) (OnePoint ℂ) ℝ 2}
    (hφ : IntegrableTopForm φ) :
    integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
      (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))) φ =
      ∫ z : ℂ, φ (z : OnePoint ℂ) ![(1 : ℂ), Complex.I] :=
  (integrable_and_integralTopForm_eq_integral hφ).2

/-- **The Fubini–Study form has total integral one.** Over the Riemann sphere with the canonical
orientation of its complex structure, reindexed from `Fin (2 * finrank ℂ ℂ)` to `Fin 2`, the
Fubini–Study form `ω_FS` integrates to `1`. -/
theorem integralTopForm_fubiniStudyForm :
    integralTopForm ((complexManifoldOrientation ℂ (OnePoint ℂ)).reindex
      (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)))
      fubiniStudyForm.val = 1 := by
  have hc : IsCompact (_root_.tsupport (α := ℂ [⋀^Fin 2]→L[ℝ] ℝ) fubiniStudyForm.val) :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  rw [integralTopForm_eq_integral_apply_coe
    (fubiniStudyForm.isSmoothForm.integrableTopForm hc Complex.basisOneI)]
  -- On the basis `(1, i)` the form is the Fubini–Study density.
  refine (integral_congr_ae (ae_of_all _ fun z ↦ ?_)).trans integral_fubiniStudyDensity
  have h := fubiniStudyForm_coe_basisOneI z
  rw [Complex.coe_basisOneI] at h
  exact h

/-- **The Fubini–Study form has total area one.** The measure `|ω_FS|` of the Fubini–Study form
gives the Riemann sphere measure `1`: in the affine chart it is Lebesgue measure with density
`ρ(z) = 1 / (π (1 + |z|²)²)`, which integrates to one (`OnePoint.integral_fubiniStudyDensity`),
and the remaining point `∞` is null. -/
@[simp]
theorem measure_fubiniStudyForm_univ {m : MeasurableSpace (OnePoint ℂ)}
    [BorelSpace (OnePoint ℂ)] :
    RoughForm.measure fubiniStudyForm.val (univ : Set (OnePoint ℂ)) = 1 := by
  -- On the basis `(1, i)`, the pullback of `ω_FS` along `ℂ → OnePoint ℂ` is the density `ρ`.
  have hρ (z : ℂ) : mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : ℂ → OnePoint ℂ) fubiniStudyForm.val z
      Complex.basisOneI = fubiniStudyDensity z := by
    refine (mpullback_apply _ _ z _).trans ?_
    rw [(hasMFDerivAt_coe z).mfderiv]
    exact (congrArg _ (funext fun i ↦ ContinuousLinearMap.id_apply (R₁ := ℝ) _)).trans
      (fubiniStudyForm_coe_basisOneI z)
  have hint : Integrable fubiniStudyDensity :=
    Integrable.of_integral_ne_zero (by rw [integral_fubiniStudyDensity]; exact one_ne_zero)
  have hf : MeasurableEmbedding ((↑) : ℂ → OnePoint ℂ) := isOpenEmbedding_coe.measurableEmbedding
  -- The point `∞` is null, and on the rest of the sphere `|ω_FS|` is transported from `ℂ`, where
  -- it is the density `ρ` against Lebesgue measure.
  rw [← measure_of_measure_compl_eq_zero (s := range ((↑) : ℂ → OnePoint ℂ)) (by simp),
    ← Measure.restrict_apply_univ,
    ← hf.map_measure_mpullback (fun z ↦ (hasMFDerivAt_coe z).mdifferentiableAt), hf.map_apply,
    preimage_univ, RoughForm.measure_eq_withDensity_addHaar _ Complex.basisOneI,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Complex.addHaar_basisOneI]
  simp_rw [hρ, abs_of_pos (fubiniStudyDensity_pos _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun z ↦ (fubiniStudyDensity_pos z).le),
    integral_fubiniStudyDensity, ENNReal.ofReal_one]

end OnePoint
