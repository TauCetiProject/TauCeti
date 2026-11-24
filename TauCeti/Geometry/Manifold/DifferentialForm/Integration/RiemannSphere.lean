/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Parametrization
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.Measure

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

## Main results

* `OnePoint.integralTopForm_fubiniStudyForm`: the Fubini–Study form integrates to `1` over the
  Riemann sphere with its complex orientation.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Section 2 (the Fubini–Study metric, normalized so that a line has area one).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 16 (integration of top forms over parametrizations).
-/

public section

noncomputable section

open MeasureTheory Module TauCeti
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

end OnePoint
