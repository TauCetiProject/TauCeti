/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The canonical planar area coefficient

The existing complex orientation supplies its normalized volume form. Its continuous alternating
map and tangent-fiber transport give an actual rough manifold top form. The coefficient in the
positive basis `(1,I)` is one, and this basis's normalized Haar measure is the existing complex
volume. Thus the actual coordinate top-form integral is ordinary planar area, with no new area
or orientation carrier.
-/

public section

noncomputable section

open MeasureTheory
open scoped Manifold

namespace TauCeti.Green

attribute [local instance] Complex.finrank_real_complex_fact

/-- The normalized volume coefficient in the actual positive complex basis is one. -/
@[simp]
theorem complexAreaForm_one_I : Complex.orientation.volumeForm ![1, Complex.I] = 1 := by
  rw [← Complex.coe_basisOneI]
  rw [Complex.orientation.volumeForm_robust Complex.orthonormalBasisOneI rfl]
  exact Complex.orthonormalBasisOneI.toBasis.det_self

/-- The canonical complex volume form transported to the actual tangent fibers. -/
def manifoldAreaForm : RoughForm 𝓘(ℝ, ℂ) ℂ ℝ 2 := fun z ↦
  Complex.orientation.volumeFormL.compContinuousLinearMap
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).toContinuousLinearMap

/-- Evaluation of the area form uses the actual canonical tangent-space identification. -/
theorem manifoldAreaForm_apply (z : ℂ) (v : Fin 2 → TangentSpace 𝓘(ℝ, ℂ) z) :
    manifoldAreaForm z v = Complex.orientation.volumeFormL
      (fun i ↦ NormedSpace.fromTangentSpace (𝕜 := ℝ) z (v i)) := (rfl)

/-- The area form's coordinate expression is the existing constant normalized volume form. -/
-- Normalize before the generic model-space chart rule erases the chart expression.
@[simp↓]
theorem manifoldAreaForm_inChartAt (c : ℂ) :
    manifoldAreaForm.inChartAt c = fun _ ↦ Complex.orientation.volumeFormL := by
  rw [RoughForm.inChartAt_modelSpace]
  rfl

/-- The basis normalization agrees with existing planar Lebesgue area. -/
theorem basisOneI_addHaar : Complex.basisOneI.addHaar = (volume : Measure ℂ) := by
  rw [← Complex.toBasis_orthonormalBasisOneI]
  exact Complex.orthonormalBasisOneI.addHaar_eq_volume

/-- The actual top-form coefficient of a scalar multiple of planar area is that scalar. -/
-- Normalize before chart and basis simplification erase this scalar-coefficient pattern.
@[simp↓]
theorem inChartAt_fun_smul_manifoldAreaForm (f : ℂ → ℝ) (c z : ℂ) :
    RoughForm.inChartAt (I := 𝓘(ℝ, ℂ)) (fun x ↦ f x • manifoldAreaForm x)
      c z Complex.basisOneI = f z := by
  have he : RoughForm.inChartAt (I := 𝓘(ℝ, ℂ)) (fun x ↦ f x • manifoldAreaForm x) c =
      fun x ↦ f x • Complex.orientation.volumeFormL := by
    rw [RoughForm.inChartAt_modelSpace]
    rfl
  rw [he, ContinuousAlternatingMap.smul_apply, smul_eq_mul, Complex.coe_basisOneI,
    Orientation.volumeFormL_apply, complexAreaForm_one_I, mul_one]

/-- The actual normalized coordinate top-form integral agrees with ordinary planar area. -/
theorem integral_manifoldAreaForm_coefficient (f : ℂ → ℝ) (c : ℂ) :
    (∫ z, RoughForm.inChartAt (I := 𝓘(ℝ, ℂ)) (fun x ↦ f x • manifoldAreaForm x)
      c z Complex.basisOneI ∂Complex.basisOneI.addHaar) = ∫ z, f z := by
  simp_rw [inChartAt_fun_smul_manifoldAreaForm]
  rw [basisOneI_addHaar]

end TauCeti.Green
