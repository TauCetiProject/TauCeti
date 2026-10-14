/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.Analysis.Calculus.FDeriv.Affine

/-!
# Change of variables under continuous affine equivalences

The linear part of an affine equivalence determines its constant Jacobian. Additive Haar
measure and Bochner integrals therefore transform by its absolute real determinant.
-/

public section

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace ContinuousAffineEquiv

private theorem det_toContinuousAffineMap_contLinear {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (A : E ≃ᴬ[ℝ] E) :
    A.toContinuousAffineMap.contLinear.det = A.linear.toLinearMap.det := by
  rw [ContinuousLinearMap.det, ContinuousAffineMap.coe_contLinear_eq_linear,
    toContinuousAffineMap_linear]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Haar measure on an affine image is the pushforward of the determinant density. -/
theorem map_withDensity_abs_det (A : E ≃ᴬ[ℝ] E) (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E}
    (hs : NullMeasurableSet s μ) :
    Measure.map A
      ((μ.restrict s).withDensity
        (fun _ ↦ ENNReal.ofReal |A.linear.toLinearMap.det|)) =
      μ.restrict (A '' s) := by
  simpa only [det_toContinuousAffineMap_contLinear] using
    map_withDensity_abs_det_fderiv_eq_addHaar μ hs
      (f := A) (f' := fun _ ↦ A.toContinuousAffineMap.contLinear)
    (fun _ _ ↦ A.toContinuousAffineMap.hasFDerivWithinAt)
    A.injective.injOn

/-- Change of variables for Haar measure under an affine equivalence. -/
theorem integral_image (A : E ≃ᴬ[ℝ] E) (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E}
    (hs : MeasurableSet s) (f : E → F) :
    (∫ z in A '' s, f z ∂μ) =
      |A.linear.toLinearMap.det| • ∫ z in s, f (A z) ∂μ := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hs
    (f := A) (f' := fun _ ↦ A.toContinuousAffineMap.contLinear)
    (fun _ _ ↦ A.toContinuousAffineMap.hasFDerivWithinAt)
    A.injective.injOn f]
  simp only [integral_smul, det_toContinuousAffineMap_contLinear]

/-- Affine images scale Haar measure by the absolute real determinant. -/
theorem addHaar_image (A : E ≃ᴬ[ℝ] E) (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E}
    (hs : NullMeasurableSet s μ) :
    μ (A '' s) =
      ENNReal.ofReal |A.linear.toLinearMap.det| * μ s := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image₀ μ hs
    (f := A) (f' := fun _ ↦ A.toContinuousAffineMap.contLinear)
    (fun _ _ ↦ A.toContinuousAffineMap.hasFDerivWithinAt)
    A.injective.injOn]
  simp only [lintegral_const, Measure.restrict_apply_univ,
    det_toContinuousAffineMap_contLinear]

/-- Integrability is preserved under an affine equivalence. -/
theorem integrableOn_image_iff (A : E ≃ᴬ[ℝ] E) (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E}
    (hs : MeasurableSet s) (f : E → F) :
    IntegrableOn f (A '' s) μ ↔ IntegrableOn (f ∘ A) s μ := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs
    (f := A) (f' := fun _ ↦ A.toContinuousAffineMap.contLinear)
    (fun _ _ ↦ A.toContinuousAffineMap.hasFDerivWithinAt)
    A.injective.injOn f]
  simp only [det_toContinuousAffineMap_contLinear]
  simpa only [IntegrableOn, Pi.smul_def, Function.comp_def] using
    (integrable_smul_iff (μ := μ.restrict s) (abs_ne_zero.mpr A.linear.isUnit_det'.ne_zero)
      (f ∘ A))

end ContinuousAffineEquiv
