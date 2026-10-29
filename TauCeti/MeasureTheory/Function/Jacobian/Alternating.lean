/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Signed change of variables for alternating-form coefficients

The Jacobian theorem transports top-degree coefficients and their integrability under
injective differentiable coordinate changes. Source and target signs account for both
orientations through their compatibility with the signed determinant.
-/

public section

noncomputable section

open MeasureTheory Set

namespace MeasureTheory

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Finite ι]
  {μ : Measure E} [μ.IsAddHaarMeasure] {T : E → E} {T' : E → E →L[ℝ] E} {s : Set E}

/-- The actual coefficient integral is compatible with chart signs, allowing reversing
coordinate changes. The signs need only agree with the signed Jacobian on the overlap. -/
theorem integral_image_signed_apply_basis_eq_integral_pullback
    (b : Module.Basis ι ℝ E) (hs : MeasurableSet s)
    (hT : ∀ x ∈ s, HasFDerivWithinAt T (T' x) s x) (hinj : InjOn T s)
    (σsource σtarget : E → ℤˣ)
    (hσ : ∀ x ∈ s, (σsource x : ℝ) * (T' x).toLinearMap.det =
      |(T' x).toLinearMap.det| * (σtarget (T x) : ℝ))
    (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    (∫ y in T '' s, (σtarget y : ℝ) * ω y b ∂μ) =
      ∫ x in s, (σsource x : ℝ) * ((ω (T x)).compContinuousLinearMap (T' x)) b ∂μ := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hs hT hinj]
  apply setIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply_basis, smul_eq_mul,
    ← mul_assoc, ← mul_assoc, hσ x hx]

/-- Genuine integrability of signed top-form coefficients transports with the chart signs,
including orientation-reversing changes of coordinates. -/
theorem integrableOn_image_signed_apply_basis_iff_pullback
    (b : Module.Basis ι ℝ E) (hs : MeasurableSet s)
    (hT : ∀ x ∈ s, HasFDerivWithinAt T (T' x) s x) (hinj : InjOn T s)
    (σsource σtarget : E → ℤˣ)
    (hσ : ∀ x ∈ s, (σsource x : ℝ) * (T' x).toLinearMap.det =
      |(T' x).toLinearMap.det| * (σtarget (T x) : ℝ))
    (ω : E → E [⋀^ι]→L[ℝ] ℝ) :
    IntegrableOn (fun y ↦ (σtarget y : ℝ) * ω y b) (T '' s) μ ↔
      IntegrableOn (fun x ↦ (σsource x : ℝ) *
        ((ω (T x)).compContinuousLinearMap (T' x)) b) s μ := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hs hT hinj]
  apply integrableOn_congr_fun _ hs
  intro x hx
  dsimp only
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply_basis, smul_eq_mul,
    ← mul_assoc, ← mul_assoc, hσ x hx]

end MeasureTheory
