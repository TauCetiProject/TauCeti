/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.SpectralCoordinates
public import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix.Basic
public import TauCeti.MeasureTheory.Function.Jacobian
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Local spectral change of variables

Every self-adjoint matrix with simple spectrum has an open neighborhood parametrized by
a real diagonal and transverse unitary angles, the fixed-frame chart
`TauCeti.spectralMatrix`. In such a chart, an additive Haar measure on the matrices, such as
Frobenius volume, has density the product of the Vandermonde factor in the diagonal, with
exponent `1` for real symmetric matrices and `2` for complex Hermitian matrices, and the angular
Jacobian.

This is the local change of variables used in Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2 and §4.1.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal TauCeti.SelfAdjointMatrix

namespace TauCeti

open Matrix

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

section Measure

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- On an injective null-measurable coordinate patch the spectral change of variables
multiplies additive Haar measure by the angular Jacobian and the Vandermonde factor. -/
theorem lintegral_image_spectralCoordinates (μ : Measure (SelfAdjointCoordinates n 𝕜))
    [μ.IsAddHaarMeasure] (U : unitaryGroup (Fin n) 𝕜) {s : Set (SelfAdjointCoordinates n 𝕜)}
    (hs : NullMeasurableSet s μ) (h : Set.InjOn spectralCoordinates s)
    (g : SelfAdjointCoordinates n 𝕜 → ℝ≥0∞) :
    (∫⁻ y in (unitaryConjCoordinates U ∘ spectralCoordinates) '' s, g y ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal (|(spectralAngularFDeriv x.2).det| *
        ∏ ij : FinStrictUpper n, |x.1 ij.val.2 - x.1 ij.val.1| ^ Module.finrank ℝ 𝕜) *
        g (unitaryConjCoordinates U (spectralCoordinates x)) ∂μ := by
  let T := (unitaryConjCoordinates U).toContinuousLinearMap
  have hF (x : SelfAdjointCoordinates n 𝕜) :=
    T.hasFDerivAt.comp x (hasFDerivAt_spectralCoordinates x).differentiableAt.hasFDerivAt
  have hjac (x : SelfAdjointCoordinates n 𝕜) :
      |(T.comp (fderiv ℝ spectralCoordinates x)).det| = |(fderiv ℝ spectralCoordinates x).det| := by
    rw [ContinuousLinearMap.det_comp, abs_mul, abs_det_unitaryConjCoordinates, one_mul]
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul₀ μ hs
    (fun x _ ↦ (hF x).hasFDerivWithinAt) ((unitaryConjCoordinates U).injective.comp_injOn h) g
  simp only [hjac, abs_det_fderiv_spectralCoordinates, Function.comp_apply] at he
  exact he

/-- An additive Haar measure on the self-adjoint matrices, such as Frobenius volume, transforms by
the spectral Jacobian on every injective null-measurable patch. The source measure is the same
measure transported to the linear matrix coordinates. -/
theorem lintegral_image_spectralMatrix
    (ν : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))) [ν.IsAddHaarMeasure]
    (U : unitaryGroup (Fin n) 𝕜) {s : Set (SelfAdjointCoordinates n 𝕜)}
    (hs : NullMeasurableSet s (ν.map selfAdjointCoordinates))
    (h : Set.InjOn (spectralMatrix U) s)
    (g : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜) → ℝ≥0∞) :
    (∫⁻ A in spectralMatrix U '' s, g A ∂ν) =
      ∫⁻ x in s, ENNReal.ofReal (|(spectralAngularFDeriv x.2).det| *
        ∏ ij : FinStrictUpper n, |x.1 ij.val.2 - x.1 ij.val.1| ^ Module.finrank ℝ 𝕜) *
        g (spectralMatrix U x) ∂(ν.map selfAdjointCoordinates) := by
  let c := selfAdjointCoordinates (n := n) (𝕜 := 𝕜)
  let e := c.toHomeomorph.toMeasurableEquiv
  let μ : Measure (SelfAdjointCoordinates n 𝕜) := ν.map c
  let : μ.IsAddHaarMeasure := c.isAddHaarMeasure_map ν
  let F := unitaryConjCoordinates U ∘ spectralCoordinates
  have hF : F = e ∘ spectralMatrix U := by
    rw [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph]
    funext x
    exact (selfAdjointCoordinates_spectralMatrix U x).symm
  have hp : e ⁻¹' (F '' s) = spectralMatrix U '' s := by
    rw [hF, Set.image_comp, e.injective.preimage_image]
  have hinj : Set.InjOn spectralCoordinates s := fun x hx y hy hxy ↦ h hx hy
    (selfAdjointCoordinates.injective (by rw [selfAdjointCoordinates_spectralMatrix,
      selfAdjointCoordinates_spectralMatrix, hxy]))
  have hchange := lintegral_image_spectralCoordinates μ U hs hinj (g ∘ e.symm)
  have hrestrict : μ.restrict (F '' s) = (ν.restrict (spectralMatrix U '' s)).map e := by
    rw [← hp]
    exact e.restrict_map ν (F '' s)
  have hsymm (x : SelfAdjointCoordinates n 𝕜) :
      e.symm (unitaryConjCoordinates U (spectralCoordinates x)) = spectralMatrix U x := by
    have hx : unitaryConjCoordinates U (spectralCoordinates x) = e (spectralMatrix U x) :=
      congrFun hF x
    rw [hx, e.symm_apply_apply]
  rw [hrestrict, lintegral_map_equiv (g ∘ e.symm) e] at hchange
  simp only [Function.comp_apply, e.symm_apply_apply, hsymm] at hchange
  -- The remaining difference is the local abbreviation `μ` for the source measure.
  exact hchange

end Measure

end TauCeti
