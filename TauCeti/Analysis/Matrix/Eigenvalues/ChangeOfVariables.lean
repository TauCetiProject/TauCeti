/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.Diagonalization
public import TauCeti.Analysis.Matrix.Eigenvalues.SpectralCoordinates
public import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Local spectral change of variables

Every self-adjoint matrix with simple spectrum has an open neighborhood parametrized by
a real diagonal and transverse unitary angles. The matrix volume in such a chart is
the product of the Vandermonde factor in the diagonal, with exponent `1` for real
symmetric matrices and `2` for complex Hermitian matrices, and the angular Jacobian.

This is the local change of variables used in Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2 and §4.1.
-/

public section

noncomputable section

open MeasureTheory
open TauCeti (StrictUpperFin)
open scoped ENNReal TauCeti.SelfAdjointMatrix

namespace Matrix

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- Conjugate the real diagonal of the first component by the fixed frame and the
transverse unitary exponential of the second component. -/
def spectralMatrix (U : unitaryGroup (Fin n) 𝕜) (x : SelfAdjointCoordinates n 𝕜) :
    selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜) :=
  selfAdjointCoordinates.symm (unitaryConjCoordinates U (spectralCoordinates x))

/-- Ambient matrix formula for spectral coordinates in a fixed unitary frame. -/
theorem coe_spectralMatrix (U : unitaryGroup (Fin n) 𝕜) (x : SelfAdjointCoordinates n 𝕜) :
    (spectralMatrix U x : Matrix (Fin n) (Fin n) 𝕜) =
      Unitary.conjStarAlgAut ℝ _ (U * expStrictUpper x.2) (diagonal fun i ↦ (x.1 i : 𝕜)) := by
  let D := diagonal fun i : Fin n ↦ (x.1 i : 𝕜)
  have hD : IsSelfAdjoint D :=
    (isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)).isSelfAdjoint
  let B : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜) :=
    ⟨Unitary.conjStarAlgAut ℝ _ (expStrictUpper x.2) D, hD.conjugate (expStrictUpper x.2)⟩
  have hB : spectralCoordinates x = selfAdjointCoordinatesLinearMap B.val := by
    rw [spectralCoordinates_apply]
    rfl
  have hC : selfAdjointCoordinates ((UnitaryGroup.selfAdjointConj U) B) =
      selfAdjointCoordinatesLinearMap (Unitary.conjStarAlgAut ℝ _ U B.val) := by
    rw [selfAdjointCoordinates_apply, UnitaryGroup.coe_selfAdjointConj_apply]
    rfl
  rw [spectralMatrix, hB, unitaryConjCoordinates_read, ← hC,
    ContinuousLinearEquiv.symm_apply_apply, UnitaryGroup.coe_selfAdjointConj_apply]
  exact (Unitary.conjStarAlgAut_mul_apply U (expStrictUpper x.2) D).symm

/-- In the decreasing chamber the diagonal coordinate is the ordered eigenvalue vector. -/
theorem eigenvalues₀_spectralMatrix (U : unitaryGroup (Fin n) 𝕜) (x : SelfAdjointCoordinates n 𝕜)
    (hd : Antitone x.1) :
    (selfAdjoint.isHermitian_coe (spectralMatrix U x)).eigenvalues₀ =
      x.1 ∘ Fin.cast (Fintype.card_fin n) := by
  let hA := selfAdjoint.isHermitian_coe (spectralMatrix U x)
  have hB : (Unitary.conjStarAlgAut ℝ _ (U * expStrictUpper x.2)
      (diagonal fun i ↦ (x.1 i : 𝕜))).IsHermitian := coe_spectralMatrix U x ▸ hA
  rw [← List.ofFn_inj, ← hA.sort_roots_charpoly_eq_eigenvalues₀, coe_spectralMatrix,
    hB.sort_roots_charpoly_eq_eigenvalues₀,
    eigenvalues₀_conjStarAlgAut_diagonal (U * expStrictUpper x.2) hd hB]

/-- Every simple self-adjoint matrix is the center of a local spectral chart. -/
theorem exists_spectralMatrix_openPartialHomeomorph
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))
    (hs : Function.Injective (selfAdjoint.isHermitian_coe A).eigenvalues) :
    ∃ (U : unitaryGroup (Fin n) 𝕜) (d : Fin n → ℝ)
      (e : OpenPartialHomeomorph (SelfAdjointCoordinates n 𝕜)
        (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))),
      (e : _ → _) = spectralMatrix U ∧ (d, 0) ∈ e.source ∧ e (d, 0) = A := by
  let hA := selfAdjoint.isHermitian_coe A
  obtain ⟨e, he, hsource⟩ := exists_spectralCoordinates_openPartialHomeomorph hA.eigenvalues hs
    hA.eigenvectorUnitary
  let e' := e.transHomeomorph selfAdjointCoordinates.symm.toHomeomorph
  have he' : (e' : _ → _) = spectralMatrix hA.eigenvectorUnitary := by
    funext x
    exact congrArg selfAdjointCoordinates.symm (congrFun he x)
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, e', he', hsource, ?_⟩
  apply Subtype.ext
  rw [he', coe_spectralMatrix, expStrictUpper_zero, mul_one]
  exact hA.spectral_theorem.symm

section Measure

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- On an injective coordinate patch the spectral change of variables multiplies
additive Haar measure by the angular Jacobian and the Vandermonde factor. -/
theorem lintegral_image_spectralCoordinates (μ : Measure (SelfAdjointCoordinates n 𝕜))
    [μ.IsAddHaarMeasure] (U : unitaryGroup (Fin n) 𝕜) {s : Set (SelfAdjointCoordinates n 𝕜)}
    (hs : MeasurableSet s) (h : Set.InjOn spectralCoordinates s)
    (g : SelfAdjointCoordinates n 𝕜 → ℝ≥0∞) :
    (∫⁻ y in (unitaryConjCoordinates U ∘ spectralCoordinates) '' s, g y ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal (|(spectralAngularFDeriv x.2).det| *
        ∏ ij : StrictUpperFin n, |x.1 ij.val.2 - x.1 ij.val.1| ^ Module.finrank ℝ 𝕜) *
        g (unitaryConjCoordinates U (spectralCoordinates x)) ∂μ := by
  let T := (unitaryConjCoordinates U).toContinuousLinearMap
  have hF (x : SelfAdjointCoordinates n 𝕜) :=
    T.hasFDerivAt.comp x (hasFDerivAt_spectralCoordinates x).differentiableAt.hasFDerivAt
  have hjac (x : SelfAdjointCoordinates n 𝕜) :
      |(T.comp (fderiv ℝ spectralCoordinates x)).det| = |(fderiv ℝ spectralCoordinates x).det| := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      abs_mul, abs_det_unitaryConjCoordinates, one_mul]
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs
    (fun x _ ↦ (hF x).hasFDerivWithinAt) ((unitaryConjCoordinates U).injective.comp_injOn h) g
  simp only [hjac, abs_det_fderiv_spectralCoordinates, Function.comp_apply] at he
  exact he

/-- Frobenius volume transforms by the spectral Jacobian on every injective patch.
The source measure is Frobenius volume transported to the linear matrix coordinates. -/
theorem lintegral_image_spectralMatrix (U : unitaryGroup (Fin n) 𝕜)
    {s : Set (SelfAdjointCoordinates n 𝕜)} (hs : MeasurableSet s)
    (h : Set.InjOn (spectralMatrix U) s)
    (g : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜) → ℝ≥0∞) :
    (∫⁻ A in spectralMatrix U '' s, g A) =
      ∫⁻ x in s, ENNReal.ofReal (|(spectralAngularFDeriv x.2).det| *
        ∏ ij : StrictUpperFin n, |x.1 ij.val.2 - x.1 ij.val.1| ^ Module.finrank ℝ 𝕜) *
        g (spectralMatrix U x) ∂(volume.map selfAdjointCoordinates) := by
  let c := selfAdjointCoordinates (n := n) (𝕜 := 𝕜)
  let e := c.toHomeomorph.toMeasurableEquiv
  let μ : Measure (SelfAdjointCoordinates n 𝕜) := volume.map c
  let : μ.IsAddHaarMeasure := c.isAddHaarMeasure_map volume
  let F := unitaryConjCoordinates U ∘ spectralCoordinates
  have hF : F = e ∘ spectralMatrix U := by
    funext x
    exact (selfAdjointCoordinates.apply_symm_apply (F x)).symm
  have hp : e ⁻¹' (F '' s) = spectralMatrix U '' s := by
    rw [hF, Set.image_comp, e.injective.preimage_image]
  have hinj : Set.InjOn spectralCoordinates s := fun x hx y hy hxy ↦ h hx hy
    (congrArg (selfAdjointCoordinates.symm ∘ unitaryConjCoordinates U) hxy)
  have hchange := lintegral_image_spectralCoordinates μ U hs hinj (g ∘ e.symm)
  have hrestrict : μ.restrict (F '' s) = (volume.restrict (spectralMatrix U '' s)).map e := by
    rw [← hp]
    exact e.restrict_map volume (F '' s)
  rw [hrestrict, lintegral_map_equiv (g ∘ e.symm) e] at hchange
  simpa [Function.comp_def, e, μ, c, spectralMatrix] using hchange

end Measure

end Matrix
