/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Matrix.Eigenvalues.Schur.Jacobian
public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# Local Schur change of variables for complex matrices

On an injective Schur coordinate patch, the density of matrix-entry Lebesgue measure is the
product of the squared Vandermonde of the diagonal and the absolute angular determinant.
The transport from coordinate integrals to matrix integrals adapts
`lintegral_image_spectralCoordinates` and `lintegral_image_spectralMatrix` from
`TauCeti.MeasureTheory.Measure.SelfAdjointMatrix.ChangeOfVariables`.

## References

* J. B. Hough, M. Krishnapur, Y. Peres and B. Virág,
  *Zeros of Gaussian Analytic Functions and Determinantal Point Processes*, §6.3.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {n : ℕ}

open Matrix.UnitaryGroup

/-- On an injective null-measurable patch, Schur coordinates transform the lower integral
against matrix-entry Lebesgue measure by the absolute angular determinant times the
squared Vandermonde. -/
theorem _root_.Matrix.UnitaryGroup.lintegral_image_schurMatrix (U : Matrix.unitaryGroup (Fin n) ℂ)
    {s : Set (SchurCoordinates n ℂ)} (hs : NullMeasurableSet s volume)
    (hinj : Set.InjOn (schurCoordinates U) s) (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) :
    (∫⁻ A in schurMatrix U '' s, g A) =
      ∫⁻ x in s, ENNReal.ofReal (|(spectralAngularFDeriv (fun ij ↦ -star (x.2 ij))).det| *
        ∏ ij : FinStrictUpper n, ‖x.1 ⟨(ij.val.1, ij.val.1), le_rfl⟩ -
          x.1 ⟨(ij.val.2, ij.val.2), le_rfl⟩‖ ^ 2) *
        g (schurMatrix U x) := by
  let e := schurMatrixMeasurableEquiv (n := n) (R := ℂ)
  have he : MeasurePreserving e volume volume := measurePreserving_schurMatrixMeasurableEquiv
  have hparam : schurMatrix U = e ∘ schurCoordinates U := by
    funext x
    rw [Function.comp_apply, show e (schurCoordinates U x) =
      schurMatrixEquiv (schurCoordinates U x) from schurMatrixMeasurableEquiv_apply _,
      ← schurMatrixEquiv_symm_schurMatrix U x, LinearEquiv.apply_symm_apply]
  calc
    _ = ∫⁻ y in schurCoordinates U '' s, g (e y) := by
      rw [hparam, Set.image_comp]
      exact (he.setLIntegral_comp_emb e.measurableEmbedding g _).symm
    _ = _ := by
      have hd (x : SchurCoordinates n ℂ) :=
        ((contDiff_schurCoordinates U (k := 1)).differentiable one_ne_zero x).hasFDerivAt
      let : (volume : Measure (SchurCoordinates n ℂ)).IsAddHaarMeasure := by
        rw [Measure.volume_eq_prod]
        apply Measure.prod.instIsAddHaarMeasure
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul₀ volume hs
        (fun x _ ↦ (hd x).hasFDerivWithinAt) hinj]
      apply setLIntegral_congr_fun₀ hs
      intro x _
      dsimp only
      have hnonneg : 0 ≤ ∏ ij : FinStrictUpper n, ‖x.1 ⟨(ij.val.1, ij.val.1), le_rfl⟩ -
          x.1 ⟨(ij.val.2, ij.val.2), le_rfl⟩‖ ^ 2 :=
        Finset.prod_nonneg fun _ _ ↦ sq_nonneg _
      rw [det_fderiv_schurCoordinates, abs_mul, abs_of_nonneg hnonneg, hparam, Function.comp_apply]

end TauCeti
