/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Matrix.Eigenvalues.Schur.Jacobian
public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.MeasureTheory.Function.Jacobian

/-!
# Local Schur change of variables for complex matrices

On an injective Schur coordinate patch, the density of matrix-entry Lebesgue measure is the
product of the squared Vandermonde of the diagonal and the angular Jacobian. Splitting the
matrix-entry coordinates into upper and strict lower entries preserves their product volume.

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

/-- Assembling a complex matrix from its upper and strict lower coordinates preserves
product Lebesgue measure. -/
theorem measurePreserving_schurMatrixEquiv :
    MeasurePreserving (schurMatrixEquiv (n := n)) volume volume := by
  let e := (schurMatrixEquiv (n := n)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  apply MeasurePreserving.symm e.symm
  let p (ij : Fin n × Fin n) := ij.1 ≤ ij.2
  let swap : FinStrictUpper n ≃ {ij // ¬p ij} :=
    (Equiv.prodComm _ _).subtypeEquiv fun _ ↦ not_le.symm
  have hread := (Matrix.volume_preserving_ofMeasurableEquiv (Fin n) (Fin n) ℂ).symm
    (Matrix.ofMeasurableEquiv (Fin n) (Fin n) ℂ)
  have hflat := (measurePreserving_curry
    (fun _ _ : Fin n ↦ (volume : Measure ℂ))).symm (MeasurableEquiv.curry (Fin n) (Fin n) ℂ)
  have hsplit := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n × Fin n ↦ ℂ) p
  have hswap := (volume_measurePreserving_piCongrLeft (fun _ : {ij // ¬p ij} ↦ ℂ) swap).symm
    (MeasurableEquiv.piCongrLeft _ swap)
  have h := ((MeasurePreserving.id (volume : Measure ({ij // p ij} → ℂ))).prod hswap).comp
    (hsplit.comp (hflat.comp hread))
  refine h.congr e.symm.measurable (.of_forall fun A ↦ ?_)
  have he (A : Matrix (Fin n) (Fin n) ℂ) : e.symm A = schurMatrixEquiv.symm A := (rfl)
  rw [he]
  apply Prod.ext <;> funext ij
  · simp only [Function.comp_apply, Prod.map_fst, id_eq, Matrix.schurMatrixEquiv_symm_fst,
      MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.coe_mk,
      Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, MeasurableEquiv.coe_curry_symm,
      Matrix.ofMeasurableEquiv_symm_apply]
    rfl
  · simp only [Function.comp_apply, Prod.map_snd, Matrix.schurMatrixEquiv_symm_snd,
      MeasurableEquiv.piCongrLeft, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
      Equiv.piCongrLeft_symm_apply, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, MeasurableEquiv.coe_curry_symm,
      Matrix.ofMeasurableEquiv_symm_apply]
    rfl

open Matrix.UnitaryGroup

/-- On an injective null-measurable patch, Schur coordinates transform the lower integral
against matrix-entry Lebesgue measure by the angular Jacobian and the squared Vandermonde. -/
theorem _root_.Matrix.UnitaryGroup.lintegral_image_schurMatrix (U : Matrix.unitaryGroup (Fin n) ℂ)
    {s : Set (SchurCoordinates n)} (hs : NullMeasurableSet s volume)
    (hinj : Set.InjOn (schurCoordinates U) s) (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) :
    (∫⁻ A in schurMatrix U '' s, g A) =
      ∫⁻ x in s, ENNReal.ofReal (|(spectralAngularFDeriv (fun ij ↦ -star (x.2 ij))).det| *
        ∏ ij : FinStrictUpper n, ‖x.1 ⟨(ij.val.1, ij.val.1), le_rfl⟩ -
          x.1 ⟨(ij.val.2, ij.val.2), le_rfl⟩‖ ^ 2) *
        g (schurMatrix U x) := by
  let e := (schurMatrixEquiv (n := n)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e volume volume := measurePreserving_schurMatrixEquiv
  have hrestrict := e.restrict_map volume (schurMatrix U '' s)
  have hparam : schurMatrix U = e ∘ schurCoordinates U := by
    funext x
    apply e.symm.injective
    rw [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
    exact schurMatrixEquiv_symm_schurMatrix U x
  have hpre : e ⁻¹' (schurMatrix U '' s) = schurCoordinates U '' s := by
    rw [hparam, Set.image_comp, e.injective.preimage_image]
  rw [he.map_eq, hpre] at hrestrict
  rw [hrestrict, lintegral_map_equiv g e]
  have hd (x : SchurCoordinates n) :=
    ((contDiff_schurCoordinates U (k := 1)).differentiable one_ne_zero x).hasFDerivAt
  let : (volume : Measure (SchurCoordinates n)).IsAddHaarMeasure := by
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
  rw [det_fderiv_schurCoordinates, abs_mul, abs_of_nonneg hnonneg, hparam]
  rfl

end TauCeti
