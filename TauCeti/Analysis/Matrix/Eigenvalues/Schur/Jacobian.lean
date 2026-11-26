/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import TauCeti.Analysis.Matrix.Exponential.SkewAdjoint
public import TauCeti.LinearAlgebra.Matrix.Triangular.Coordinates
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Analysis.Calculus.FDeriv.Unitary
import TauCeti.LinearAlgebra.Complex.Determinant
import TauCeti.LinearAlgebra.Matrix.Kronecker.MulLeftMulRight
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Prod
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# The Jacobian of Schur coordinates

Local Schur coordinates conjugate an upper triangular matrix by the exponential of a
zero-diagonal skew-adjoint matrix. In the moving frame, the angular differential feeds a
triangular commutator operator on the strict lower entries. Its diagonal consists of the
eigenvalue gaps. The upper triangular directions contribute a determinant of one. The
resulting squared Vandermonde factor enters the local change of variables for Ginibre matrices.

The moving-frame derivative and local chart adapt the self-adjoint construction in
`TauCeti.Analysis.Matrix.Eigenvalues.SpectralCoordinates`.

## References

* J. B. Hough, M. Krishnapur, Y. Peres and B. Virág,
  *Zeros of Gaussian Analytic Functions and Determinantal Point Processes*, §6.3.
-/

public section

noncomputable section

namespace TauCeti

open Matrix
open scoped Matrix

variable {n : ℕ}

section Differentiation

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

private def schurAngleFlip : (FinStrictUpper n → ℂ) →L[ℝ] (FinStrictUpper n → ℂ) :=
  ContinuousLinearMap.pi fun ij ↦ -Complex.conjCLE.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj ij)

@[simp] private theorem schurAngleFlip_apply (b : FinStrictUpper n → ℂ)
    (ij : FinStrictUpper n) : schurAngleFlip b ij = -star (b ij) := (rfl)

private theorem coe_schurAngleFlip (b : FinStrictUpper n → ℂ) :
    schurAngleFlip b = fun ij ↦ -star (b ij) :=
  funext (schurAngleFlip_apply b)

private def schurMatrixCLE :
    SchurCoordinates n ℂ ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (schurMatrixEquiv.restrictScalars ℝ).toContinuousLinearEquiv

private theorem schurMatrixCLE_apply (x : SchurCoordinates n ℂ) :
    schurMatrixCLE x = schurMatrixEquiv x := by
  rw [schurMatrixCLE, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.restrictScalars_apply]

private theorem schurMatrixCLE_symm_apply (A : Matrix (Fin n) (Fin n) ℂ) :
    schurMatrixCLE.symm A = schurMatrixEquiv.symm A := by
  rw [schurMatrixCLE, LinearEquiv.coe_toContinuousLinearEquiv_symm',
    LinearEquiv.restrictScalars_symm_apply]

private def schurUpper :
    ({ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  schurMatrixCLE.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)

private theorem schurUpper_apply (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :
    schurUpper a = schurMatrixEquiv (a, 0) := by
  rw [schurUpper, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.inl_apply, schurMatrixCLE_apply]

private def schurFrame (b : FinStrictUpper n → ℂ) : unitaryGroup (Fin n) ℂ :=
  expStrictUpper (schurAngleFlip b)

/-- The input gives the upper triangular entries and the strict lower angular coordinates.
Negatively conjugate the angles for `expStrictUpper`, apply the resulting unitary in the fixed
frame, and split the resulting matrix into its upper triangular and strict lower entries. -/
def _root_.Matrix.UnitaryGroup.schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n ℂ) : SchurCoordinates n ℂ :=
  schurMatrixEquiv.symm
    (Unitary.conjStarAlgAut ℂ _ (U * schurFrame x.2) (schurMatrixEquiv (x.1, 0)))

open Matrix.UnitaryGroup

/-- The Schur parametrization assembles the upper triangular input and conjugates it
by the unitary exponential in the fixed frame. -/
theorem _root_.Matrix.UnitaryGroup.schurCoordinates_apply (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n ℂ) :
    schurCoordinates U x = schurMatrixEquiv.symm
      (Unitary.conjStarAlgAut ℂ _ (U * expStrictUpper (fun ij ↦ -star (x.2 ij)))
        (schurMatrixEquiv (x.1, 0))) := by
  rw [schurCoordinates, schurFrame, coe_schurAngleFlip]

/-- Zero angles give the unitary conjugate of the upper triangular input by the fixed frame. -/
@[simp] theorem _root_.Matrix.UnitaryGroup.schurCoordinates_zero (U : unitaryGroup (Fin n) ℂ)
    (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :
    schurCoordinates U (a, 0) = schurMatrixEquiv.symm
      (Unitary.conjStarAlgAut ℂ _ U (schurMatrixEquiv (a, 0))) := by
  rw [schurCoordinates]
  simp [schurFrame]

/-- The complex matrix parametrized by the upper triangular entries and the angles in a
fixed unitary frame. -/
def _root_.Matrix.UnitaryGroup.schurMatrix (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  schurMatrixEquiv (schurCoordinates U x)

/-- Reading the entries of the parametrized matrix gives the Schur coordinate map. -/
@[simp] theorem _root_.Matrix.UnitaryGroup.schurMatrixEquiv_symm_schurMatrix
    (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n ℂ) : schurMatrixEquiv.symm (schurMatrix U x) = schurCoordinates U x :=
  schurMatrixEquiv.symm_apply_apply _

/-- The matrix parametrization conjugates the triangular input by the fixed frame followed by
the transverse unitary exponential. -/
theorem _root_.Matrix.UnitaryGroup.schurMatrix_apply (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n ℂ) :
    schurMatrix U x = Unitary.conjStarAlgAut ℂ _
      (U * expStrictUpper (fun ij ↦ -star (x.2 ij))) (schurMatrixEquiv (x.1, 0)) := by
  rw [schurMatrix, schurCoordinates_apply, LinearEquiv.apply_symm_apply]

/-- At zero angles the matrix parametrization conjugates the upper triangular matrix by the
fixed frame. -/
@[simp] theorem _root_.Matrix.UnitaryGroup.schurMatrix_zero (U : unitaryGroup (Fin n) ℂ)
    (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :
    schurMatrix U (a, 0) = Unitary.conjStarAlgAut ℂ _ U (schurMatrixEquiv (a, 0)) := by
  rw [schurMatrix, schurCoordinates_zero, LinearEquiv.apply_symm_apply]

/-- The characteristic polynomial of the Schur matrix has the diagonal input entries as roots,
with multiplicities. -/
theorem _root_.Matrix.UnitaryGroup.charpoly_schurMatrix (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n ℂ) :
    (schurMatrix U x).charpoly =
      ∏ i : Fin n, (Polynomial.X - Polynomial.C (x.1 ⟨(i, i), le_rfl⟩)) := by
  let V := U * expStrictUpper (fun ij ↦ -star (x.2 ij))
  have hconj (T : Matrix (Fin n) (Fin n) ℂ) :
      (Unitary.conjStarAlgAut ℂ _ V T).charpoly = T.charpoly := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] using
      (charpoly_unitary_conj T (star V))
  rw [schurMatrix_apply, hconj, charpoly_of_isUpperTriangular _
    ((isUpperTriangular_schurMatrixEquiv_iff (x.1, 0)).2 rfl)]
  simp only [schurMatrixEquiv_apply_of_le _ le_rfl]

private def schurConj (U : unitaryGroup (Fin n) ℂ) :
    SchurCoordinates n ℂ ≃L[ℝ] SchurCoordinates n ℂ :=
  let C := (Unitary.conjStarAlgAut ℂ _ U).toAlgEquiv.toLinearEquiv.restrictScalars ℝ
  schurMatrixCLE.trans (C.toContinuousLinearEquiv.trans schurMatrixCLE.symm)

private theorem schurConj_apply (U : unitaryGroup (Fin n) ℂ) (x : SchurCoordinates n ℂ) :
    schurConj U x = schurMatrixEquiv.symm
      (Unitary.conjStarAlgAut ℂ _ U (schurMatrixEquiv x)) := by
  rw [schurConj, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
    LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.restrictScalars_apply,
    AlgEquiv.toLinearEquiv_apply, StarAlgEquiv.coe_toAlgEquiv, schurMatrixCLE_apply,
    schurMatrixCLE_symm_apply]

private theorem det_schurConj (U : unitaryGroup (Fin n) ℂ) :
    (schurConj U).toContinuousLinearMap.det = 1 := by
  let C := (Unitary.conjStarAlgAut ℂ _ U).toAlgEquiv.toLinearMap
  have hC : C = (LinearMap.mulLeft ℂ (U : Matrix (Fin n) (Fin n) ℂ)).comp
      (LinearMap.mulRight ℂ (star (U : Matrix (Fin n) (Fin n) ℂ))) := by
    apply LinearMap.ext
    intro M
    simp [C, mul_assoc]
  have hdet : C.det = 1 := by
    rw [hC, Matrix.det_mulLeft_comp_mulRight_of_mul_eq_one _ _
      (Unitary.mul_star_self_of_mem U.property)]
  have hconj : (schurConj U).toContinuousLinearMap.toLinearMap =
      schurMatrixCLE.symm.toLinearEquiv.conj (C.restrictScalars ℝ) := by
    apply LinearMap.ext
    intro x
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe, schurConj_apply,
      LinearEquiv.conj_apply_apply, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.symm_symm,
      LinearMap.coe_restrictScalars, schurMatrixCLE_apply, schurMatrixCLE_symm_apply, C,
      AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv]
  rw [ContinuousLinearMap.det, hconj, LinearEquiv.conj_apply, LinearMap.comp_assoc,
    LinearMap.det_conj, LinearMap.det_restrictScalars_eq_normSq, hdet, Complex.normSq_one]

/-- Schur coordinates depend smoothly on both the triangular entries and the angles. -/
theorem _root_.Matrix.UnitaryGroup.contDiff_schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    {k : WithTop ℕ∞} :
    ContDiff ℝ k (schurCoordinates U) := by
  have hD := schurUpper.contDiff.comp
    (contDiff_fst : ContDiff ℝ k (Prod.fst : SchurCoordinates n ℂ → _))
  have h := contDiff_conjStarAlgAut_expStrictUpper U hD
    (schurAngleFlip.contDiff.comp contDiff_snd)
  convert schurMatrixCLE.symm.toContinuousLinearMap.contDiff.comp h using 1
  funext x
  simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, schurCoordinates, schurFrame,
    schurMatrixCLE_symm_apply, schurUpper_apply, Unitary.conjStarAlgAut_apply]

private def schurFDeriv (T : Matrix (Fin n) (Fin n) ℂ)
    (K : (FinStrictUpper n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    SchurCoordinates n ℂ →L[ℝ] SchurCoordinates n ℂ :=
  let C := (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip T -
    ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ) T
  schurMatrixCLE.symm.toContinuousLinearMap.comp
    ((schurUpper.comp (ContinuousLinearMap.fst ℝ _ _)) +
      C.comp (K.comp (ContinuousLinearMap.snd ℝ _ _)))

private theorem schurFDeriv_apply (T : Matrix (Fin n) (Fin n) ℂ)
    (K : (FinStrictUpper n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (v : SchurCoordinates n ℂ) :
    schurFDeriv T K v =
      schurMatrixEquiv.symm (schurMatrixEquiv (v.1, 0) + (K v.2 * T - T * K v.2)) := by
  simp only [schurFDeriv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    schurMatrixCLE_symm_apply, add_apply, sub_apply, schurUpper_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply']

private theorem det_schurFDeriv {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.IsUpperTriangular)
    (K : (FinStrictUpper n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (L : (FinStrictUpper n → ℂ) →L[ℝ] (FinStrictUpper n → ℂ))
    (hK : ∀ v, (schurMatrixEquiv.symm (K v)).2 = L v) :
    (schurFDeriv T K).det = L.det *
      ∏ ij : FinStrictUpper n, ‖T ij.val.1 ij.val.1 - T ij.val.2 ij.val.2‖ ^ 2 := by
  classical
  let D := (schurLowerCommutator T).restrictScalars ℝ
  have hsnd (v : SchurCoordinates n ℂ) : (schurFDeriv T K v).2 = D (L v.2) := by
    funext ij
    rw [schurFDeriv_apply, schurMatrixEquiv_symm_snd, Matrix.add_apply,
      schurMatrixEquiv_apply_of_gt _ ij.property]
    simp only [Pi.zero_apply, zero_add, D, LinearMap.coe_restrictScalars]
    rw [← hT.schurLowerCommutator_eq, hK]
  let e := LinearEquiv.prodComm ℝ ({ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) (FinStrictUpper n → ℂ)
  let g := e.conj (schurFDeriv T K).toLinearMap
  have hfst (v) : (g v).1 = D (L v.1) := by
    simpa only [g, LinearEquiv.conj_apply_apply, e, LinearEquiv.symm_prodComm,
      LinearEquiv.prodComm_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
      Prod.swap] using hsnd v.swap
  have hzero (a) : (g (0, a)).1 = 0 := by simp [hfst]
  have h₁ : (LinearMap.fst ℝ _ _).comp (g.comp (LinearMap.inl ℝ _ _)) = D.comp L.toLinearMap :=
    LinearMap.ext fun b ↦ hfst (b, 0)
  have h₂ : (LinearMap.snd ℝ _ _).comp (g.comp (LinearMap.inr ℝ _ _)) = LinearMap.id := by
    apply LinearMap.ext
    intro a
    -- After swapping the factors, this block inserts and reads the upper coordinates.
    change (schurFDeriv T K (a, 0)).1 = a
    simp [schurFDeriv_apply]
  have hg : g.det = (schurFDeriv T K).det := by
    dsimp only [g]
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj, ContinuousLinearMap.det]
  rw [← hg, LinearMap.det_eq_det_mul_det_of_fst_apply_inr hzero, h₁, h₂, LinearMap.det_id, mul_one,
    LinearMap.det_comp, mul_comm, ← ContinuousLinearMap.det,
    LinearMap.det_restrictScalars_eq_normSq, hT.det_schurLowerCommutator, map_prod]
  simp only [Complex.normSq_eq_norm_sq]

private def schurRelativeFDeriv (b : FinStrictUpper n → ℂ) :
    (FinStrictUpper n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (fderiv ℝ (fun c ↦ (relativeFrame (schurAngleFlip b) c : Matrix (Fin n) (Fin n) ℂ))
    (schurAngleFlip b)).comp schurAngleFlip

private theorem star_schurRelativeFDeriv (b v : FinStrictUpper n → ℂ) :
    star (schurRelativeFDeriv b v) = -(schurRelativeFDeriv b v) := by
  rw [schurRelativeFDeriv, ContinuousLinearMap.comp_apply, star_fderiv_relativeFrame]

private theorem schurRelativeFDeriv_lower (b v : FinStrictUpper n → ℂ) :
    (schurMatrixEquiv.symm (schurRelativeFDeriv b v)).2 =
      schurAngleFlip (spectralAngularFDeriv (schurAngleFlip b) (schurAngleFlip v)) := by
  funext ij
  have hs := congrFun₂ (star_schurRelativeFDeriv b v) ij.val.2 ij.val.1
  have he : (schurRelativeFDeriv b v) ij.val.2 ij.val.1 =
      -star ((schurRelativeFDeriv b v) ij.val.1 ij.val.2) := by
    simpa only [Matrix.star_apply, Matrix.neg_apply, neg_neg] using (congrArg Neg.neg hs).symm
  rw [schurMatrixEquiv_symm_snd, he, schurAngleFlip_apply, spectralAngularFDeriv_apply,
    schurRelativeFDeriv, ContinuousLinearMap.comp_apply]

private theorem schurAngleFlip_involutive : Function.Involutive (schurAngleFlip (n := n)) := by
  intro b
  funext ij
  simp

private theorem hasFDerivAt_schurCoordinates_relative (x : SchurCoordinates n ℂ) :
    HasFDerivAt
      (fun y : SchurCoordinates n ℂ ↦ schurMatrixEquiv.symm
        (Unitary.conjStarAlgAut ℂ _
          (relativeFrame (schurAngleFlip x.2) (schurAngleFlip y.2)) (schurMatrixEquiv (y.1, 0))))
      (schurFDeriv (schurMatrixEquiv (x.1, 0)) (schurRelativeFDeriv x.2)) x := by
  let F (b : FinStrictUpper n → ℂ) :=
    (relativeFrame (schurAngleFlip x.2) (schurAngleFlip b) : Matrix (Fin n) (Fin n) ℂ)
  have hF : HasFDerivAt F (schurRelativeFDeriv x.2) x.2 :=
    (((contDiff_relativeFrame (schurAngleFlip x.2) (k := 1)).differentiable
      one_ne_zero (schurAngleFlip x.2)).hasFDerivAt).comp x.2 schurAngleFlip.hasFDerivAt
  let P : SchurCoordinates n ℂ →L[ℝ] (FinStrictUpper n → ℂ) := ContinuousLinearMap.snd ℝ _ _
  let Q : SchurCoordinates n ℂ →L[ℝ] ({ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :=
    ContinuousLinearMap.fst ℝ _ _
  have hFF := hF.comp x P.hasFDerivAt
  have hD := schurUpper.hasFDerivAt.comp x Q.hasFDerivAt
  have h := hFF.unitary_conj_of_eq_one hD
    (.of_forall fun y ↦ (relativeFrame (schurAngleFlip x.2) (schurAngleFlip y.2)).property)
    (by simp [F])
  have hf := schurMatrixCLE.symm.toContinuousLinearMap.hasFDerivAt.comp x h
  refine (hf.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)).congr_fderiv ?_
  · simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, schurMatrixCLE_symm_apply,
      schurUpper_apply, Unitary.conjStarAlgAut_apply, F, Q, ContinuousLinearMap.coe_fst']
  · simp only [schurFDeriv, Function.comp_apply, schurUpper_apply, P, Q,
      ContinuousLinearMap.coe_fst']

private theorem hasFDerivAt_schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n ℂ) :
    HasFDerivAt (schurCoordinates U)
      ((schurConj (U * schurFrame x.2)).toContinuousLinearMap.comp
        (schurFDeriv (schurMatrixEquiv (x.1, 0)) (schurRelativeFDeriv x.2))) x := by
  have h := (schurConj (U * schurFrame x.2)).toContinuousLinearMap.hasFDerivAt.comp x
    (hasFDerivAt_schurCoordinates_relative x)
  refine h.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)
  have hu : (U * schurFrame x.2) * relativeFrame (schurAngleFlip x.2) (schurAngleFlip y.2) =
      U * schurFrame y.2 := by
    rw [mul_assoc]
    exact congrArg (U * ·) (expStrictUpper_mul_relativeFrame _ _)
  simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, schurConj_apply,
    LinearEquiv.apply_symm_apply]
  rw [schurCoordinates, ← hu, Unitary.conjStarAlgAut_mul_apply]

/-- The real Jacobian of the Schur parametrization is the angular Jacobian times the
squared Vandermonde of the upper triangular diagonal. -/
theorem _root_.Matrix.UnitaryGroup.det_fderiv_schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n ℂ) :
    (fderiv ℝ (schurCoordinates U) x).det =
      (spectralAngularFDeriv (fun ij ↦ -star (x.2 ij))).det *
        ∏ ij : FinStrictUpper n, ‖x.1 ⟨(ij.val.1, ij.val.1), le_rfl⟩ -
          x.1 ⟨(ij.val.2, ij.val.2), le_rfl⟩‖ ^ 2 := by
  let A := spectralAngularFDeriv (schurAngleFlip x.2)
  let L := schurAngleFlip.comp (A.comp schurAngleFlip)
  have hL : L.det = A.det := by
    simp only [L, ContinuousLinearMap.det_comp]
    calc
      schurAngleFlip.det * (A.det * schurAngleFlip.det) = schurAngleFlip.det ^ 2 * A.det := by ring
      _ = A.det := by
        rw [ContinuousLinearMap.det_sq_eq_one_of_involutive _ schurAngleFlip_involutive, one_mul]
  rw [(hasFDerivAt_schurCoordinates U x).fderiv, ContinuousLinearMap.det_comp, det_schurConj,
    one_mul, det_schurFDeriv ((isUpperTriangular_schurMatrixEquiv_iff (x.1, 0)).2 rfl)
      _ L (schurRelativeFDeriv_lower x.2), hL]
  simp only [A, coe_schurAngleFlip, schurMatrixEquiv_apply_of_le _ le_rfl]

/-- At zero angle the Jacobian in every fixed unitary frame is the squared Vandermonde. -/
@[simp] theorem _root_.Matrix.UnitaryGroup.det_fderiv_schurCoordinates_zero
    (U : unitaryGroup (Fin n) ℂ)
    (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :
    (fderiv ℝ (schurCoordinates U) (a, 0)).det =
      ∏ ij : FinStrictUpper n, ‖a ⟨(ij.val.1, ij.val.1), le_rfl⟩ -
        a ⟨(ij.val.2, ij.val.2), le_rfl⟩‖ ^ 2 := by
  rw [det_fderiv_schurCoordinates]
  have h : (fun ij : FinStrictUpper n ↦ -star ((0 : FinStrictUpper n → ℂ) ij)) = 0 := by
    funext ij
    simp
  simp only [h, spectralAngularFDeriv_zero, ContinuousLinearMap.det_id, one_mul]

/-- At distinct diagonal entries and an invertible angular differential, the Schur
parametrization restricts to a local chart. -/
theorem _root_.Matrix.UnitaryGroup.exists_schurCoordinates_openPartialHomeomorph
    (U : unitaryGroup (Fin n) ℂ) (x : SchurCoordinates n ℂ)
    (ha : Function.Injective fun i ↦ x.1 ⟨(i, i), le_rfl⟩)
    (hb : (spectralAngularFDeriv (fun ij ↦ -star (x.2 ij))).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (SchurCoordinates n ℂ) (SchurCoordinates n ℂ),
      (e : _ → _) = schurCoordinates U ∧ x ∈ e.source := by
  let f := schurCoordinates U
  let D := fderiv ℝ f x
  have hD : D.det ≠ 0 := by
    rw [det_fderiv_schurCoordinates]
    refine mul_ne_zero hb (Finset.prod_ne_zero_iff.mpr fun ij _ ↦ ?_)
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (ha.ne ij.property.ne)))
  have hf := (contDiff_schurCoordinates U (k := 1)).contDiffAt (x := x)
  have hfd : HasFDerivAt f (D.toContinuousLinearEquivOfDetNeZero hD : _ →L[ℝ] _) x := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hf.differentiableAt one_ne_zero).hasFDerivAt
  have hstrict := hf.hasStrictFDerivAt hfd one_ne_zero
  exact ⟨hstrict.toOpenPartialHomeomorph _, hstrict.toOpenPartialHomeomorph_coe,
    hstrict.mem_toOpenPartialHomeomorph_source⟩

/-- Distinct diagonal entries give a local Schur chart centered at zero angle. -/
theorem _root_.Matrix.UnitaryGroup.exists_schurCoordinates_openPartialHomeomorph_zero
    (U : unitaryGroup (Fin n) ℂ) (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ)
    (ha : Function.Injective fun i ↦ a ⟨(i, i), le_rfl⟩) :
    ∃ e : OpenPartialHomeomorph (SchurCoordinates n ℂ) (SchurCoordinates n ℂ),
      (e : _ → _) = schurCoordinates U ∧ (a, 0) ∈ e.source := by
  apply exists_schurCoordinates_openPartialHomeomorph U (a, 0) ha
  have h : schurAngleFlip (0 : FinStrictUpper n → ℂ) = 0 := map_zero _
  rw [← coe_schurAngleFlip, h, spectralAngularFDeriv_zero, ContinuousLinearMap.det_id]
  exact one_ne_zero

/-- The matrix-valued Schur parametrization gives a local chart at any regular input. -/
theorem _root_.Matrix.UnitaryGroup.exists_schurMatrix_openPartialHomeomorph
    (U : unitaryGroup (Fin n) ℂ) (x : SchurCoordinates n ℂ)
    (ha : Function.Injective fun i ↦ x.1 ⟨(i, i), le_rfl⟩)
    (hb : (spectralAngularFDeriv (fun ij ↦ -star (x.2 ij))).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (SchurCoordinates n ℂ) (Matrix (Fin n) (Fin n) ℂ),
      (e : _ → _) = schurMatrix U ∧ x ∈ e.source := by
  obtain ⟨e, he, hx⟩ := exists_schurCoordinates_openPartialHomeomorph U x ha hb
  refine ⟨e.transHomeomorph schurMatrixCLE.toHomeomorph, ?_, hx⟩
  rw [OpenPartialHomeomorph.transHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph, he]
  funext y
  rw [Function.comp_apply, schurMatrixCLE_apply, schurMatrix]

end Differentiation

end TauCeti
