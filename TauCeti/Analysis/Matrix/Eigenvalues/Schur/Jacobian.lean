/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.Analysis.Matrix.Eigenvalues.Schur.Coordinates
public import TauCeti.Topology.Algebra.Module.Matrix
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Analysis.Calculus.FDeriv.Unitary
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Matrix.Eigenvalues.Schur.Basic
import TauCeti.LinearAlgebra.Complex.Determinant
import TauCeti.LinearAlgebra.Matrix.Kronecker.MulLeftMulRight
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Prod
import TauCeti.Topology.Algebra.Matrix.UnitaryGroup
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

open _root_.Matrix
open scoped _root_.Matrix

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

section Differentiation

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

private def schurAngleFlip : (FinStrictUpper n → 𝕜) ≃L[ℝ] (FinStrictUpper n → 𝕜) :=
  ContinuousLinearEquiv.piCongrRight fun _ ↦
    RCLike.conjCLE.trans (ContinuousLinearEquiv.neg ℝ)

@[simp] private theorem schurAngleFlip_apply (b : FinStrictUpper n → 𝕜)
    (ij : FinStrictUpper n) : schurAngleFlip b ij = -star (b ij) := by
  simp [schurAngleFlip, RCLike.star_def]

private theorem schurAngleFlip_symm :
    (schurAngleFlip (n := n) (𝕜 := 𝕜)).symm = schurAngleFlip := by
  apply ContinuousLinearEquiv.ext
  funext b
  rw [ContinuousLinearEquiv.symm_apply_eq]
  funext ij
  simp

private theorem coe_schurAngleFlip (b : FinStrictUpper n → 𝕜) :
    schurAngleFlip b = fun ij ↦ -star (b ij) :=
  funext (schurAngleFlip_apply b)

private def schurUpper :
    ({ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (schurMatrixCLE (𝕜 := ℝ)).toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)

private theorem schurUpper_apply (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :
    schurUpper a = schurMatrixEquiv (a, 0) := by
  rw [schurUpper, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.inl_apply, schurMatrixCLE_apply]

open Matrix.UnitaryGroup

private def schurConj (U : unitaryGroup (Fin n) ℂ) :
    SchurCoordinates (Fin n) ℂ →L[ℝ] SchurCoordinates (Fin n) ℂ :=
  (schurMatrixCLE (𝕜 := ℝ)).symm.toContinuousLinearMap ∘L
    ((conjStarAlgAutCLE U).restrictScalars ℝ).toContinuousLinearMap ∘L
    (schurMatrixCLE (𝕜 := ℝ)).toContinuousLinearMap

private theorem schurConj_apply (U : unitaryGroup (Fin n) ℂ) (x : SchurCoordinates (Fin n) ℂ) :
    schurConj U x = schurMatrixEquiv.symm
      (Unitary.conjStarAlgAut ℂ _ U (schurMatrixEquiv x)) := by
  simp only [schurConj, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.restrictScalars_apply, conjStarAlgAutCLE_apply,
    schurMatrixCLE_apply, schurMatrixCLE_symm_apply]

private theorem det_schurConj (U : unitaryGroup (Fin n) ℂ) : (schurConj U).det = 1 := by
  let e := (conjStarAlgAutCLE U).restrictScalars ℝ
  calc
    (schurConj U).det = e.toContinuousLinearMap.det := by
      simpa only [schurConj, ContinuousLinearEquiv.symm_symm] using
        ContinuousLinearMap.det_conj e.toContinuousLinearMap (schurMatrixCLE (𝕜 := ℝ)).symm
    _ = 1 := by
      dsimp only [e]
      rw [ContinuousLinearMap.det, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
        ContinuousLinearEquiv.restrictScalars_toLinearEquiv, conjStarAlgAutCLE_toLinearEquiv,
        LinearEquiv.restrictScalars_toLinearMap]
      exact det_conjStarAlgAut_restrictScalars U

/-- Schur coordinates depend smoothly on both the triangular entries and the angles. -/
theorem _root_.Matrix.UnitaryGroup.contDiff_schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    {k : WithTop ℕ∞} :
    ContDiff ℝ k (schurCoordinates U) := by
  have hD := schurUpper.contDiff.comp
    (contDiff_fst : ContDiff ℝ k (Prod.fst : SchurCoordinates (Fin n) ℂ → _))
  have h := contDiff_conjStarAlgAut_expStrictUpper U hD
    (schurAngleFlip.toContinuousLinearMap.contDiff.comp contDiff_snd)
  convert (schurMatrixCLE (𝕜 := ℝ)).symm.toContinuousLinearMap.contDiff.comp h using 1
  funext x
  simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, schurCoordinates_apply,
    schurFrame_apply, ← coe_schurAngleFlip, schurMatrixCLE_symm_apply, schurUpper_apply,
    Unitary.conjStarAlgAut_apply]

/-- The matrix-valued Schur parametrization is smooth in the triangular entries and angles. -/
theorem _root_.Matrix.UnitaryGroup.contDiff_schurMatrix (U : unitaryGroup (Fin n) ℂ)
    {k : WithTop ℕ∞} : ContDiff ℝ k (schurMatrix U) := by
  simpa only [Function.comp_def, schurMatrixCLE_apply, schurMatrixEquiv_schurCoordinates] using
    (schurMatrixCLE (𝕜 := ℝ) (ι := Fin n) (R := ℂ)).contDiff.comp (contDiff_schurCoordinates U)

private def schurFDeriv (T : Matrix (Fin n) (Fin n) ℂ)
    (K : (FinStrictUpper n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    SchurCoordinates (Fin n) ℂ →L[ℝ] SchurCoordinates (Fin n) ℂ :=
  let C := (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip T -
    ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ) T
  (schurMatrixCLE (𝕜 := ℝ)).symm.toContinuousLinearMap.comp
    ((schurUpper.comp (ContinuousLinearMap.fst ℝ _ _)) +
      C.comp (K.comp (ContinuousLinearMap.snd ℝ _ _)))

private theorem schurFDeriv_apply (T : Matrix (Fin n) (Fin n) ℂ)
    (K : (FinStrictUpper n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (v : SchurCoordinates (Fin n) ℂ) :
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
  have hsnd (v : SchurCoordinates (Fin n) ℂ) : (schurFDeriv T K v).2 = D (L v.2) := by
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
    simp [g, e, LinearEquiv.conj_apply_apply, schurFDeriv_apply]
  have hg : g.det = (schurFDeriv T K).det := by
    dsimp only [g]
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj, ContinuousLinearMap.det]
  rw [← hg, LinearMap.det_eq_det_mul_det_of_fst_apply_inr hzero, h₁, h₂, LinearMap.det_id, mul_one,
    LinearMap.det_comp, mul_comm, ← ContinuousLinearMap.det,
    LinearMap.det_restrictScalars_eq_normSq, hT.det_schurLowerCommutator, map_prod]
  simp only [Complex.normSq_eq_norm_sq]

private def schurRelativeFDeriv (b : FinStrictUpper n → 𝕜) :
    (FinStrictUpper n → 𝕜) →L[ℝ] Matrix (Fin n) (Fin n) 𝕜 :=
  (fderiv ℝ (fun c ↦ (relativeFrame (schurAngleFlip b) c : Matrix (Fin n) (Fin n) 𝕜))
    (schurAngleFlip b)).comp schurAngleFlip.toContinuousLinearMap

private theorem hasFDerivAt_schurRelativeFrame (b : FinStrictUpper n → 𝕜) :
    HasFDerivAt
      (fun c ↦ (relativeFrame (schurAngleFlip b) (schurAngleFlip c) : Matrix (Fin n) (Fin n) 𝕜))
      (schurRelativeFDeriv b) b :=
  ((contDiff_relativeFrame (schurAngleFlip b) (k := 1)).differentiable one_ne_zero
    (schurAngleFlip b)).hasFDerivAt.comp b
      (schurAngleFlip (n := n) (𝕜 := 𝕜)).toContinuousLinearMap.hasFDerivAt

private theorem star_schurRelativeFDeriv (b v : FinStrictUpper n → 𝕜) :
    star (schurRelativeFDeriv b v) = -(schurRelativeFDeriv b v) := by
  rw [schurRelativeFDeriv, ContinuousLinearMap.comp_apply, star_fderiv_relativeFrame]

/-- The angular differential takes the strict lower entries of the derivative of the relative
unitary frame at the base angle. Input and output are indexed by the transposed lower positions. -/
def schurAngularFDeriv (b : FinStrictUpper n → 𝕜) :
    (FinStrictUpper n → 𝕜) →L[ℝ] (FinStrictUpper n → 𝕜) :=
  schurAngleFlip.toContinuousLinearMap ∘L
    spectralAngularFDeriv (schurAngleFlip b) ∘L schurAngleFlip.toContinuousLinearMap

private theorem schurRelativeFDeriv_lower (b v : FinStrictUpper n → 𝕜) :
    (schurMatrixEquiv.symm (schurRelativeFDeriv b v)).2 = schurAngularFDeriv b v := by
  funext ij
  have hs := congrFun₂ (star_schurRelativeFDeriv b v) ij.val.2 ij.val.1
  have he : (schurRelativeFDeriv b v) ij.val.2 ij.val.1 =
      -star ((schurRelativeFDeriv b v) ij.val.1 ij.val.2) := by
    simpa only [Matrix.star_apply, Matrix.neg_apply, neg_neg] using (congrArg Neg.neg hs).symm
  rw [schurMatrixEquiv_symm_snd, he]
  simp only [schurAngularFDeriv, schurRelativeFDeriv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, schurAngleFlip_apply, spectralAngularFDeriv_apply]

/-- Each entry is the corresponding strict lower entry of the derivative in Schur directions. -/
theorem schurAngularFDeriv_apply (b v : FinStrictUpper n → 𝕜) (ij : FinStrictUpper n) :
    schurAngularFDeriv b v ij =
      fderiv ℝ (fun c ↦ (relativeFrame (fun kl ↦ -star (b kl)) (fun kl ↦ -star (c kl)) :
        Matrix (Fin n) (Fin n) 𝕜)) b v ij.val.2 ij.val.1 := by
  rw [← schurRelativeFDeriv_lower, schurMatrixEquiv_symm_snd,
    ← (hasFDerivAt_schurRelativeFrame b).fderiv]
  simp only [coe_schurAngleFlip]

/-- At zero angle the Schur angular differential is the identity. -/
@[simp] theorem schurAngularFDeriv_zero :
    schurAngularFDeriv (0 : FinStrictUpper n → 𝕜) = ContinuousLinearMap.id ℝ _ := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [schurAngularFDeriv, map_zero, spectralAngularFDeriv_zero,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe]
  simpa only [schurAngleFlip_symm] using schurAngleFlip.symm_apply_apply v

/-- The determinant of the Schur angular differential depends continuously on the angles. -/
theorem continuous_det_schurAngularFDeriv :
    Continuous (fun b : FinStrictUpper n → 𝕜 ↦ (schurAngularFDeriv b).det) := by
  apply ContinuousLinearMap.continuous_det.comp
  refine continuous_clm_apply.mpr fun v ↦ continuous_pi fun ij ↦ ?_
  let F (b : FinStrictUpper n → 𝕜) :=
    (expStrictUpper (schurAngleFlip b) : Matrix (Fin n) (Fin n) 𝕜)
  have hF : ContDiff ℝ 1 F :=
    (contDiff_expStrictUpper (n := n) (𝕜 := 𝕜)).comp
      (schurAngleFlip (n := n) (𝕜 := 𝕜)).contDiff
  have h (b : FinStrictUpper n → 𝕜) :
      schurAngularFDeriv b v ij = (star (F b) * fderiv ℝ F b v) ij.val.2 ij.val.1 := by
    rw [schurAngularFDeriv_apply]
    simp only [← coe_schurAngleFlip, coe_relativeFrame]
    -- Fold the two occurrences of the frame into the same smooth family.
    change fderiv ℝ (fun c ↦ star (F b) * F c) b v ij.val.2 ij.val.1 = _
    rw [fderiv_const_mul (hF.differentiable one_ne_zero b), smul_apply, smul_eq_mul]
  simp_rw [h]
  exact ((continuous_star.comp hF.continuous).mul
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)).matrix_elem _ _

private theorem hasFDerivAt_schurCoordinates_relative (x : SchurCoordinates (Fin n) ℂ) :
    HasFDerivAt
      (fun y : SchurCoordinates (Fin n) ℂ ↦ schurMatrixEquiv.symm
        (Unitary.conjStarAlgAut ℂ _
          (relativeFrame (schurAngleFlip x.2) (schurAngleFlip y.2)) (schurMatrixEquiv (y.1, 0))))
      (schurFDeriv (schurMatrixEquiv (x.1, 0)) (schurRelativeFDeriv x.2)) x := by
  let F (b : FinStrictUpper n → ℂ) :=
    (relativeFrame (schurAngleFlip x.2) (schurAngleFlip b) : Matrix (Fin n) (Fin n) ℂ)
  have hF : HasFDerivAt F (schurRelativeFDeriv x.2) x.2 := hasFDerivAt_schurRelativeFrame x.2
  let P : SchurCoordinates (Fin n) ℂ →L[ℝ] (FinStrictUpper n → ℂ) := ContinuousLinearMap.snd ℝ _ _
  let Q : SchurCoordinates (Fin n) ℂ →L[ℝ] ({ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :=
    ContinuousLinearMap.fst ℝ _ _
  have hFF := hF.comp x P.hasFDerivAt
  have hD := schurUpper.hasFDerivAt.comp x Q.hasFDerivAt
  have h := hFF.unitary_conj_of_eq_one hD
    (.of_forall fun y ↦ (relativeFrame (schurAngleFlip x.2) (schurAngleFlip y.2)).property)
    (by simp [F])
  have hf := (schurMatrixCLE (𝕜 := ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp x h
  refine (hf.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)).congr_fderiv ?_
  · simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, schurMatrixCLE_symm_apply,
      schurUpper_apply, Unitary.conjStarAlgAut_apply, F, Q, ContinuousLinearMap.coe_fst']
  · simp only [schurFDeriv, Function.comp_apply, schurUpper_apply, P, Q,
      ContinuousLinearMap.coe_fst']

private theorem hasFDerivAt_schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates (Fin n) ℂ) :
    HasFDerivAt (schurCoordinates U)
      ((schurConj (U * schurFrame x.2)).comp
        (schurFDeriv (schurMatrixEquiv (x.1, 0)) (schurRelativeFDeriv x.2))) x := by
  have h := (schurConj (U * schurFrame x.2)).hasFDerivAt.comp x
    (hasFDerivAt_schurCoordinates_relative x)
  refine h.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)
  have hu : (U * schurFrame x.2) * relativeFrame (schurAngleFlip x.2) (schurAngleFlip y.2) =
      U * schurFrame y.2 := by
    simp only [mul_assoc, schurFrame_apply, ← coe_schurAngleFlip, expStrictUpper_mul_relativeFrame]
  simp only [Function.comp_apply, schurConj_apply, LinearEquiv.apply_symm_apply]
  rw [schurCoordinates_apply, ← hu, Unitary.conjStarAlgAut_mul_apply]

/-- The derivative of the Schur matrix is the triangular variation plus the angular
commutator, conjugated by the frame at the base angle. Here `K` is the derivative of the
relative unitary frame in the angular direction. -/
theorem _root_.Matrix.UnitaryGroup.fderiv_schurMatrix_apply (U : unitaryGroup (Fin n) ℂ)
    (x v : SchurCoordinates (Fin n) ℂ) :
    let T := schurMatrixEquiv (x.1, 0)
    let K := fderiv ℝ (fun b ↦ (relativeFrame (fun ij ↦ -star (x.2 ij)) (fun ij ↦ -star (b ij)) :
      Matrix (Fin n) (Fin n) ℂ)) x.2 v.2
    fderiv ℝ (schurMatrix U) x v =
      Unitary.conjStarAlgAut ℂ _ (U * schurFrame x.2)
        (schurMatrixEquiv (v.1, 0) + (K * T - T * K)) := by
  let e := schurMatrixCLE (𝕜 := ℝ) (ι := Fin n) (R := ℂ)
  have h := e.toContinuousLinearMap.hasFDerivAt.comp x (hasFDerivAt_schurCoordinates U x)
  have he : schurMatrix U = (e.toContinuousLinearMap : _ → _) ∘ schurCoordinates U := by
    funext y
    simp only [e, Function.comp_apply, ContinuousLinearEquiv.coe_coe, schurMatrixCLE_apply,
      schurMatrixEquiv_schurCoordinates]
  rw [he, h.fderiv]
  simp only [e, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, schurMatrixCLE_apply,
    schurConj_apply, LinearEquiv.apply_symm_apply, schurFDeriv_apply,
    ← (hasFDerivAt_schurRelativeFrame x.2).fderiv, coe_schurAngleFlip]

/-- The real Jacobian of the Schur parametrization is the angular Jacobian times the
squared Vandermonde of the upper triangular diagonal. -/
theorem _root_.Matrix.UnitaryGroup.det_fderiv_schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates (Fin n) ℂ) :
    (fderiv ℝ (schurCoordinates U) x).det =
      (schurAngularFDeriv x.2).det *
        ∏ ij : FinStrictUpper n, ‖x.1 ⟨(ij.val.1, ij.val.1), le_rfl⟩ -
          x.1 ⟨(ij.val.2, ij.val.2), le_rfl⟩‖ ^ 2 := by
  rw [(hasFDerivAt_schurCoordinates U x).fderiv, ContinuousLinearMap.det_comp, det_schurConj,
    one_mul, det_schurFDeriv ((isUpperTriangular_schurMatrixEquiv_iff (x.1, 0)).2 rfl)
      _ _ (schurRelativeFDeriv_lower x.2)]
  simp only [schurMatrixEquiv_apply_of_le _ le_rfl]

/-- At zero angle the Jacobian in every fixed unitary frame is the squared Vandermonde. -/
@[simp] theorem _root_.Matrix.UnitaryGroup.det_fderiv_schurCoordinates_zero
    (U : unitaryGroup (Fin n) ℂ)
    (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :
    (fderiv ℝ (schurCoordinates U) (a, 0)).det =
      ∏ ij : FinStrictUpper n, ‖a ⟨(ij.val.1, ij.val.1), le_rfl⟩ -
        a ⟨(ij.val.2, ij.val.2), le_rfl⟩‖ ^ 2 := by
  simp only [det_fderiv_schurCoordinates, schurAngularFDeriv_zero,
    ContinuousLinearMap.det_id, one_mul]

/-- At distinct diagonal entries and an invertible angular differential, the Schur
parametrization restricts to a local chart with real-analytic inverse. -/
theorem _root_.Matrix.UnitaryGroup.exists_schurCoordinates_openPartialHomeomorph
    (U : unitaryGroup (Fin n) ℂ) (x : SchurCoordinates (Fin n) ℂ)
    (ha : Function.Injective fun i ↦ x.1 ⟨(i, i), le_rfl⟩)
    (hb : (schurAngularFDeriv x.2).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (SchurCoordinates (Fin n) ℂ) (SchurCoordinates (Fin n) ℂ),
      (e : _ → _) = schurCoordinates U ∧ x ∈ e.source ∧ ContDiffOn ℝ ⊤ e.symm e.target := by
  let f := schurCoordinates U
  let D := fderiv ℝ f x
  have hD : D.det ≠ 0 := by
    rw [det_fderiv_schurCoordinates]
    refine mul_ne_zero hb (Finset.prod_ne_zero_iff.mpr fun ij _ ↦ ?_)
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (ha.ne ij.property.ne)))
  obtain ⟨e, he, hx, _, hInv⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph
    (contDiff_schurCoordinates U (k := ⊤)).contDiffOn isOpen_univ (Set.mem_univ x) le_top
    (ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero D hD)
  exact ⟨e, he, hx, hInv⟩

/-- Distinct diagonal entries give a local Schur chart with real-analytic inverse at zero angle. -/
theorem _root_.Matrix.UnitaryGroup.exists_schurCoordinates_openPartialHomeomorph_zero
    (U : unitaryGroup (Fin n) ℂ) (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ)
    (ha : Function.Injective fun i ↦ a ⟨(i, i), le_rfl⟩) :
    ∃ e : OpenPartialHomeomorph (SchurCoordinates (Fin n) ℂ) (SchurCoordinates (Fin n) ℂ),
      (e : _ → _) = schurCoordinates U ∧ (a, 0) ∈ e.source ∧ ContDiffOn ℝ ⊤ e.symm e.target := by
  apply exists_schurCoordinates_openPartialHomeomorph U (a, 0) ha
  simpa only [schurAngularFDeriv_zero, ContinuousLinearMap.det_id] using
    (one_ne_zero : (1 : ℝ) ≠ 0)

/-- The matrix-valued Schur parametrization gives a local chart with real-analytic inverse at any
regular input. -/
theorem _root_.Matrix.UnitaryGroup.exists_schurMatrix_openPartialHomeomorph
    (U : unitaryGroup (Fin n) ℂ) (x : SchurCoordinates (Fin n) ℂ)
    (ha : Function.Injective fun i ↦ x.1 ⟨(i, i), le_rfl⟩)
    (hb : (schurAngularFDeriv x.2).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (SchurCoordinates (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ),
      (e : _ → _) = schurMatrix U ∧ x ∈ e.source ∧ ContDiffOn ℝ ⊤ e.symm e.target := by
  obtain ⟨e, he, hx, hInv⟩ := exists_schurCoordinates_openPartialHomeomorph U x ha hb
  let L := schurMatrixCLE (𝕜 := ℝ) (ι := Fin n) (R := ℂ)
  refine ⟨e.transHomeomorph L.toHomeomorph, ?_, hx, ?_⟩
  · rw [OpenPartialHomeomorph.transHomeomorph_apply, ContinuousLinearEquiv.coe_toHomeomorph, he]
    funext y
    simp only [Function.comp_apply, L, schurMatrixCLE_apply, schurMatrixEquiv_schurCoordinates]
  · rw [OpenPartialHomeomorph.transHomeomorph_symm_apply,
      OpenPartialHomeomorph.transHomeomorph_target, ← ContinuousLinearEquiv.toHomeomorph_symm,
      ContinuousLinearEquiv.coe_toHomeomorph]
    exact hInv.comp L.symm.contDiff.contDiffOn (fun _ hy ↦ hy)

/-- Every complex matrix with simple spectrum is the center of a local Schur chart with
real-analytic inverse at zero angle, where simplicity means separability of the characteristic
polynomial. -/
theorem _root_.Matrix.exists_schurMatrix_openPartialHomeomorph_of_separable
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.charpoly.Separable) :
    ∃ (U : unitaryGroup (Fin n) ℂ) (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ)
      (e : OpenPartialHomeomorph (SchurCoordinates (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ)),
      (e : _ → _) = schurMatrix U ∧ (a, 0) ∈ e.source ∧ e (a, 0) = A ∧
        ContDiffOn ℝ ⊤ e.symm e.target := by
  obtain ⟨U, hU⟩ := A.exists_unitary_isUpperTriangular
  let T := (Unitary.conjStarAlgAut ℂ _ U).symm A
  let a := (schurMatrixEquiv.symm T : SchurCoordinates (Fin n) ℂ).1
  have hT : T.IsUpperTriangular := by
    simpa only [T, Unitary.conjStarAlgAut_symm_apply, Unitary.coe_star] using hU
  have hTa : schurMatrixEquiv (a, 0) = T := by
    apply schurMatrixEquiv.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    refine Prod.ext rfl ?_
    exact ((isUpperTriangular_schurMatrixEquiv_iff (schurMatrixEquiv.symm T)).1
      (by simpa only [LinearEquiv.apply_symm_apply] using hT)).symm
  have ha : Function.Injective fun i ↦ a ⟨(i, i), le_rfl⟩ := by
    rw [← charpoly_unitary_conj A U, charpoly_of_isUpperTriangular _ hU] at hA
    simpa only [a, schurMatrixEquiv_symm_fst, T, Unitary.conjStarAlgAut_symm_apply,
      Unitary.coe_star, diag_apply] using hA.injective_of_prod_X_sub_C
  obtain ⟨e, he, hx, hInv⟩ := exists_schurMatrix_openPartialHomeomorph U (a, 0) ha
    (by simp [ContinuousLinearMap.det_id])
  refine ⟨U, a, e, he, hx, ?_, hInv⟩
  rw [he, schurMatrix_zero, hTa, StarAlgEquiv.apply_symm_apply]

end Differentiation

end TauCeti
