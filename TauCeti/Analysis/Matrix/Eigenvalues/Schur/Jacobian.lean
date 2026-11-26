/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import TauCeti.Analysis.Matrix.Exponential.SkewAdjoint
import Mathlib.Analysis.Calculus.FDeriv.Star
import TauCeti.LinearAlgebra.Complex.Determinant
import TauCeti.LinearAlgebra.Matrix.Kronecker.MulLeftMulRight
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# The Jacobian of Schur coordinates

Local Schur coordinates conjugate an upper triangular matrix by the exponential of a
zero-diagonal skew-adjoint matrix. In the moving frame, the strict lower part of the
differential is a triangular operator on the angular directions. Its diagonal consists of
the eigenvalue gaps. The upper triangular directions contribute a determinant of one. The
resulting squared Vandermonde factor enters the local change of variables for Ginibre matrices.

## References

* J. B. Hough, M. Krishnapur, Y. Peres and B. Virág,
  *Zeros of Gaussian Analytic Functions and Determinantal Point Processes*, §6.3.
-/

public section

noncomputable section

namespace TauCeti

open Matrix
open scoped Matrix

/-- The upper triangular entries, including the diagonal, and the strict lower entries,
with the latter indexed by their transposed positions. -/
abbrev SchurCoordinates (n : ℕ) :=
  ({ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) × (FinStrictUpper n → ℂ)

variable {n : ℕ}

/-- Assemble a matrix from the two parts of its Schur coordinates. -/
def schurMatrixEquiv : SchurCoordinates n ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  let p (ij : Fin n × Fin n) := ij.1 ≤ ij.2
  let swap : FinStrictUpper n ≃ {ij // ¬p ij} :=
    (Equiv.prodComm _ _).subtypeEquiv fun _ ↦ not_le.symm
  let split : (Fin n × Fin n → ℂ) ≃ₗ[ℂ] ({ij // p ij} → ℂ) × ({ij // ¬p ij} → ℂ) :=
    { Equiv.piEquivPiSubtypeProd p (fun _ ↦ ℂ) with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  ((Matrix.ofLinearEquiv ℂ).symm.trans <|
    (LinearEquiv.curry ℂ ℂ (Fin n) (Fin n)).symm.trans <| split.trans <|
      (LinearEquiv.refl ℂ _).prodCongr (LinearEquiv.funCongrLeft ℂ ℂ swap)).symm

/-- The first coordinate reads the upper triangular entries. -/
@[simp] theorem _root_.Matrix.schurMatrixEquiv_symm_fst (A : Matrix (Fin n) (Fin n) ℂ)
    (ij : {ij : Fin n × Fin n // ij.1 ≤ ij.2}) :
    (schurMatrixEquiv.symm A).1 ij = A ij.val.1 ij.val.2 := (rfl)

/-- The second coordinate reads the strict lower entries. -/
@[simp] theorem _root_.Matrix.schurMatrixEquiv_symm_snd (A : Matrix (Fin n) (Fin n) ℂ)
    (ij : FinStrictUpper n) :
    (schurMatrixEquiv.symm A).2 ij = A ij.val.2 ij.val.1 := (rfl)

/-- At an upper triangular position the assembled matrix reads the first coordinate. -/
@[simp] theorem schurMatrixEquiv_apply_of_le (x : SchurCoordinates n) {i j : Fin n}
    (h : i ≤ j) : schurMatrixEquiv x i j = x.1 ⟨(i, j), h⟩ := by
  have he := schurMatrixEquiv_symm_fst (schurMatrixEquiv x) ⟨(i, j), h⟩
  rw [LinearEquiv.symm_apply_apply] at he
  exact he.symm

/-- At a strict lower position the assembled matrix reads the second coordinate. -/
@[simp] theorem schurMatrixEquiv_apply_of_gt (x : SchurCoordinates n) {i j : Fin n}
    (h : j < i) : schurMatrixEquiv x i j = x.2 ⟨(j, i), h⟩ := by
  have he := schurMatrixEquiv_symm_snd (schurMatrixEquiv x) ⟨(j, i), h⟩
  rw [LinearEquiv.symm_apply_apply] at he
  exact he.symm

/-- The assembled matrix is upper triangular exactly when its strict lower coordinates vanish. -/
@[simp] theorem isUpperTriangular_schurMatrixEquiv_iff (x : SchurCoordinates n) :
    (schurMatrixEquiv x).IsUpperTriangular ↔ x.2 = 0 := by
  constructor
  · intro hx
    funext ij
    rw [← schurMatrixEquiv_apply_of_gt x ij.property]
    exact hx ij.property
  · intro hx i j h
    rw [schurMatrixEquiv_apply_of_gt x (by simpa only [id_eq] using h), hx]
    rfl

/-- Read the strict lower entries of the commutator with an upper triangular matrix.
The input specifies the strict lower part of the first factor. -/
private def schurLowerCommutator (T : Matrix (Fin n) (Fin n) ℂ) :
    (FinStrictUpper n → ℂ) →ₗ[ℂ] (FinStrictUpper n → ℂ) :=
  let L := schurMatrixEquiv.toLinearMap.comp (LinearMap.inr ℂ _ _)
  let P := (LinearMap.snd ℂ _ _).comp schurMatrixEquiv.symm.toLinearMap
  P.comp (((LinearMap.mulRight ℂ T).comp L) - ((LinearMap.mulLeft ℂ T).comp L))

private theorem schurLowerCommutator_apply (T : Matrix (Fin n) (Fin n) ℂ)
    (x : FinStrictUpper n → ℂ) (ij : FinStrictUpper n) :
    schurLowerCommutator T x ij =
      (schurMatrixEquiv (0, x) * T - T * schurMatrixEquiv (0, x)) ij.val.2 ij.val.1 :=
  (rfl)

private theorem schurMatrixEquiv_single (ij : FinStrictUpper n) :
    schurMatrixEquiv (0, Pi.single ij 1) = Matrix.single ij.val.2 ij.val.1 1 := by
  ext i j
  by_cases h : j < i
  · have he : (⟨(j, i), h⟩ : FinStrictUpper n) = ij ↔
        ij.val.2 = i ∧ ij.val.1 = j := by
      rw [eq_comm, Subtype.ext_iff]
      exact Prod.ext_iff.trans and_comm
    simp only [schurMatrixEquiv_apply_of_gt _ h, Pi.single_apply, Matrix.single_apply, he]
  · simp only [schurMatrixEquiv_apply_of_le _ (le_of_not_gt h), Pi.zero_apply,
      Matrix.single_apply]
    split_ifs with he
    · exact (h (he.2 ▸ he.1 ▸ ij.property)).elim
    · rfl

private theorem toMatrix'_schurLowerCommutator (T : Matrix (Fin n) (Fin n) ℂ)
    (ij kl : FinStrictUpper n) :
    LinearMap.toMatrix' (schurLowerCommutator T) ij kl =
      (if ij.val.2 = kl.val.2 then T kl.val.1 ij.val.1 else 0) -
        (if ij.val.1 = kl.val.1 then T ij.val.2 kl.val.2 else 0) := by
  rw [LinearMap.toMatrix'_apply, schurLowerCommutator_apply, schurMatrixEquiv_single,
    Matrix.sub_apply]
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  obtain ⟨⟨k, l⟩, hkl⟩ := kl
  dsimp only
  by_cases hj : j = l
  · subst l
    by_cases hi : i = k
    · subst k
      simp [single_mul_apply_same, mul_single_apply_same]
    · simp [hi, single_mul_apply_same, mul_single_apply_of_ne]
  · by_cases hi : i = k
    · subst k
      simp [hj, mul_single_apply_same, single_mul_apply_of_ne]
    · simp [hi, hj, mul_single_apply_of_ne, single_mul_apply_of_ne]

private theorem det_schurLowerCommutator {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.IsUpperTriangular) :
    (schurLowerCommutator T).det = ∏ ij : FinStrictUpper n,
      (T ij.val.1 ij.val.1 - T ij.val.2 ij.val.2) := by
  -- Order lower positions by row and, within each row, by decreasing column.
  let rank (ij : FinStrictUpper n) : Fin n ×ₗ (Fin n)ᵒᵈ :=
    toLex (ij.val.2, OrderDual.toDual ij.val.1)
  have hrank : Function.Injective rank := by
    intro ij kl h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj (congrArg ofLex h)
    exact Subtype.ext (Prod.ext h₂ h₁)
  have htri : (LinearMap.toMatrix' (schurLowerCommutator T)).BlockTriangular rank := by
    intro ij kl h
    rw [toMatrix'_schurLowerCommutator]
    have h' : kl.val.2 < ij.val.2 ∨
        (kl.val.2 = ij.val.2 ∧ ij.val.1 < kl.val.1) := by
      simpa only [rank, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual] using h
    rcases h' with h' | ⟨he, h'⟩
    · simp [h'.ne', hT h']
    · simp [he, h'.ne, hT h']
  rw [← LinearMap.det_toMatrix', htri.det_eq_prod_diag hrank]
  exact Finset.prod_congr rfl fun ij _ ↦ by
    rw [toMatrix'_schurLowerCommutator]
    simp only [ite_true]

private theorem schurLowerCommutator_eq {T K : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.IsUpperTriangular) (ij : FinStrictUpper n) :
    schurLowerCommutator T (schurMatrixEquiv.symm K).2 ij =
      (K * T - T * K) ij.val.2 ij.val.1 := by
  let S := schurMatrixEquiv (0, (schurMatrixEquiv.symm K).2)
  have hS : (K - S).IsUpperTriangular := by
    intro i j h
    have hij : j < i := by simpa only [id_eq] using h
    dsimp only [S]
    rw [Matrix.sub_apply, schurMatrixEquiv_apply_of_gt _ hij, schurMatrixEquiv_symm_snd,
      sub_self]
  have hzero := ((hS.mul hT).sub (hT.mul hS)) ij.property
  rw [sub_mul, mul_sub] at hzero
  simp only [Matrix.sub_apply] at hzero
  rw [schurLowerCommutator_apply]
  rw [sub_sub_sub_comm] at hzero
  exact (sub_eq_zero.mp hzero).symm

section Differentiation

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

private def schurAngleFlip : (FinStrictUpper n → ℂ) →L[ℝ] (FinStrictUpper n → ℂ) :=
  ContinuousLinearMap.pi fun ij ↦ -Complex.conjCLE.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj ij)

@[simp] private theorem schurAngleFlip_apply (b : FinStrictUpper n → ℂ)
    (ij : FinStrictUpper n) : schurAngleFlip b ij = -star (b ij) := (rfl)

private def schurMatrixCLE :
    SchurCoordinates n ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (schurMatrixEquiv.restrictScalars ℝ).toContinuousLinearEquiv

private def schurUpper :
    ({ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  schurMatrixCLE.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)

private theorem schurUpper_apply (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :
    schurUpper a = schurMatrixEquiv (a, 0) := (rfl)

private theorem schurMatrixCLE_symm_apply (A : Matrix (Fin n) (Fin n) ℂ) :
    schurMatrixCLE.symm A = schurMatrixEquiv.symm A := (rfl)

private def schurFrame (b : FinStrictUpper n → ℂ) : unitaryGroup (Fin n) ℂ :=
  expStrictUpper (schurAngleFlip b)

/-- Conjugate the upper triangular component by the fixed unitary frame followed by the
transverse exponential of the strict lower angular coordinates, and read the resulting
matrix entries in Schur coordinates. -/
def _root_.Matrix.UnitaryGroup.schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n) : SchurCoordinates n :=
  schurMatrixEquiv.symm
    (Unitary.conjStarAlgAut ℂ _ (U * schurFrame x.2) (schurMatrixEquiv (x.1, 0)))

open Matrix.UnitaryGroup

/-- The Schur parametrization assembles the upper triangular input and conjugates it
by the unitary exponential in the fixed frame. -/
theorem _root_.Matrix.UnitaryGroup.schurCoordinates_apply (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n) :
    schurCoordinates U x = schurMatrixEquiv.symm
      (Unitary.conjStarAlgAut ℂ _ (U * expStrictUpper (fun ij ↦ -star (x.2 ij)))
        (schurMatrixEquiv (x.1, 0))) := (rfl)

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
    (x : SchurCoordinates n) : Matrix (Fin n) (Fin n) ℂ :=
  schurMatrixEquiv (schurCoordinates U x)

/-- Reading the entries of the parametrized matrix gives the Schur coordinate map. -/
@[simp] theorem _root_.Matrix.UnitaryGroup.schurMatrixEquiv_symm_schurMatrix
    (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n) : schurMatrixEquiv.symm (schurMatrix U x) = schurCoordinates U x :=
  schurMatrixEquiv.symm_apply_apply _

/-- The matrix parametrization conjugates the triangular input by the fixed frame followed by
the transverse unitary exponential. -/
theorem _root_.Matrix.UnitaryGroup.schurMatrix_apply (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n) :
    schurMatrix U x = Unitary.conjStarAlgAut ℂ _
      (U * expStrictUpper (fun ij ↦ -star (x.2 ij))) (schurMatrixEquiv (x.1, 0)) := by
  rw [schurMatrix, schurCoordinates_apply, LinearEquiv.apply_symm_apply]

private def schurConj (U : unitaryGroup (Fin n) ℂ) :
    SchurCoordinates n ≃L[ℝ] SchurCoordinates n :=
  let C := (Unitary.conjStarAlgAut ℂ _ U).toAlgEquiv.toLinearEquiv.restrictScalars ℝ
  schurMatrixCLE.trans (C.toContinuousLinearEquiv.trans schurMatrixCLE.symm)

private theorem det_schurConj (U : unitaryGroup (Fin n) ℂ) :
    (schurConj U).toContinuousLinearMap.det = 1 := by
  let A : Matrix (Fin n) (Fin n) ℂ := U
  let C := (Unitary.conjStarAlgAut ℂ _ U).toAlgEquiv.toLinearEquiv.toLinearMap
  have hC : C = (LinearMap.mulLeft ℂ A).comp (LinearMap.mulRight ℂ (star A)) := by
    ext M
    simp [C, A, mul_assoc]
  have hdet : C.det = 1 := by
    rw [hC, Matrix.det_mulLeft_comp_mulRight, ← mul_pow, ← det_mul]
    simp [A]
  have hconj : (schurConj U).toContinuousLinearMap.toLinearMap =
      schurMatrixCLE.symm.toLinearEquiv.conj (C.restrictScalars ℝ) := (rfl)
  rw [ContinuousLinearMap.det, hconj, LinearEquiv.conj_apply, LinearMap.comp_assoc,
    LinearMap.det_conj, LinearMap.det_restrictScalars_eq_normSq, hdet, Complex.normSq_one]

/-- Schur coordinates depend smoothly on both the triangular entries and the angles. -/
theorem _root_.Matrix.UnitaryGroup.contDiff_schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    {k : WithTop ℕ∞} :
    ContDiff ℝ k (schurCoordinates U) := by
  have hF : ContDiff ℝ k (fun x : SchurCoordinates n ↦
      (U : Matrix (Fin n) (Fin n) ℂ) * (schurFrame x.2 : Matrix (Fin n) (Fin n) ℂ)) :=
    contDiff_const.mul (contDiff_expStrictUpper.comp (schurAngleFlip.contDiff.comp contDiff_snd))
  have hD := schurUpper.contDiff.comp
    (contDiff_fst : ContDiff ℝ k (Prod.fst : SchurCoordinates n → _))
  have hS := (starL' ℝ : Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] _).toContinuousLinearMap.contDiff.comp hF
  have he : schurCoordinates U = fun x : SchurCoordinates n ↦
      schurMatrixCLE.symm
        ((U : Matrix (Fin n) (Fin n) ℂ) * (schurFrame x.2 : Matrix (Fin n) (Fin n) ℂ) *
          schurUpper x.1 * star ((U : Matrix (Fin n) (Fin n) ℂ) * (schurFrame x.2))) := by
    funext x
    rw [schurCoordinates, Unitary.conjStarAlgAut_apply, Submonoid.coe_mul]
    rfl
  rw [he]
  exact schurMatrixCLE.symm.toContinuousLinearMap.contDiff.comp ((hF.mul hD).mul hS)

private def schurFDeriv (T : Matrix (Fin n) (Fin n) ℂ)
    (K : (FinStrictUpper n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    SchurCoordinates n →L[ℝ] SchurCoordinates n :=
  let C := (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip T -
    ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ) T
  schurMatrixCLE.symm.toContinuousLinearMap.comp
    ((schurUpper.comp (ContinuousLinearMap.fst ℝ _ _)) +
      (C.comp K).comp (ContinuousLinearMap.snd ℝ _ _))

private theorem schurFDeriv_apply (T : Matrix (Fin n) (Fin n) ℂ)
    (K : (FinStrictUpper n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (v : SchurCoordinates n) :
    schurFDeriv T K v =
      schurMatrixEquiv.symm (schurMatrixEquiv (v.1, 0) + (K v.2 * T - T * K v.2)) := (rfl)

private theorem det_schurFDeriv {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.IsUpperTriangular)
    (K : (FinStrictUpper n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (L : (FinStrictUpper n → ℂ) →L[ℝ] (FinStrictUpper n → ℂ))
    (hK : ∀ v, (schurMatrixEquiv.symm (K v)).2 = L v) :
    (schurFDeriv T K).det = L.det *
      ∏ ij : FinStrictUpper n, ‖T ij.val.1 ij.val.1 - T ij.val.2 ij.val.2‖ ^ 2 := by
  classical
  let B := Module.Basis.ofVectorSpace ℝ ({ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ)
  let C := Module.Basis.ofVectorSpace ℝ (FinStrictUpper n → ℂ)
  let D := (schurLowerCommutator T).restrictScalars ℝ
  let M := LinearMap.toMatrix (B.prod C) (B.prod C) (schurFDeriv T K).toLinearMap
  have hsnd (v : SchurCoordinates n) : (schurFDeriv T K v).2 = D (L v.2) := by
    funext ij
    rw [schurFDeriv_apply, schurMatrixEquiv_symm_snd, Matrix.add_apply,
      schurMatrixEquiv_apply_of_gt _ ij.property]
    simp only [Pi.zero_apply, zero_add]
    rw [← schurLowerCommutator_eq hT, hK]
    rfl
  have hblock :
      M = fromBlocks 1 M.toBlocks₁₂ 0 (LinearMap.toMatrix C C (D.comp L.toLinearMap)) := by
    ext (i | i) (j | j)
    · simp [M, LinearMap.toMatrix_apply, schurFDeriv_apply, Matrix.one_apply,
        Finsupp.single_apply, eq_comm]
    · rfl
    · simp [M, LinearMap.toMatrix_apply, hsnd]
    · simp [M, LinearMap.toMatrix_apply, hsnd]
  have hM : (schurFDeriv T K).det = M.det :=
    (LinearMap.det_toMatrix (B.prod C) _).symm
  rw [hM, hblock, det_fromBlocks_zero₂₁, det_one, one_mul, LinearMap.det_toMatrix,
    LinearMap.det_comp]
  rw [mul_comm, ContinuousLinearMap.det, LinearMap.det_restrictScalars_eq_normSq,
    det_schurLowerCommutator hT, map_prod]
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
  rw [schurMatrixEquiv_symm_snd, he, schurAngleFlip_apply, spectralAngularFDeriv_apply]
  rfl

private theorem schurAngleFlip_comp_self :
    (schurAngleFlip (n := n)).comp schurAngleFlip = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro v
  funext ij
  simp

private theorem det_schurAngleFlip_sq :
    (schurAngleFlip (n := n)).det ^ 2 = 1 := by
  rw [sq, ← ContinuousLinearMap.det_comp, schurAngleFlip_comp_self, ContinuousLinearMap.det_id]

private theorem hasFDerivAt_schurCoordinates_relative (x : SchurCoordinates n) :
    HasFDerivAt
      (fun y : SchurCoordinates n ↦ schurMatrixEquiv.symm
        (Unitary.conjStarAlgAut ℂ _
          (relativeFrame (schurAngleFlip x.2) (schurAngleFlip y.2)) (schurMatrixEquiv (y.1, 0))))
      (schurFDeriv (schurMatrixEquiv (x.1, 0)) (schurRelativeFDeriv x.2)) x := by
  let F (b : FinStrictUpper n → ℂ) :=
    (relativeFrame (schurAngleFlip x.2) (schurAngleFlip b) : Matrix (Fin n) (Fin n) ℂ)
  let K := schurRelativeFDeriv x.2
  have hF : HasFDerivAt F K x.2 :=
    (((contDiff_relativeFrame (schurAngleFlip x.2) (k := 1)).differentiable
      one_ne_zero (schurAngleFlip x.2)).hasFDerivAt).comp x.2 schurAngleFlip.hasFDerivAt
  have h1 : F x.2 = 1 := by simp [F]
  let P : SchurCoordinates n →L[ℝ] (FinStrictUpper n → ℂ) := ContinuousLinearMap.snd ℝ _ _
  let Q : SchurCoordinates n →L[ℝ] ({ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ) :=
    ContinuousLinearMap.fst ℝ _ _
  have hFF := hF.comp x (P.hasFDerivAt (x := x))
  have hD := schurUpper.hasFDerivAt.comp x (Q.hasFDerivAt (x := x))
  have hf := schurMatrixCLE.symm.toContinuousLinearMap.hasFDerivAt.comp x
    ((hFF.fun_mul' hD).fun_mul' hFF.star)
  refine (hf.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)).congr_fderiv ?_
  · rw [Unitary.conjStarAlgAut_apply]
    rfl
  · apply ContinuousLinearMap.ext
    intro v
    have hs := star_schurRelativeFDeriv x.2 v.2
    simp only [schurFDeriv_apply, ContinuousLinearMap.comp_apply, add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, starL'_apply, op_smul_eq_mul, smul_eq_mul, P, Q, h1,
      star_one, mul_one, one_mul, K, hs, mul_neg, sub_eq_add_neg,
      schurUpper_apply, schurMatrixCLE_symm_apply]
    exact congrArg schurMatrixEquiv.symm (by abel)

private theorem hasFDerivAt_schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n) :
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
  rw [schurCoordinates, ← hu, map_mul]
  simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, schurConj,
    ContinuousLinearEquiv.trans_apply]
  have hcancel (A : Matrix (Fin n) (Fin n) ℂ) : schurMatrixCLE (schurMatrixEquiv.symm A) = A :=
    schurMatrixEquiv.apply_symm_apply A
  rw [hcancel]
  rfl

/-- The real Jacobian of the Schur parametrization is the angular Jacobian times the
squared Vandermonde of the upper triangular diagonal. -/
theorem _root_.Matrix.UnitaryGroup.det_fderiv_schurCoordinates (U : unitaryGroup (Fin n) ℂ)
    (x : SchurCoordinates n) :
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
      _ = A.det := by rw [det_schurAngleFlip_sq, one_mul]
  rw [(hasFDerivAt_schurCoordinates U x).fderiv, ContinuousLinearMap.det_comp, det_schurConj,
    one_mul, det_schurFDeriv ((isUpperTriangular_schurMatrixEquiv_iff (x.1, 0)).2 rfl)
      _ L (schurRelativeFDeriv_lower x.2), hL]
  simp only [A, schurMatrixEquiv_apply_of_le _ le_rfl]
  rfl

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

/-- At an upper triangular input with distinct diagonal entries, the Schur parametrization
restricts to a local chart centered at zero angle. -/
theorem _root_.Matrix.UnitaryGroup.exists_schurCoordinates_openPartialHomeomorph
    (U : unitaryGroup (Fin n) ℂ)
    (a : {ij : Fin n × Fin n // ij.1 ≤ ij.2} → ℂ)
    (ha : Function.Injective fun i ↦ a ⟨(i, i), le_rfl⟩) :
    ∃ e : OpenPartialHomeomorph (SchurCoordinates n) (SchurCoordinates n),
      (e : _ → _) = schurCoordinates U ∧ (a, 0) ∈ e.source := by
  let x : SchurCoordinates n := (a, 0)
  let f := schurCoordinates U
  let D := fderiv ℝ f x
  have hD : D.det ≠ 0 := by
    have h := det_fderiv_schurCoordinates_zero U a
    rw [h]
    refine Finset.prod_ne_zero_iff.mpr fun ij _ ↦ ?_
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (ha.ne ij.property.ne)))
  have hf := (contDiff_schurCoordinates U (k := 1)).contDiffAt (x := x)
  have hfd : HasFDerivAt f (D.toContinuousLinearEquivOfDetNeZero hD : _ →L[ℝ] _) x := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hf.differentiableAt one_ne_zero).hasFDerivAt
  have hstrict := hf.hasStrictFDerivAt hfd one_ne_zero
  exact ⟨hstrict.toOpenPartialHomeomorph _, hstrict.toOpenPartialHomeomorph_coe,
    hstrict.mem_toOpenPartialHomeomorph_source⟩

end Differentiation

end TauCeti
