/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Extension
import TauCeti.LinearAlgebra.Matrix.Triangular.Intertwining
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
import TauCeti.RingTheory.Polynomial.RootEnumeration

/-!
# Unitary Schur triangularization

Every complex square matrix is unitarily similar to an upper triangular matrix. Any prescribed
ordering of the characteristic roots, with their algebraic multiplicities, can be put on the
diagonal. When the eigenvalues are distinct and their order is fixed, the unitary matrix is
determined up to right multiplication by the diagonal torus. Every representative of the coset
gives the same ordered diagonal. This is the triangular representation used in the spectral
change of variables for complex Ginibre matrices. Existence also holds for real matrices with
split characteristic polynomial.

## References

* J. B. Hough, M. Krishnapur, Y. Peres and B. Virág,
  *Zeros of Gaussian Analytic Functions and Determinantal Point Processes*, §6.3.
-/

public section

open Module.End Polynomial

namespace Matrix

section Ordered

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem exists_unitary_schur_first_column {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) {z : 𝕜} (hz : A.charpoly.IsRoot z) :
    ∃ U : unitaryGroup (Fin (n + 1)) 𝕜,
      ∀ i : Fin (n + 1),
        (star U.val * A * U.val : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) i 0 =
          if i = 0 then z else 0 := by
  let std := EuclideanSpace.basisFun (Fin (n + 1)) 𝕜
  let T : Module.End 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := A.toEuclideanLin
  have hA : LinearMap.toMatrix std.toBasis std.toBasis T = A := by
    dsimp only [T, std]
    rw [toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  have heig : T.HasEigenvalue z := by
    rw [hasEigenvalue_iff_isRoot_charpoly, ← LinearMap.charpoly_toMatrix _ std.toBasis, hA]
    exact hz
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hTw : T (NormedSpace.normalize v) = z • NormedSpace.normalize v := by
    simpa only [NormedSpace.normalize, LinearMap.restrictScalars_apply, hv.apply_eq_smul,
      smul_comm (‖v‖⁻¹ : ℝ) z v] using (T.restrictScalars ℝ).map_smul ‖v‖⁻¹ v
  obtain ⟨b, hb⟩ := TauCeti.exists_orthonormalBasis_fin_apply_zero_eq
    (by rw [finrank_euclideanSpace, Fintype.card_fin]) (NormedSpace.norm_normalize hv.2)
  let U : unitaryGroup (Fin (n + 1)) 𝕜 :=
    ⟨std.toBasis.toMatrix b.toBasis, std.toMatrix_orthonormalBasis_mem_unitary b⟩
  have hstar : star U.val = b.toBasis.toMatrix std.toBasis :=
    left_inv_eq_right_inv (Unitary.coe_star_mul_self U)
      (std.toBasis.toMatrix_mul_toMatrix_flip b.toBasis)
  have hmatrix : star U.val * A * U.val = LinearMap.toMatrix b.toBasis b.toBasis T := by
    rw [hstar, ← hA]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      b.toBasis std.toBasis b.toBasis std.toBasis T
  refine ⟨U, fun i ↦ ?_⟩
  have hTb : T (b.toBasis 0) = z • b.toBasis 0 := by
    simpa only [OrthonormalBasis.coe_toBasis, hb] using hTw
  rw [hmatrix, LinearMap.toMatrix_apply, hTb, map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]

private theorem exists_unitary_initial_schur_block {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (d : Fin (n + 1) → 𝕜)
    (hd : A.charpoly = ∏ i, (X - C (d i))) :
    let e : Fin 1 ⊕ Fin n ≃ Fin (n + 1) := finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
    ∃ (U : unitaryGroup (Fin (n + 1)) 𝕜) (F : Matrix (Fin 1) (Fin n) 𝕜)
      (D : Matrix (Fin n) (Fin n) 𝕜),
      (star U.val * A * U.val).submatrix e e =
        fromBlocks (diagonal fun _ : Fin 1 ↦ d 0) F 0 D ∧
      D.charpoly = ∏ i : Fin n, (X - C (d i.succ)) := by
  have hz : A.charpoly.IsRoot (d 0) := by
    simp [Polynomial.IsRoot, hd, Fin.prod_univ_succ]
  obtain ⟨U, hcol⟩ := exists_unitary_schur_first_column A hz
  let B := star U.val * A * U.val
  let e : Fin 1 ⊕ Fin n ≃ Fin (n + 1) := finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
  have he₀ (i : Fin 1) : e (Sum.inl i) = 0 := by
    apply Fin.ext
    simp [e, Fin.eq_zero i]
  let D := (B.submatrix e e).toBlocks₂₂
  let F := (B.submatrix e e).toBlocks₁₂
  have hB : B.submatrix e e = fromBlocks (diagonal fun _ : Fin 1 ↦ d 0) F 0 D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simpa [he₀, Fin.eq_zero i, Fin.eq_zero j] using hcol (0 : Fin (n + 1))
    · rfl
    · have hi : e (Sum.inr i) ≠ 0 := fun h ↦
        Sum.inr_ne_inl (e.injective (h.trans (he₀ 0).symm))
      simpa [he₀, hi] using hcol (e (Sum.inr i))
    · rfl
  refine ⟨U, F, D, hB, ?_⟩
  have hc : (B.submatrix e e).charpoly = A.charpoly := calc
    _ = (reindex e.symm e.symm B).charpoly := by simp [reindex_apply]
    _ = B.charpoly := charpoly_reindex e.symm B
    _ = A.charpoly := charpoly_unitary_conj A U
  rw [hB, charpoly_fromBlocks_zero₂₁, charpoly_diagonal, Fin.prod_univ_one, hd,
    Fin.prod_univ_succ] at hc
  exact mul_left_cancel₀ (X_sub_C_ne_zero (d 0)) hc

private theorem exists_unitary_isUpperTriangular_diag_fin {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) (d : Fin n → 𝕜)
    (hd : A.charpoly = ∏ i, (X - C (d i))) :
    ∃ U : unitaryGroup (Fin n) 𝕜,
      (star U.val * A * U.val).IsUpperTriangular ∧ (star U.val * A * U.val).diag = d := by
  induction n with
  | zero => exact ⟨1, fun i ↦ i.elim0, funext fun i ↦ i.elim0⟩
  | succ n ih =>
    let e : Fin 1 ⊕ Fin n ≃ Fin (n + 1) := finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
    have he₀ (i : Fin 1) : e (Sum.inl i) = 0 := by
      apply Fin.ext
      simp [e, Fin.eq_zero i]
    have he₁ (i : Fin n) : e (Sum.inr i) = i.succ := by
      apply Fin.ext
      simp [e]
    obtain ⟨U, F, D, hB, hD⟩ := exists_unitary_initial_schur_block A d hd
    obtain ⟨V, hV, hdiag⟩ := ih D (d ∘ Fin.succ) hD
    let W := UnitaryGroup.prodBlockSucc 𝕜 n (1, V)
    have hW : W.val.submatrix e e =
        fromBlocks 1 0 0 V.val := by
      rw [UnitaryGroup.coe_prodBlockSucc]
      exact (reindex e e).symm_apply_apply _
    let B := star (U * W).val * A * (U * W).val
    have hC : B.submatrix e e =
        fromBlocks (diagonal fun _ : Fin 1 ↦ d 0) (F * V.val) 0 (star V.val * D * V.val) := by
      have h : B = star W.val * (star U.val * A * U.val) * W.val := by
        simp only [B, Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
      rw [h, ← submatrix_mul_equiv _ _ e e e, ← submatrix_mul_equiv _ _ e e e]
      rw [star_eq_conjTranspose, ← conjTranspose_submatrix, hW, hB]
      simp [fromBlocks_conjTranspose, fromBlocks_multiply, star_eq_conjTranspose]
    have hUpper : B.IsUpperTriangular := by
      intro i j hij
      refine Fin.cases (fun h ↦ (Fin.not_lt_zero _ h).elim) (fun a h ↦ ?_) i hij
      refine Fin.cases (fun _ ↦ ?_) (fun b h ↦ ?_) j h
      · simpa [he₀, he₁] using
          congr_fun₂ hC (Sum.inr a) (Sum.inl (0 : Fin 1))
      · simpa [he₁, hV (Fin.succ_lt_succ_iff.mp h)] using
          congr_fun₂ hC (Sum.inr a) (Sum.inr b)
    have hDiag : B.diag = d := funext fun i ↦ by
      refine Fin.cases ?_ (fun a ↦ ?_) i
      · simpa [he₀] using congr_fun₂ hC (Sum.inl (0 : Fin 1)) (Sum.inl (0 : Fin 1))
      · simpa [he₁, diag_apply, Function.comp_apply] using
          (congr_fun₂ hC (Sum.inr a) (Sum.inr a)).trans (congrFun hdiag a)
    exact ⟨U * W, hUpper, hDiag⟩

/-- **Ordered Schur triangularization.** A tuple is the diagonal of an upper triangular unitary
conjugate of A exactly when it lists the characteristic roots of A with their multiplicities. -/
theorem exists_unitary_isUpperTriangular_diag_iff {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι 𝕜) (d : ι → 𝕜) :
    (∃ U : unitaryGroup ι 𝕜,
      (star U.val * A * U.val).IsUpperTriangular ∧ (star U.val * A * U.val).diag = d) ↔
    A.charpoly = ∏ i, (X - C (d i)) := by
  constructor
  · rintro ⟨U, hU, hdiag⟩
    rw [← charpoly_unitary_conj A U, charpoly_of_isUpperTriangular _ hU]
    exact Finset.prod_congr rfl fun i _ ↦ congrArg (fun z ↦ X - C z) (congrFun hdiag i)
  · intro hd
    let e := Fintype.orderIsoFinOfCardEq ι rfl
    have he : (A.submatrix e e).charpoly = ∏ i, (X - C ((d ∘ e) i)) := by
      calc
        _ = (reindex e.symm.toEquiv e.symm.toEquiv A).charpoly := by simp [reindex_apply]
        _ = _ := (charpoly_reindex _ A).trans (hd.trans
          (Fintype.prod_equiv e.toEquiv _ _ fun _ ↦ rfl).symm)
    obtain ⟨U, hU, hdiag⟩ := exists_unitary_isUpperTriangular_diag_fin _ _ he
    let V : unitaryGroup ι 𝕜 :=
      ⟨U.val.submatrix e.symm e.symm, submatrix_equiv_mem_unitary.mpr (SetLike.coe_mem U)⟩
    have hA : (A.submatrix e e).submatrix e.symm e.symm = A :=
      (reindex e.toEquiv e.toEquiv).apply_symm_apply A
    have hmatrix : star V.val * A * V.val =
        (star U.val * A.submatrix e e * U.val).submatrix e.symm e.symm := by
      simp only [V, star_eq_conjTranspose, conjTranspose_submatrix]
      rw [← submatrix_mul_equiv _ _ _ e.symm.toEquiv _,
        ← submatrix_mul_equiv _ _ _ e.symm.toEquiv _]
      simp only [OrderIso.coe_toEquiv, hA]
    refine ⟨V, ?_, ?_⟩
    · rw [hmatrix]
      exact hU.submatrix_of_strictMono e.symm.strictMono
    · rw [hmatrix]
      ext i
      simpa using congrFun hdiag (e.symm i)

/-- A square matrix over an `RCLike` field with split characteristic polynomial has an upper
triangular unitary conjugate. -/
theorem exists_unitary_isUpperTriangular_of_splits {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι 𝕜) (hs : A.charpoly.Splits) :
    ∃ U : unitaryGroup ι 𝕜, (star U.val * A * U.val).IsUpperTriangular := by
  have hdeg : (A.charpoly.map (algebraMap 𝕜 𝕜)).natDegree = Fintype.card ι := by
    simp
  obtain ⟨d, hd⟩ := (exists_isRootEnumeration_iff_splits hdeg).mpr (by simpa using hs)
  have hprod : A.charpoly = ∏ i, (X - C (d i)) := by
    simpa [A.charpoly_monic.leadingCoeff] using hd.eq_C_mul_prod_X_sub_C hdeg.le
  obtain ⟨U, hU, -⟩ := (exists_unitary_isUpperTriangular_diag_iff A d).mpr hprod
  exact ⟨U, hU⟩

end Ordered

/-- **Schur triangularization.** Every complex square matrix has an upper triangular unitary
conjugate. -/
theorem exists_unitary_isUpperTriangular {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) : ∃ U : unitaryGroup ι ℂ, (star U.val * A * U.val).IsUpperTriangular :=
  A.exists_unitary_isUpperTriangular_of_splits (IsAlgClosed.splits A.charpoly)

/-- Every representative of the same diagonal torus coset as a unitary triangularizer also
triangularizes the matrix and gives the same ordered diagonal, even with repeated roots. -/
theorem isUpperTriangular_diag_of_inv_mul_mem_unitaryTorus {ι : Type*}
    [Fintype ι] [DecidableEq ι] [LT ι] (A : Matrix ι ι ℂ) {U V : unitaryGroup ι ℂ}
    (hU : (star U.val * A * U.val).IsUpperTriangular) (hV : U⁻¹ * V ∈ TauCeti.unitaryTorus ι) :
    (star V.val * A * V.val).IsUpperTriangular ∧
      (star V.val * A * V.val).diag = (star U.val * A * U.val).diag := by
  obtain ⟨z, hz⟩ := TauCeti.mem_unitaryTorus_iff_exists_unitaryTorusHom.mp hV
  have hVeq : V = U * TauCeti.unitaryTorusHom ι z := by
    rw [hz]
    simp
  have hconj : star V.val * A * V.val =
      diagonal (star fun i ↦ (z i : ℂ)) * (star U.val * A * U.val) *
        diagonal (fun i ↦ (z i : ℂ)) := by
    rw [hVeq]
    simp only [Submonoid.coe_mul, star_mul, TauCeti.coe_unitaryTorusHom, Matrix.mul_assoc]
    rw [star_eq_conjTranspose, diagonal_conjTranspose]
  rw [hconj]
  refine ⟨fun i j hji ↦ ?_, funext fun i ↦ ?_⟩
  · simp [hU hji]
  · simp only [diag_apply, mul_diagonal, diagonal_mul, Pi.star_apply, mul_right_comm _ _ (z i : ℂ),
      Complex.star_def, Circle.conj_coe_mul_self, one_mul]

/-- Two unitary triangularizations with the same distinct diagonal entries in the same order
differ by a diagonal unitary change of basis. -/
theorem inv_mul_mem_unitaryTorus_of_isUpperTriangular {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) {U V : unitaryGroup ι ℂ}
    (hU : (star U.val * A * U.val).IsUpperTriangular)
    (hV : (star V.val * A * V.val).IsUpperTriangular)
    (hdiag : (star U.val * A * U.val).diag = (star V.val * A * V.val).diag)
    (hinj : Function.Injective (star U.val * A * U.val).diag) :
    U⁻¹ * V ∈ TauCeti.unitaryTorus ι := by
  let P := U⁻¹ * V
  have hP : P.val = star U.val * V.val := by
    simp only [P, Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star]
  have hintertwine : (star U.val * A * U.val) * P.val = P.val * (star V.val * A * V.val) := by
    calc
      _ = star U.val * A * V.val := by
        simp only [hP, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc U.val (star U.val), mem_unitaryGroup_iff.mp U.property,
          Matrix.one_mul]
      _ = _ := by
        simp only [hP, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc V.val (star V.val), mem_unitaryGroup_iff.mp V.property,
          Matrix.one_mul]
  have htri := hU.isUpperTriangular_of_mul_eq_mul hV hintertwine fun {i j} hji ↦ by
    rw [← diag_apply (star U.val * A * U.val), ← diag_apply (star V.val * A * V.val), ← hdiag]
    exact hinj.ne hji.ne'
  rw [← TauCeti.comap_toUnits_upperTriangularGroup_eq_unitaryTorus]
  simpa only [Subgroup.mem_comap, TauCeti.UpperTriangularGroup.mem_iff, Unitary.val_toUnits_apply]
    using htri

/-- When the characteristic roots are listed in a fixed order and are distinct, there is a
unique coset of unitary matrices, modulo right multiplication by the diagonal torus, admitting
an upper triangular conjugate with the prescribed diagonal. -/
theorem existsUnique_schurFlag {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (d : ι → ℂ) (hd : A.charpoly = ∏ i, (X - C (d i)))
    (hinj : Function.Injective d) :
    ∃! q : unitaryGroup ι ℂ ⧸ TauCeti.unitaryTorus ι,
      ∃ U : unitaryGroup ι ℂ, QuotientGroup.mk U = q ∧
        (star U.val * A * U.val).IsUpperTriangular ∧ (star U.val * A * U.val).diag = d := by
  obtain ⟨U, hU, hdU⟩ := (exists_unitary_isUpperTriangular_diag_iff A d).mpr hd
  refine ⟨QuotientGroup.mk U, ⟨U, rfl, hU, hdU⟩, ?_⟩
  rintro q ⟨V, rfl, hV, hdV⟩
  have h := A.inv_mul_mem_unitaryTorus_of_isUpperTriangular hU hV (hdU.trans hdV.symm)
    (hdU.symm ▸ hinj)
  exact (QuotientGroup.eq.mpr h).symm

end Matrix
