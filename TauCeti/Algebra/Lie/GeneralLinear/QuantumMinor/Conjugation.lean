/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Comatrix
import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.BasisChange
import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.MatrixUnitLieHom
import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Polynomial
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Polynomial

/-!
# Change of basis for quantum cofactors

The matrix of transposed signed quantum cofactors transforms by the same scalar similarity as
both the generator matrix and its diagonal spectral shifts. Consequently the contraction of
these cofactors against a vector and a covector is independent of the scalar basis. Neither the
full quantum determinant nor the shifted generator matrix needs to be invertible.

The contracted identity is the change of basis for `C(u)` in L. Alpöge's formalization of the
Riemann hypothesis for Dirichlet L-functions, `PI.QnHermHaar.glConj`. The proof here uses the
comatrix identity over a polynomial ring, so that the shifted generator matrix can be cancelled
before evaluating the central indeterminate at zero.
-/

public section

namespace Matrix

open Polynomial

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A] {n : ℕ}

/-- The comatrix of the quantum minor on all rows and columns, with the cofactors transposed. -/
noncomputable def quantumComatrix (E : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (u : K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  of fun i j ↦ (-1 : ℤ) ^ (i.val + j.val) • E.quantumMinor u (j.removeNth id) (i.removeNth id)

/-- The `(i,j)` entry deletes row `j` and column `i` and applies the cofactor sign. -/
@[simp] theorem quantumComatrix_apply (E : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (u : K)
    (i j : Fin (n + 1)) :
    E.quantumComatrix u i j =
      (-1 : ℤ) ^ (i.val + j.val) • E.quantumMinor u (j.removeNth id) (i.removeNth id) := (rfl)

/-- The comatrix multiplied on the right by the final shifted generator matrix is the scalar
matrix of the full quantum determinant. -/
theorem quantumComatrix_mul_add_scalar (E : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (hE : E.HasMatrixUnitLieRelations) (u : K) :
    E.quantumComatrix u * (E + scalar _ (algebraMap K A (u - (n : K)))) =
      scalar _ (E.quantumMinor u id id) := by
  ext i l
  simpa only [Matrix.mul_apply, Matrix.add_apply, scalar_apply, diagonal_apply,
    quantumComatrix_apply, smul_mul_assoc, add_comm, id_eq]
    using E.quantumMinor_comatrix hE u id id i l

/-- Quantum cofactors commute with algebra homomorphisms on the coefficient algebra. -/
@[simp] theorem _root_.AlgHom.map_quantumComatrix {B : Type*} [Ring B] [Algebra K B]
    (f : A →ₐ[K] B) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (u : K) :
    (E.quantumComatrix u).map f = (E.map f).quantumComatrix u := by
  ext i j
  simp

/-- Similarity by scalar matrices, in the convention for changing a family of matrix units. -/
private theorem scalar_basis_change_apply {ι : Type*} [Fintype ι]
    (E : Matrix ι ι A) (P Q : Matrix ι ι K) (i j : ι) :
    (Pᵀ.map (algebraMap K A) * E * Qᵀ.map (algebraMap K A)) i j =
      ∑ c, ∑ d, (P c i * Q j d) • E c d := by
  simp only [Matrix.mul_apply, map_apply, transpose_apply, Finset.sum_mul, Algebra.smul_def,
    map_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun d _ ↦ by
    rw [mul_assoc, ← Algebra.commutes (Q j d) (E c d), mul_assoc]

/-- Over a polynomial coefficient algebra the last shifted matrix is right cancellable. -/
private theorem quantumComatrix_conj_with_X
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (hE : E.HasMatrixUnitLieRelations) (u : K)
    (P Q : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hQP : Q * P = 1) :
    let S := Pᵀ.map (algebraMap K A[X])
    let T := Qᵀ.map (algebraMap K A[X])
    let F := E.map C + diagonal (fun _ ↦ (X : A[X]))
    (S * F * T).quantumComatrix u = S * F.quantumComatrix u * T := by
  intro S T F
  let D := scalar (Fin (n + 1)) (algebraMap K A[X] (u - (n : K)))
  have hinv (U V : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hUV : U * V = 1) :
      Vᵀ.map (algebraMap K A[X]) * Uᵀ.map (algebraMap K A[X]) = 1 := by
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) K ↦
      Mᵀ.map (algebraMap K A[X])) hUV
    simpa only [transpose_mul, ← Matrix.map_mul, transpose_one, Matrix.map_one _ (map_zero _)
      (map_one _)] using h
  have hST : S * T = 1 := hinv Q P hQP
  have hTS : T * S = 1 := hinv P Q (mul_eq_one_comm.mp hQP)
  have hF : F.HasMatrixUnitLieRelations := hE.map_C_add_diagonal_X
  have hEq : S * F * T = of fun i j ↦ ∑ c, ∑ d, (P c i * Q j d) • F c d :=
    Matrix.ext (scalar_basis_change_apply F P Q)
  have hG : (S * F * T).HasMatrixUnitLieRelations :=
    hEq ▸ hF.change_of_basis P Q hQP
  have hdet : (S * F * T).quantumMinor u id id = F.quantumMinor u id id :=
    hEq ▸ F.quantumMinor_conj_of_mul_eq_one hF u P Q hQP
  have hshift : S * F * T + D = S * (F + D) * T := by
    have hS : Commute D S := scalar_commute _ (Algebra.commutes (u - (n : K))) _
    rw [mul_add S F D, add_mul, ← hS.eq, mul_assoc D S T, hST, mul_one]
  have hreg : IsRightRegular (F + D) := by
    have hbase := isRightRegular_map_C_add_diagonal_X
      (E + scalar _ (algebraMap K A (u - (n : K))))
    convert hbase using 1
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;>
      simp [F, D, hij, add_right_comm, Polynomial.algebraMap_apply]
  have h₁ : (S * F * T).quantumComatrix u * (S * (F + D) * T) =
      scalar _ (F.quantumMinor u id id) := by
    rw [← hshift, quantumComatrix_mul_add_scalar _ hG, hdet]
  have h₂ : F.quantumComatrix u * (F + D) = scalar _ (F.quantumMinor u id id) :=
    quantumComatrix_mul_add_scalar F hF u
  have hcomm : Commute (scalar (Fin (n + 1)) (F.quantumMinor u id id)) S := by
    exact scalar_commute_iff.mpr (Matrix.ext fun i j ↦
      (Algebra.commutes (P j i) (F.quantumMinor u id id)).symm)
  have hprod : ((S * F * T).quantumComatrix u * S) * (F + D) * T =
      ((S * F.quantumComatrix u * T) * S) * (F + D) * T := by
    calc
      _ = scalar _ (F.quantumMinor u id id) := by simpa only [mul_assoc] using h₁
      _ = (S * (F.quantumComatrix u * (F + D))) * T := by
        rw [h₂, ← hcomm.eq, mul_assoc, hST, mul_one]
      _ = _ := by
        rw [mul_assoc (S * F.quantumComatrix u) T S, hTS, mul_one]
        simp only [mul_assoc]
  have hc := hreg (by simpa only [mul_assoc, hTS, mul_one] using congrArg (· * S) hprod :
    ((S * F * T).quantumComatrix u * S) * (F + D) =
      ((S * F.quantumComatrix u * T) * S) * (F + D))
  simpa only [mul_assoc, hST, mul_one] using congrArg (· * T) hc

/-- Under the scalar change of basis `E' = Pᵀ E Qᵀ` with `Q * P = 1`, the comatrix is
transformed by the same similarity. The scalar matrices act via the coefficient algebra map. -/
theorem quantumComatrix_conj_of_mul_eq_one
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (hE : E.HasMatrixUnitLieRelations) (u : K)
    (P Q : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hQP : Q * P = 1) :
    (Pᵀ.map (algebraMap K A) * E * Qᵀ.map (algebraMap K A)).quantumComatrix u =
      Pᵀ.map (algebraMap K A) * E.quantumComatrix u * Qᵀ.map (algebraMap K A) := by
  let f : A[X] →ₐ[K] A :=
    { constantCoeff with
      commutes' k := by simp [Polynomial.algebraMap_apply] }
  have hF : (E.map C + diagonal (fun _ ↦ (X : A[X]))).map f = E := by
    ext i j
    by_cases hij : i = j <;> simp [f, hij]
  have hP (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
      (M.map (algebraMap K A[X])).map f = M.map (algebraMap K A) := by
    apply Matrix.ext
    intro i j
    exact f.commutes (M i j)
  have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) A[X] ↦ M.map f)
    (quantumComatrix_conj_with_X E hE u P Q hQP)
  simpa only [AlgHom.map_quantumComatrix, ← AlgHom.coe_toRingHom, Matrix.map_mul,
    AlgHom.coe_toRingHom, hP, hF] using h

/-- The scalar contraction of the signed cofactors is basis independent. Here `x` is the
column vector and `ξ` the row covector: in the changed basis they are `Q *ᵥ x` and `ξ ᵥ* P`. -/
theorem quantumComatrix_contraction_conj_of_mul_eq_one
    (E : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (hE : E.HasMatrixUnitLieRelations) (u : K)
    (P Q : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hQP : Q * P = 1)
    (x ξ : Fin (n + 1) → K) :
    ((algebraMap K A ∘ (Q *ᵥ x)) ᵥ*
      (of fun i j ↦ ∑ c, ∑ d, (P c i * Q j d) • E c d).quantumComatrix u) ⬝ᵥ
      (algebraMap K A ∘ (ξ ᵥ* P)) =
    ((algebraMap K A ∘ x) ᵥ* E.quantumComatrix u) ⬝ᵥ (algebraMap K A ∘ ξ) := by
  let S := Pᵀ.map (algebraMap K A)
  let T := Qᵀ.map (algebraMap K A)
  have hTS : T * S = 1 := by
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) K ↦
      Mᵀ.map (algebraMap K A)) (mul_eq_one_comm.mp hQP)
    simpa only [transpose_mul, ← Matrix.map_mul, transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _), S, T] using h
  have hmat : (of fun i j ↦ ∑ c, ∑ d, (P c i * Q j d) • E c d) = S * E * T :=
    (Matrix.ext (scalar_basis_change_apply E P Q)).symm
  have hx : algebraMap K A ∘ (Q *ᵥ x) = (algebraMap K A ∘ x) ᵥ* T := by
    rw [← vecMul_transpose]
    exact funext fun i ↦ (algebraMap K A).map_vecMul _ _ i
  have hξ : algebraMap K A ∘ (ξ ᵥ* P) = S *ᵥ (algebraMap K A ∘ ξ) := by
    funext i
    rw [Function.comp_apply, RingHom.map_vecMul]
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, map_apply, S, transpose_apply,
      Function.comp_apply]
    exact Finset.sum_congr rfl fun j _ ↦ Algebra.commutes (ξ j) ((algebraMap K A) (P j i))
  rw [hx, hξ, hmat, quantumComatrix_conj_of_mul_eq_one E hE u P Q hQP]
  have hleft : ((algebraMap K A ∘ x) ᵥ* T) ᵥ* (S * E.quantumComatrix u * T) =
      ((algebraMap K A ∘ x) ᵥ* E.quantumComatrix u) ᵥ* T := by
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_vecMul _ T S, hTS, vecMul_one]
  rw [hleft, ← dotProduct_mulVec, mulVec_mulVec, hTS, one_mulVec]

end Matrix
