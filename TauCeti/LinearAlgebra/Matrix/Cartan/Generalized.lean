/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Generalized Cartan matrices

Basic API for Mathlib's `Matrix.IsGeneralizedCartan` (`A i i = 2`, `A i j ≤ 0` for `i ≠ j`, and
`A i j = 0 ↔ A j i = 0`, following Kac, *Infinite-dimensional Lie algebras*, §1.1): subsingleton
and empty index types, nonnegativity and vanishing of Cartan products `A i j * A j i`, closure
under transposition and principal submatrices, and proofs that the affine `A₁⁽¹⁾` matrix
`!![2, -2; -2, 2]` and the standard Cartan families `A`, `B`, `C`, `D`, `E`, `F₄`, `G₂` satisfy
`Matrix.IsGeneralizedCartan`.
-/

public section

namespace Matrix

namespace IsGeneralizedCartan

variable {I J : Type*} {A : Matrix I I ℤ}

/-- On a subsingleton index type, any integral matrix with diagonal entries `2` is a generalized
Cartan matrix. -/
theorem of_subsingleton [Subsingleton I] (hdiag : ∀ i, A i i = 2) : A.IsGeneralizedCartan :=
  ⟨hdiag, fun i j hij ↦ absurd (Subsingleton.elim i j) hij,
    fun i j ↦ by rw [Subsingleton.elim i j]⟩

/-- On an empty index type, every integral matrix is a generalized Cartan matrix. -/
theorem of_isEmpty [IsEmpty I] (A : Matrix I I ℤ) : A.IsGeneralizedCartan :=
  of_subsingleton isEmptyElim

section
variable (hA : A.IsGeneralizedCartan)
include hA

/-- Every Cartan product `A i j * A j i` is nonnegative. -/
protected theorem mul_nonneg (i j : I) : 0 ≤ A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hA.diag i]
  · exact mul_nonneg_of_nonpos_of_nonpos (hA.offDiag_nonpos i j hij)
      (hA.offDiag_nonpos j i hij.symm)

/-- A Cartan product `A i j * A j i` vanishes if and only if `A i j = 0`. -/
protected theorem mul_eq_zero_iff (i j : I) : A i j * A j i = 0 ↔ A i j = 0 :=
  mul_eq_zero.trans (or_iff_left_iff_imp.mpr (hA.zero_comm j i).mp)

/-- The transpose of a generalized Cartan matrix is a generalized Cartan matrix. -/
protected theorem transpose : Aᵀ.IsGeneralizedCartan :=
  ⟨fun i ↦ hA.diag i, fun i j hij ↦ hA.offDiag_nonpos j i hij.symm, fun i j ↦ hA.zero_comm j i⟩

/-- Any principal submatrix of a generalized Cartan matrix along an embedding is a generalized
Cartan matrix. -/
protected theorem submatrix (f : J ↪ I) : (A.submatrix f f).IsGeneralizedCartan :=
  ⟨fun i ↦ hA.diag (f i), fun i j hij ↦ hA.offDiag_nonpos (f i) (f j) (f.injective.ne hij),
    fun i j ↦ hA.zero_comm (f i) (f j)⟩
end

@[simp] theorem transpose_iff : Aᵀ.IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h ↦ h.transpose, IsGeneralizedCartan.transpose⟩

@[simp] theorem submatrix_equiv_iff (e : J ≃ I) :
    (A.submatrix e e).IsGeneralizedCartan ↔ A.IsGeneralizedCartan := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.submatrix e.toEmbedding⟩
  simpa [Matrix.submatrix_submatrix] using h.submatrix e.symm.toEmbedding

end IsGeneralizedCartan

/-- The affine `A₁⁽¹⁾` matrix `!![2, -2; -2, 2]` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_two_neg_two :
    (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsGeneralizedCartan :=
  ⟨fun i ↦ by fin_cases i <;> decide, fun i j _ ↦ by fin_cases i <;> fin_cases j <;> simp_all,
    fun i j ↦ by fin_cases i <;> fin_cases j <;> decide⟩

end Matrix

namespace CartanMatrix
/-- `CartanMatrix.A n` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_A (n : ℕ) : (A n).IsGeneralizedCartan :=
  ⟨congrFun (A_diag n), A_apply_le_zero_of_ne n, fun i j ↦ by rw [(A_isSymm n).apply i j]⟩
/-- `CartanMatrix.B n` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_B (n : ℕ) : (B n).IsGeneralizedCartan :=
  ⟨B_diag n, B_off_diag_nonpos n, fun i j ↦ by simp only [B, Matrix.of_apply, Fin.ext_iff]; grind⟩
/-- `CartanMatrix.C n` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_C (n : ℕ) : (C n).IsGeneralizedCartan :=
  B_transpose n ▸ (isGeneralizedCartan_B n).transpose
/-- `CartanMatrix.D n` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_D (n : ℕ) : (D n).IsGeneralizedCartan :=
  ⟨D_diag n, D_off_diag_nonpos n, fun i j ↦ by rw [(D_isSymm n).apply i j]⟩
/-- `CartanMatrix.E n` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_E (n : ℕ) : (E n).IsGeneralizedCartan :=
  ⟨E_diag n, E_off_diag_nonpos n, fun i j ↦ by rw [(E_isSymm n).apply i j]⟩
/-- `CartanMatrix.F₄` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_F₄ : F₄.IsGeneralizedCartan :=
  ⟨F₄_diag, F₄_off_diag_nonpos, fun i j ↦ by fin_cases i <;> fin_cases j <;> decide⟩
/-- `CartanMatrix.G₂` is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_G₂ : G₂.IsGeneralizedCartan :=
  ⟨G₂_diag, G₂_off_diag_nonpos, fun i j ↦ by fin_cases i <;> fin_cases j <;> decide⟩
end CartanMatrix
