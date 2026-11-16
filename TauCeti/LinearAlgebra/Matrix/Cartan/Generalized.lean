/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-!
# Generalized Cartan matrices

An integral matrix `A : Matrix I I ℤ` on an arbitrary index type `I` satisfies
`Matrix.IsGeneralizedCartan` if `A i i = 2`, `A i j ≤ 0` for `i ≠ j`, and `A i j = 0 ↔ A j i = 0`
(Kac, *Infinite-dimensional Lie algebras*, §1.1), without finiteness or symmetrizability
assumptions. We prove nonnegativity and vanishing of Cartan products `A i j * A j i`, closure
under transposition and principal submatrices, and instances for `Matrix.IsFiniteCartan`,
`TauCeti.SymmetrizableDatum`, and the standard Cartan families `A`, `B`, `C`, `D`, `E`, `F₄`, `G₂`.
-/

public section

namespace Matrix

/-- An integral square matrix `A` is a **generalized Cartan matrix** if its diagonal entries are
`2`, its off-diagonal entries are nonpositive, and its zero pattern is symmetric. -/
structure IsGeneralizedCartan {I : Type*} (A : Matrix I I ℤ) : Prop where
  /-- Every diagonal entry is `2`. -/
  diag : ∀ i, A i i = 2
  /-- Every off-diagonal entry is nonpositive. -/
  offDiag_nonpos : ∀ i j, i ≠ j → A i j ≤ 0
  /-- Vanishing is symmetric across the diagonal. -/
  zero_comm : ∀ i j, A i j = 0 ↔ A j i = 0

namespace IsGeneralizedCartan

variable {I J : Type*} {A : Matrix I I ℤ}

theorem of_isEmpty [IsEmpty I] (A : Matrix I I ℤ) : A.IsGeneralizedCartan :=
  ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩

section

variable (hA : A.IsGeneralizedCartan)
include hA

theorem diag_map (K : Type*) [AddGroupWithOne K] (i : I) :
    A.map (Int.cast : ℤ → K) i i = 2 := by simp [hA.diag i]

/-- Every Cartan product `A i j * A j i` is nonnegative. -/
theorem mul_nonneg (i j : I) : 0 ≤ A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hA.diag i]
  · exact mul_nonneg_of_nonpos_of_nonpos (hA.offDiag_nonpos i j hij)
      (hA.offDiag_nonpos j i hij.symm)

theorem mul_eq_zero_iff (i j : I) : A i j * A j i = 0 ↔ A i j = 0 :=
  mul_eq_zero.trans (or_iff_left_iff_imp.mpr (hA.zero_comm j i).mp)

protected theorem transpose : Aᵀ.IsGeneralizedCartan :=
  ⟨fun i ↦ hA.diag i, fun i j hij ↦ hA.offDiag_nonpos j i hij.symm, fun i j ↦ hA.zero_comm j i⟩

protected theorem submatrix (f : J ↪ I) : (A.submatrix f f).IsGeneralizedCartan :=
  ⟨fun i ↦ hA.diag (f i), fun i j hij ↦ hA.offDiag_nonpos (f i) (f j) (f.injective.ne hij),
    fun i j ↦ hA.zero_comm (f i) (f j)⟩

end

@[simp]
theorem transpose_iff : Aᵀ.IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h ↦ h.transpose, IsGeneralizedCartan.transpose⟩

@[simp]
theorem submatrix_equiv_iff (e : J ≃ I) :
    (A.submatrix e e).IsGeneralizedCartan ↔ A.IsGeneralizedCartan := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.submatrix e.toEmbedding⟩
  simpa [Matrix.submatrix_submatrix] using h.submatrix e.symm.toEmbedding

end IsGeneralizedCartan

theorem IsFiniteCartan.isGeneralizedCartan {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : A.IsFiniteCartan) : A.IsGeneralizedCartan :=
  ⟨hA.diag, hA.offDiag_nonpos, hA.zero_comm⟩

end Matrix

namespace TauCeti.SymmetrizableDatum

theorem isGeneralizedCartan {I : Type*} (D : SymmetrizableDatum I) :
    D.cartan.IsGeneralizedCartan :=
  ⟨D.diag, D.offDiag_nonpos, D.zero_comm⟩

end TauCeti.SymmetrizableDatum

namespace CartanMatrix

theorem isGeneralizedCartan_A (n : ℕ) : (A n).IsGeneralizedCartan :=
  ⟨congrFun (A_diag n), A_apply_le_zero_of_ne n, fun i j ↦ by rw [(A_isSymm n).apply i j]⟩

theorem isGeneralizedCartan_B (n : ℕ) : (B n).IsGeneralizedCartan :=
  ⟨B_diag n, B_off_diag_nonpos n, fun i j ↦ by simp only [B, Matrix.of_apply, Fin.ext_iff]; grind⟩

theorem isGeneralizedCartan_C (n : ℕ) : (C n).IsGeneralizedCartan :=
  B_transpose n ▸ (isGeneralizedCartan_B n).transpose

theorem isGeneralizedCartan_D (n : ℕ) : (D n).IsGeneralizedCartan :=
  ⟨D_diag n, D_off_diag_nonpos n, fun i j ↦ by rw [(D_isSymm n).apply i j]⟩

theorem isGeneralizedCartan_E (n : ℕ) : (E n).IsGeneralizedCartan :=
  ⟨E_diag n, E_off_diag_nonpos n, fun i j ↦ by rw [(E_isSymm n).apply i j]⟩

theorem isGeneralizedCartan_F₄ : F₄.IsGeneralizedCartan :=
  ⟨F₄_diag, F₄_off_diag_nonpos, fun i j ↦ by fin_cases i <;> fin_cases j <;> decide⟩

theorem isGeneralizedCartan_G₂ : G₂.IsGeneralizedCartan :=
  ⟨G₂_diag, G₂_off_diag_nonpos, fun i j ↦ by fin_cases i <;> fin_cases j <;> decide⟩

end CartanMatrix
