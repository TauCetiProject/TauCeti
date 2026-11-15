/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-!
# Generalized Cartan matrices

A **generalized Cartan matrix** on an arbitrary index type `I` is an integral matrix `A = (aᵢⱼ)`
satisfying Kac's three axioms:

* `A i i = 2` for every `i`;
* `A i j ≤ 0` for `i ≠ j`;
* `A i j = 0 ↔ A j i = 0`.

Unlike `Matrix.IsFiniteCartan` and `TauCeti.SymmetrizableDatum`, no finiteness, positive
definiteness, or symmetrizability assumption is imposed. Both finite-type Cartan matrices and
symmetrizable generalized Cartan data satisfy `Matrix.IsGeneralizedCartan`, as do the classical
families `CartanMatrix.A`, `CartanMatrix.B`, `CartanMatrix.C`, `CartanMatrix.D`, and the extended
`CartanMatrix.E n` family in every rank (including affine `E 9` and hyperbolic `E 10`).

## Main definitions

* `Matrix.IsGeneralizedCartan`: the predicate that an integral matrix is a generalized Cartan
  matrix.

## Main results

* `Matrix.IsGeneralizedCartan.mul_nonneg` and `Matrix.IsGeneralizedCartan.mul_eq_zero_iff`:
  nonnegativity and vanishing of Cartan products `A i j * A j i`.
* `Matrix.IsGeneralizedCartan.transpose`, `Matrix.IsGeneralizedCartan.submatrix`: closure under
  transposition and principal submatrices.
* `Matrix.IsFiniteCartan.isGeneralizedCartan` and
  `TauCeti.SymmetrizableDatum.isGeneralizedCartan`: forgetful implications.
* `CartanMatrix.isGeneralizedCartan_A`, `CartanMatrix.isGeneralizedCartan_B`,
  `CartanMatrix.isGeneralizedCartan_C`, `CartanMatrix.isGeneralizedCartan_D`,
  `CartanMatrix.isGeneralizedCartan_E`: the standard families are generalized Cartan matrices.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §1.1.
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

/-- On an empty index type, the unique matrix is a generalized Cartan matrix. -/
theorem of_isEmpty [IsEmpty I] (A : Matrix I I ℤ) : A.IsGeneralizedCartan where
  diag := isEmptyElim
  offDiag_nonpos := isEmptyElim
  zero_comm := isEmptyElim

section

variable (hA : A.IsGeneralizedCartan)
include hA

/-- After casting entries to an additive group with one, every diagonal entry is `2`. -/
theorem diag_map (K : Type*) [AddGroupWithOne K] (i : I) :
    A.map (Int.cast : ℤ → K) i i = 2 := by
  simp [hA.diag i]

/-- Every Cartan product `A i j * A j i` is nonnegative: `4` on the diagonal, and a product of two
nonpositive integers off the diagonal. -/
theorem mul_nonneg (i j : I) : 0 ≤ A i j * A j i := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hA.diag i]
  · exact mul_nonneg_of_nonpos_of_nonpos (hA.offDiag_nonpos i j hij)
      (hA.offDiag_nonpos j i hij.symm)

/-- The Cartan product `A i j * A j i` vanishes if and only if `A i j = 0`. -/
theorem mul_eq_zero_iff (i j : I) : A i j * A j i = 0 ↔ A i j = 0 := by
  rw [mul_eq_zero]
  exact or_iff_left_iff_imp.mpr (hA.zero_comm j i).mp

/-- The transpose of a generalized Cartan matrix is a generalized Cartan matrix. -/
protected theorem transpose : Aᵀ.IsGeneralizedCartan where
  diag i := hA.diag i
  offDiag_nonpos i j hij := hA.offDiag_nonpos j i hij.symm
  zero_comm i j := hA.zero_comm j i

/-- Any principal submatrix of a generalized Cartan matrix along an embedding is a generalized
Cartan matrix. -/
protected theorem submatrix (f : J ↪ I) : (A.submatrix f f).IsGeneralizedCartan where
  diag i := hA.diag (f i)
  offDiag_nonpos i j hij := hA.offDiag_nonpos (f i) (f j) (f.injective.ne hij)
  zero_comm i j := hA.zero_comm (f i) (f j)

end

@[simp]
theorem transpose_iff : Aᵀ.IsGeneralizedCartan ↔ A.IsGeneralizedCartan :=
  ⟨fun h ↦ h.transpose, IsGeneralizedCartan.transpose⟩

@[simp]
theorem submatrix_equiv_iff (e : J ≃ I) :
    (A.submatrix e e).IsGeneralizedCartan ↔ A.IsGeneralizedCartan := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.submatrix e.toEmbedding⟩
  have heq : A = (A.submatrix e e).submatrix e.symm e.symm := by
    ext i j
    simp
  rw [heq]
  exact h.submatrix e.symm.toEmbedding

end IsGeneralizedCartan

/-- Every finite-type Cartan matrix is a generalized Cartan matrix. -/
theorem IsFiniteCartan.isGeneralizedCartan {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : A.IsFiniteCartan) : A.IsGeneralizedCartan where
  diag := hA.diag
  offDiag_nonpos := hA.offDiag_nonpos
  zero_comm := hA.zero_comm

end Matrix

namespace TauCeti.SymmetrizableDatum

/-- The underlying matrix of a symmetrizable datum is a generalized Cartan matrix. -/
theorem isGeneralizedCartan {I : Type*} (D : SymmetrizableDatum I) :
    D.cartan.IsGeneralizedCartan where
  diag := D.diag
  offDiag_nonpos := D.offDiag_nonpos
  zero_comm := D.zero_comm

end TauCeti.SymmetrizableDatum

namespace CartanMatrix

/-- The type-`A` Cartan matrix is a generalized Cartan matrix in every rank. -/
theorem isGeneralizedCartan_A (n : ℕ) : (A n).IsGeneralizedCartan where
  diag i := congrFun (A_diag n) i
  offDiag_nonpos := A_apply_le_zero_of_ne n
  zero_comm i j := by rw [(A_isSymm n).apply i j]

/-- The type-`B` Cartan matrix is a generalized Cartan matrix in every rank. -/
theorem isGeneralizedCartan_B (n : ℕ) : (B n).IsGeneralizedCartan where
  diag := B_diag n
  offDiag_nonpos := B_off_diag_nonpos n
  zero_comm i j := by
    simp only [B, Matrix.of_apply, Fin.ext_iff]
    grind

/-- The type-`C` Cartan matrix is a generalized Cartan matrix in every rank. -/
theorem isGeneralizedCartan_C (n : ℕ) : (C n).IsGeneralizedCartan :=
  B_transpose n ▸ (isGeneralizedCartan_B n).transpose

/-- The type-`D` Cartan matrix is a generalized Cartan matrix in every rank. -/
theorem isGeneralizedCartan_D (n : ℕ) : (D n).IsGeneralizedCartan where
  diag := D_diag n
  offDiag_nonpos := D_off_diag_nonpos n
  zero_comm i j := by rw [(D_isSymm n).apply i j]

/-- The generalized `Eₙ` Cartan matrix is a generalized Cartan matrix in every rank, including
affine `E 9` and hyperbolic `E 10`. -/
theorem isGeneralizedCartan_E (n : ℕ) : (E n).IsGeneralizedCartan where
  diag := E_diag n
  offDiag_nonpos := E_off_diag_nonpos n
  zero_comm i j := by rw [(E_isSymm n).apply i j]

/-- The `F₄` Cartan matrix is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_F₄ : F₄.IsGeneralizedCartan where
  diag := F₄_diag
  offDiag_nonpos := F₄_off_diag_nonpos
  zero_comm i j := by fin_cases i <;> fin_cases j <;> decide

/-- The `G₂` Cartan matrix is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_G₂ : G₂.IsGeneralizedCartan where
  diag := G₂_diag
  offDiag_nonpos := G₂_off_diag_nonpos
  zero_comm i j := by fin_cases i <;> fin_cases j <;> decide

end CartanMatrix
