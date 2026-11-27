/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# Generalized Cartan matrices

API lemmas and instances for Mathlib's `Matrix.IsGeneralizedCartan`, the predicate that an
integral square matrix `M` on an index type `I` has diagonal entries `2`, nonpositive off-diagonal
entries, and vanishing entries in symmetric positions: `M i j = 0 ↔ M j i = 0`. No finiteness
assumption on `I` and no symmetrizability assumption on `M` is imposed.

These three axioms are the exact matrix hypotheses needed for the triangular decomposition of the
Serre-presented Kac–Moody algebra of a realization (`TauCeti.KacMoody.PresentedLieAlgebra`) and for
the injectivity of its Cartan map, whereas constructing an invariant bilinear form additionally uses
a symmetrizer (`TauCeti.SymmetrizableDatum`).

## Main results

* `Matrix.isGeneralizedCartan_transpose`: transposition preserves generalized Cartan matrices.
* `Matrix.IsGeneralizedCartan.submatrix`, `Matrix.isGeneralizedCartan_submatrix_equiv`,
  `Matrix.IsGeneralizedCartan.fromBlocks`: closure under principal submatrices along an embedding,
  restriction along an equivalence, and block-diagonal direct sums.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §1.1.
-/

public section

namespace Matrix

instance instDecidablePredIsGeneralizedCartan {ι : Type*} [Fintype ι] [DecidableEq ι] :
    DecidablePred (IsGeneralizedCartan (ι := ι)) :=
  fun M =>
    letI (_i _j : ι) : Decidable (_i ≠ _j → M _i _j ≤ 0) := inferInstance
    letI (_i _j : ι) : Decidable (M _i _j = 0 ↔ M _j _i = 0) := inferInstance
    decidable_of_iff
      ((∀ i, M i i = 2) ∧ (∀ i j, i ≠ j → M i j ≤ 0) ∧ ∀ i j, M i j = 0 ↔ M j i = 0)
      ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun h => ⟨h.diag, h.offDiag_nonpos, h.zero_comm⟩⟩

namespace IsGeneralizedCartan

variable {I J : Type*} {M : Matrix I I ℤ} {N : Matrix J J ℤ}

/-- On an empty index type, every matrix is vacuously a generalized Cartan matrix. -/
theorem of_isEmpty [IsEmpty I] (M : Matrix I I ℤ) : M.IsGeneralizedCartan where
  diag := isEmptyElim
  offDiag_nonpos := isEmptyElim
  zero_comm := isEmptyElim

/-- The transpose of a generalized Cartan matrix is a generalized Cartan matrix. -/
protected theorem transpose (hM : M.IsGeneralizedCartan) : Mᵀ.IsGeneralizedCartan where
  diag i := hM.diag i
  offDiag_nonpos i j hij := hM.offDiag_nonpos j i hij.symm
  zero_comm i j := hM.zero_comm j i

/-- Restricting a generalized Cartan matrix along an embedding of index types gives a generalized
Cartan matrix; for the inclusion of a subset this is the Levi submatrix. -/
theorem submatrix (hM : M.IsGeneralizedCartan) (f : J ↪ I) :
    (M.submatrix f f).IsGeneralizedCartan where
  diag i := hM.diag (f i)
  offDiag_nonpos i j hij := hM.offDiag_nonpos (f i) (f j) (f.injective.ne hij)
  zero_comm i j := hM.zero_comm (f i) (f j)

/-- The block-diagonal direct sum of two generalized Cartan matrices is a generalized Cartan
matrix. -/
theorem fromBlocks (hM : M.IsGeneralizedCartan) (hN : N.IsGeneralizedCartan) :
    (Matrix.fromBlocks M 0 0 N).IsGeneralizedCartan where
  diag := by rintro (i | j) <;> simp [hM.diag, hN.diag]
  offDiag_nonpos := by
    rintro (i | i) (j | j) hij
    · exact hM.offDiag_nonpos i j (hij ∘ congrArg Sum.inl)
    · simp
    · simp
    · exact hN.offDiag_nonpos i j (hij ∘ congrArg Sum.inr)
  zero_comm := by rintro (i | i) (j | j) <;> simp [hM.zero_comm, hN.zero_comm]

end IsGeneralizedCartan

/-- Transposing a matrix preserves and reflects the generalized Cartan property. -/
@[simp]
theorem isGeneralizedCartan_transpose {I : Type*} {M : Matrix I I ℤ} :
    Mᵀ.IsGeneralizedCartan ↔ M.IsGeneralizedCartan :=
  ⟨fun h => h.transpose, IsGeneralizedCartan.transpose⟩

/-- Restricting a matrix along an equivalence of index types preserves and reflects the
generalized Cartan property. -/
@[simp]
theorem isGeneralizedCartan_submatrix_equiv {I I' : Type*} {M : Matrix I I ℤ} (e : I' ≃ I) :
    (M.submatrix e e).IsGeneralizedCartan ↔ M.IsGeneralizedCartan :=
  ⟨fun h => by simpa [Matrix.submatrix_submatrix] using h.submatrix e.symm.toEmbedding,
    fun h => h.submatrix e.toEmbedding⟩

end Matrix

/-! ### Examples -/

/-- The affine Cartan matrix `A₁⁽¹⁾` is a singular generalized Cartan matrix. -/
example : (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsGeneralizedCartan ∧
    (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det = 0 :=
  ⟨by decide, by decide⟩

/-- Violating symmetric vanishing of entries prevents a matrix from being generalized Cartan. -/
example : ¬ (!![2, -1; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsGeneralizedCartan := by
  decide
