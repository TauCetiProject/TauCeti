/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Symmetrizable

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
* `Matrix.IsGeneralizedCartan.submatrix`, `Matrix.isGeneralizedCartan_reindex`,
  `Matrix.IsGeneralizedCartan.fromBlocks`: closure under principal submatrices along an embedding,
  reindexing along an equivalence, and block-diagonal direct sums.
* `TauCeti.SymmetrizableDatum.isGeneralizedCartan`: symmetrizable Cartan data have generalized
  Cartan underlying matrices.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §1.1.
-/

public section

namespace Matrix

instance instDecidablePredIsGeneralizedCartan {ι : Type*} [Fintype ι] [DecidableEq ι] :
    DecidablePred (IsGeneralizedCartan (ι := ι)) :=
  fun M =>
    let m : ι → ι → ℤ := Matrix.of.symm M
    decidable_of_iff
      ((∀ i, m i i = 2) ∧ (∀ i j, i ≠ j → m i j ≤ 0) ∧ ∀ i j, m i j = 0 ↔ m j i = 0)
      ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

namespace IsGeneralizedCartan

variable {I J I' : Type*} {M : Matrix I I ℤ} {N : Matrix J J ℤ}

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

/-- Reindexing a generalized Cartan matrix along a bijection gives a generalized Cartan matrix. -/
theorem reindex (hM : M.IsGeneralizedCartan) (e : I ≃ I') :
    (M.reindex e e).IsGeneralizedCartan :=
  hM.submatrix e.symm.toEmbedding

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

/-- Reindexing a matrix along an equivalence preserves and reflects the generalized Cartan
property. -/
theorem isGeneralizedCartan_reindex {I I' : Type*} {M : Matrix I I ℤ} (e : I ≃ I') :
    (M.reindex e e).IsGeneralizedCartan ↔ M.IsGeneralizedCartan :=
  ⟨fun h => by simpa using h.reindex e.symm, fun h => h.reindex e⟩

end Matrix

namespace TauCeti.SymmetrizableDatum

/-- The underlying matrix of a symmetrizable Cartan datum is a generalized Cartan matrix. -/
theorem isGeneralizedCartan {I : Type*} (A : SymmetrizableDatum I) :
    A.cartan.IsGeneralizedCartan where
  diag := A.diag
  offDiag_nonpos := A.offDiag_nonpos
  zero_comm := A.zero_comm

end TauCeti.SymmetrizableDatum

/-! ### Examples -/

/-- The affine Cartan matrix `A₁⁽¹⁾` is a singular generalized Cartan matrix. -/
example : (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsGeneralizedCartan ∧
    (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).det = 0 :=
  ⟨by decide, by decide⟩

/-- Violating symmetric vanishing of entries prevents a matrix from being generalized Cartan. -/
example : ¬ (!![2, -1; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsGeneralizedCartan := by
  decide
