/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation

/-!
# Exchange matrices with a shared frozen boundary

An indexed family of extended exchange matrices can share one frozen index type while
keeping their mutable vertices disjoint. Their principal block is block diagonal, but
there is only one copy of each frozen row. Mutation at a mutable vertex changes its
own factor, retaining the contributions of all other factors to the same frozen rows.

This construction amalgamates the rectangular mutable columns over the integers. It does
not construct the full rational frozen-frozen block of a weighted ice quiver. No finite-family
assumption is
needed for this projection, because each mutable column belongs to a unique factor.

## Reference

* V. Fock and A. Goncharov, *Cluster X-varieties, amalgamation, and Poisson–Lie groups*,
  §2.2, for amalgamation along frozen vertices.
-/

public section

namespace TauCeti.ExchangeMatrix

open Matrix

variable {A F : Type*} {K : A → Type*} [DecidableEq A]

/-- Assemble extended exchange matrices with a common frozen index type, identifying the
frozen vertices and keeping the mutable indices and their chosen symmetrizers disjoint. -/
def amalgamate (B : ∀ a, ExchangeMatrix (Function.Embedding.inl : K a ↪ K a ⊕ F)) :
    ExchangeMatrix (Function.Embedding.inl : (Σ a, K a) ↪ (Σ a, K a) ⊕ F) where
  matrix := .of fun i j ↦ Sum.elim
    (fun l ↦ blockDiagonal' (fun a ↦ (B a).matrix.submatrix Sum.inl id) l j)
    (fun f ↦ (B j.1).matrix (Sum.inr f) j.2) i
  symmetrizer := fun i ↦ (B i.1).symmetrizer i.2
  isSkewSymmetrizer := by
    constructor
    · rintro ⟨a, k⟩
      exact (B a).isSkewSymmetrizer.pos k
    · rintro ⟨a, i⟩ ⟨b, j⟩
      by_cases h : a = b
      · subst b
        simpa [Matrix.submatrix_apply, Matrix.of_apply, Sum.elim_inl] using
          (B a).isSkewSymmetrizer.mul_apply i j
      · simp [Matrix.submatrix_apply, Matrix.of_apply, Sum.elim_inl,
          blockDiagonal'_apply_ne, h, Ne.symm h]

variable (B C : ∀ a, ExchangeMatrix (Function.Embedding.inl : K a ↪ K a ⊕ F))

/-- Mutable entries in the same factor are the original mutable entries. -/
@[simp] theorem amalgamate_matrix_same (a : A) (i j : K a) :
    (amalgamate B).matrix (Sum.inl ⟨a, i⟩) ⟨a, j⟩ = (B a).matrix (Sum.inl i) j := by
  simp [amalgamate, Matrix.of_apply, Sum.elim_inl, Matrix.submatrix_apply]

/-- No principal entry joins distinct factors. -/
theorem amalgamate_matrix_ne {a b : A} (i : K a) (j : K b) (h : a ≠ b) :
    (amalgamate B).matrix (Sum.inl ⟨a, i⟩) ⟨b, j⟩ = 0 := by
  simp [amalgamate, Matrix.of_apply, Sum.elim_inl, blockDiagonal'_apply_ne, h]

/-- The shared frozen row retains each factor's original columns. -/
@[simp] theorem amalgamate_matrix_frozen (f : F) (a : A) (k : K a) :
    (amalgamate B).matrix (Sum.inr f) ⟨a, k⟩ = (B a).matrix (Sum.inr f) k := by
  rfl

/-- Assembly retains the chosen symmetrizer of each factor. -/
@[simp] theorem amalgamate_symmetrizer (a : A) (k : K a) :
    (amalgamate B).symmetrizer ⟨a, k⟩ = (B a).symmetrizer k := by
  rfl

/-- Restricting to one mutable factor and the shared frozen vertices recovers that factor. -/
@[simp] theorem amalgamate_submatrix (a : A) :
    (amalgamate B).submatrix (Sum.map (Sigma.mk a) id) (Sigma.mk a)
      (fun _ ↦ by simp only [Function.Embedding.inl_apply, Sum.map_inl]) = B a := by
  ext : 1
  · ext (i | f) j <;> simp
  · funext k
    simp

/-- Equal factor columns give equal assembled columns, even at the shared frozen rows.
No equality of the other factor columns or of their chosen symmetrizers is required. -/
theorem amalgamate_column_congr (a : A) (j : K a)
    (h : ∀ i, (B a).matrix i j = (C a).matrix i j) (i : (Σ a, K a) ⊕ F) :
    (amalgamate B).matrix i ⟨a, j⟩ = (amalgamate C).matrix i ⟨a, j⟩ := by
  rcases i with ⟨b, i⟩ | f
  · by_cases hba : b = a
    · subst b
      simpa only [amalgamate_matrix_same] using h (Sum.inl i)
    · rw [amalgamate_matrix_ne B i j hba, amalgamate_matrix_ne C i j hba]
  · simpa only [amalgamate_matrix_frozen] using h (Sum.inr f)

/-- Relabelling the shared frozen boundary commutes with assembly. -/
theorem amalgamate_reindex_frozen {F' : Type*} (e : F ≃ F') :
    amalgamate (fun a ↦ reindex (Equiv.sumCongr (Equiv.refl (K a)) e)
      (Equiv.refl (K a)) (fun _ ↦ by simp) (B a)) =
      reindex (Equiv.sumCongr (Equiv.refl (Σ a, K a)) e)
        (Equiv.refl (Σ a, K a)) (fun _ ↦ by simp) (amalgamate B) := by
  ext : 1
  · ext (⟨a, i⟩ | f) ⟨b, j⟩
    · by_cases h : a = b
      · subst b
        simp [reindex_matrix, Matrix.submatrix_apply]
      · simp [reindex_matrix, Matrix.submatrix_apply, amalgamate_matrix_ne, h]
    · simp [reindex_matrix, Matrix.submatrix_apply]
  · funext ⟨a, k⟩
    simp

section Mutation

variable [DecidableEq F] [∀ a, DecidableEq (K a)]

/-- Mutation in a factor commutes with extracting that factor and its shared frozen rows. -/
theorem amalgamate_mutation_submatrix (a : A) (k : K a) :
    ((amalgamate B).mutation ⟨a, k⟩).submatrix
      (Sum.map (Sigma.mk a) id) (Sigma.mk a)
      (fun _ ↦ by simp only [Function.Embedding.inl_apply, Sum.map_inl]) = (B a).mutation k := by
  have hf : Function.Injective (Sum.map (Sigma.mk (β := K) a) (id : F → F)) :=
    (sigma_mk_injective (β := K)).sumMap Function.injective_id
  rw [(amalgamate B).submatrix_mutation hf
    (fun _ ↦ by simp only [Function.Embedding.inl_apply, Sum.map_inl]), amalgamate_submatrix]

/-- Mutating one factor changes exactly that factor's columns, with only one shared frozen
row present throughout the mutation. -/
theorem mutation_amalgamate (a : A) (k : K a) :
    (amalgamate B).mutation ⟨a, k⟩ =
      amalgamate (Function.update B a ((B a).mutation k)) := by
  have hr := amalgamate_mutation_submatrix B a k
  have hc {b : A} (j : K b) (hba : b ≠ a) (i : (Σ a, K a) ⊕ F) :
      ((amalgamate B).mutation ⟨a, k⟩).matrix i ⟨b, j⟩ =
        (amalgamate B).matrix i ⟨b, j⟩ := by
    simpa only [mutation_matrix] using matrixMutation_apply_of_apply_row_eq_zero
      (row := Function.Embedding.inl) (B := (amalgamate B).matrix) (k := ⟨a, k⟩)
      (j := ⟨b, j⟩) (fun h ↦ hba (congrArg Sigma.fst h))
      (amalgamate_matrix_ne B k j hba.symm) i
  ext : 1
  · ext i ⟨b, j⟩
    by_cases hba : b = a
    · subst b
      rcases i with ⟨b, i⟩ | f
      · by_cases hba : b = a
        · subst b
          have h := congrFun (congrFun (congrArg ExchangeMatrix.matrix hr) (Sum.inl i)) j
          simpa [submatrix_matrix] using h
        · rw [mutation_matrix, matrixMutation_apply_of_apply_col_eq_zero
            (row := Function.Embedding.inl) (B := (amalgamate B).matrix) (k := ⟨a, k⟩)
            (fun h ↦ hba (congrArg Sigma.fst (Sum.inl_injective h)))
            (amalgamate_matrix_ne B i k hba) ⟨a, j⟩]
          rw [amalgamate_matrix_ne B i j hba, amalgamate_matrix_ne _ i j hba]
      · have h := congrFun (congrFun (congrArg ExchangeMatrix.matrix hr) (Sum.inr f)) j
        simpa [submatrix_matrix] using h
    · rw [hc j hba i]
      apply amalgamate_column_congr
      intro l
      simp [hba]
  · funext ⟨b, j⟩
    by_cases hba : b = a
    · subst b
      simp
    · simp [hba]

end Mutation

end TauCeti.ExchangeMatrix
