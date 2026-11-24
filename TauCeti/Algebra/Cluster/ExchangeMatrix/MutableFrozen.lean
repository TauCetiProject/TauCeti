/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
public import TauCeti.Logic.Equiv.Set
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Standard

/-!
# Standard mutable and frozen row presentations

Every embedding of mutable rows gives a standard presentation with the mutable rows first
and the complementary frozen rows second. This presentation preserves the chosen symmetrizer,
principal block and mutation. An extended exchange matrix is equivalently its square principal
exchange matrix together with an arbitrary matrix of frozen rows. Both constructions allow
infinite row sets and degenerate mutable index types.

The index decomposition reuses `Equiv.ofInjectiveSumCompl`; matrix transport
is the existing `ExchangeMatrix.reindex`. No extra exchange-matrix carrier is introduced.

## References

* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and double
  Bruhat cells*, Duke Math. J. 126 (2005), §1.
-/

public noncomputable section

namespace TauCeti.ExchangeMatrix

open Matrix

variable {I K : Type*} (row : K ↪ I)

/-- Present an arbitrary mutable embedding as the inclusion of the first summand; the
second summand is exactly the complement of the original mutable image. -/
def mutableFrozenEquiv : ExchangeMatrix row ≃
    ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ ((Set.range row)ᶜ : Set I)) :=
  reindex (Equiv.ofInjectiveSumCompl row row.injective).symm (Equiv.refl K)
    (fun k ↦ Equiv.ofInjectiveSumCompl_symm_apply row.injective k)

/-- Standardization displays the full matrix as its principal block above its frozen rows. -/
@[simp]
theorem mutableFrozenEquiv_matrix (B : ExchangeMatrix row) :
    (mutableFrozenEquiv row B).matrix =
      Matrix.fromRows B.principal.matrix (B.matrix.submatrix Subtype.val id) := by
  calc
    _ = B.matrix.submatrix (Equiv.ofInjectiveSumCompl row row.injective) id :=
      B.reindex_matrix (Equiv.ofInjectiveSumCompl row row.injective).symm (Equiv.refl K)
        (fun k ↦ Equiv.ofInjectiveSumCompl_symm_apply row.injective k)
    _ = _ := by
      ext (i | a) j <;> simp [principal_matrix]

/-- The chosen symmetrizer is unchanged by the standard row presentation. -/
@[simp]
theorem mutableFrozenEquiv_symmetrizer (B : ExchangeMatrix row) :
    (mutableFrozenEquiv row B).symmetrizer = B.symmetrizer := by
  exact B.reindex_symmetrizer (Equiv.ofInjectiveSumCompl row row.injective).symm (Equiv.refl K)
    (fun k ↦ Equiv.ofInjectiveSumCompl_symm_apply row.injective k)

/-- The inverse standardization reindexes the standard matrix back to the original rows. -/
@[simp]
theorem mutableFrozenEquiv_symm_matrix
    (C : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ ((Set.range row)ᶜ : Set I))) :
    ((mutableFrozenEquiv row).symm C).matrix =
      C.matrix.submatrix (Equiv.ofInjectiveSumCompl row row.injective).symm id := by
  have h := reindex_symm_apply (Equiv.ofInjectiveSumCompl row row.injective).symm
    (Equiv.refl K) (fun k ↦ Equiv.ofInjectiveSumCompl_symm_apply row.injective k) C
  simpa only [mutableFrozenEquiv, submatrix_matrix, Equiv.coe_refl] using
    congrArg ExchangeMatrix.matrix h

/-- The inverse standardization preserves the chosen symmetrizer. -/
@[simp]
theorem mutableFrozenEquiv_symm_symmetrizer
    (C : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ ((Set.range row)ᶜ : Set I))) :
    ((mutableFrozenEquiv row).symm C).symmetrizer = C.symmetrizer := by
  have h := reindex_symm_apply (Equiv.ofInjectiveSumCompl row row.injective).symm
    (Equiv.refl K) (fun k ↦ Equiv.ofInjectiveSumCompl_symm_apply row.injective k) C
  simpa only [mutableFrozenEquiv, submatrix_symmetrizer, Equiv.coe_refl, Function.comp_id] using
    congrArg ExchangeMatrix.symmetrizer h

/-- Standardization leaves the principal exchange matrix unchanged. -/
@[simp]
theorem mutableFrozenEquiv_principal (B : ExchangeMatrix row) :
    (mutableFrozenEquiv row B).principal = B.principal := by
  simpa only [mutableFrozenEquiv, reindex_refl, Equiv.refl_apply] using
    B.principal_reindex (Equiv.ofInjectiveSumCompl row row.injective).symm (Equiv.refl K)
      (fun k ↦ Equiv.ofInjectiveSumCompl_symm_apply row.injective k)

/-- An extended exchange matrix is exactly a principal exchange matrix and an unconstrained
frozen-row matrix, with the original row embedding retained by the inverse construction. -/
def principalFrozenEquiv : ExchangeMatrix row ≃
    ExchangeMatrix (Function.Embedding.refl K) × Matrix ((Set.range row)ᶜ : Set I) K ℤ :=
  (mutableFrozenEquiv row).trans (standardPartsEquiv K _)

/-- The forward decomposition consists of the actual principal block and actual frozen rows. -/
@[simp]
theorem principalFrozenEquiv_apply (B : ExchangeMatrix row) :
    principalFrozenEquiv row B = (B.principal, B.matrix.submatrix Subtype.val id) := by
  simp only [principalFrozenEquiv, Equiv.trans_apply, standardPartsEquiv_apply]
  apply Prod.ext
  · exact mutableFrozenEquiv_principal row B
  · ext a j
    simp

/-- Reconstructing the full matrix returns the assembled blocks in the original row indexing. -/
@[simp]
theorem principalFrozenEquiv_symm_matrix
    (p : ExchangeMatrix (Function.Embedding.refl K) × Matrix ((Set.range row)ᶜ : Set I) K ℤ) :
    ((principalFrozenEquiv row).symm p).matrix =
      (Matrix.fromRows p.1.matrix p.2).submatrix
        (Equiv.ofInjectiveSumCompl row row.injective).symm id := by
  simp only [principalFrozenEquiv, Equiv.symm_trans_apply,
    mutableFrozenEquiv_symm_matrix, standardPartsEquiv_symm_matrix]

/-- Reconstructing a matrix preserves the principal block's chosen symmetrizer. -/
@[simp]
theorem principalFrozenEquiv_symm_symmetrizer
    (p : ExchangeMatrix (Function.Embedding.refl K) × Matrix ((Set.range row)ᶜ : Set I) K ℤ) :
    ((principalFrozenEquiv row).symm p).symmetrizer = p.1.symmetrizer := by
  simp only [principalFrozenEquiv, Equiv.symm_trans_apply,
    mutableFrozenEquiv_symm_symmetrizer, standardPartsEquiv_symm_symmetrizer]

/-- Reconstructed matrices have the prescribed principal block. -/
@[simp]
theorem principalFrozenEquiv_symm_principal
    (p : ExchangeMatrix (Function.Embedding.refl K) × Matrix ((Set.range row)ᶜ : Set I) K ℤ) :
    ((principalFrozenEquiv row).symm p).principal = p.1 := by
  simpa only [principalFrozenEquiv_apply] using
    congrArg Prod.fst ((principalFrozenEquiv row).apply_symm_apply p)

@[simp]
private theorem fromRows_submatrix_frozen {J α : Type*}
    (A : Matrix K J α) (F : Matrix ((Set.range row)ᶜ : Set I) J α) :
    (Matrix.fromRows A F).submatrix
      ((Equiv.ofInjectiveSumCompl row row.injective).symm ∘ Subtype.val) id = F := by
  ext a j
  simp [Matrix.submatrix_apply]

/-- Reconstructed matrices have precisely the prescribed frozen block. -/
theorem principalFrozenEquiv_symm_frozen
    (p : ExchangeMatrix (Function.Embedding.refl K) × Matrix ((Set.range row)ᶜ : Set I) K ℤ) :
    ((principalFrozenEquiv row).symm p).matrix.submatrix Subtype.val id = p.2 := by
  simp only [principalFrozenEquiv_symm_matrix, Matrix.submatrix_submatrix, Function.comp_id,
    fromRows_submatrix_frozen]

section Mutation

variable [DecidableEq I] [DecidableEq K]

/-- Mutation is transported by the standard mutable/frozen row presentation. -/
@[simp]
theorem mutableFrozenEquiv_mutation (B : ExchangeMatrix row) (k : K) :
    mutableFrozenEquiv row (B.mutation k) = (mutableFrozenEquiv row B).mutation k := by
  exact (B.mutation_reindex (Equiv.ofInjectiveSumCompl row row.injective).symm (Equiv.refl K)
    (fun k ↦ Equiv.ofInjectiveSumCompl_symm_apply row.injective k) k).symm

/-- A frozen row obeys the same exchange formula, with coupling to the principal block;
its row can never be the mutable row selected for mutation. -/
theorem principalFrozenEquiv_mutation_snd_apply (B : ExchangeMatrix row) (k : K)
    (a : ((Set.range row)ᶜ : Set I)) (j : K) :
    (principalFrozenEquiv row (B.mutation k)).2 a j =
      if j = k then -B.matrix a k else
        B.matrix a j + (B.matrix a k)⁺ * (B.principal.matrix k j)⁺ -
          (B.matrix a k)⁻ * (B.principal.matrix k j)⁻ := by
  have ha : (a : I) ≠ row k := fun h ↦ a.property ⟨k, h.symm⟩
  simp only [principalFrozenEquiv_apply, mutation_matrix, Matrix.submatrix_apply, id_eq,
    matrixMutation_apply, ha, false_or, principal_matrix]
  split_ifs with hj
  · subst j
    rfl
  · rfl

end Mutation

end TauCeti.ExchangeMatrix
