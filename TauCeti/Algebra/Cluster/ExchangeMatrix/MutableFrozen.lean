/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
public import TauCeti.Logic.Equiv.Set
public import Mathlib.Data.Matrix.ColumnRowPartitioned

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

/-- Standardization leaves the principal exchange matrix unchanged. -/
@[simp]
theorem mutableFrozenEquiv_principal (B : ExchangeMatrix row) :
    (mutableFrozenEquiv row B).principal = B.principal := by
  simpa only [mutableFrozenEquiv, reindex_refl, Equiv.refl_apply] using
    B.principal_reindex (Equiv.ofInjectiveSumCompl row row.injective).symm (Equiv.refl K)
      (fun k ↦ Equiv.ofInjectiveSumCompl_symm_apply row.injective k)

private def standardPartsEquiv (K J : Type*) :
    ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) ≃
      ExchangeMatrix (Function.Embedding.refl K) × Matrix J K ℤ where
  toFun B := (B.principal, B.matrix.submatrix Sum.inr id)
  invFun p :=
    { matrix := Matrix.fromRows p.1.matrix p.2
      symmetrizer := p.1.symmetrizer
      isSkewSymmetrizer := p.1.isSkewSymmetrizer }
  left_inv B := by
    ext : 1
    · dsimp only
      rw [principal_matrix]
      exact Matrix.fromRows_toRows B.matrix
    · simp
  right_inv p := by
    apply Prod.ext
    · ext : 1
      · dsimp only
        rw [principal_matrix]
        exact Matrix.toRows₁_fromRows p.1.matrix p.2
      · simp
    · exact Matrix.toRows₂_fromRows p.1.matrix p.2

/-- An extended exchange matrix is exactly a principal exchange matrix and an unconstrained
frozen-row matrix, with the original row embedding retained by the inverse construction. -/
def principalFrozenEquiv : ExchangeMatrix row ≃
    ExchangeMatrix (Function.Embedding.refl K) × Matrix ((Set.range row)ᶜ : Set I) K ℤ :=
  (mutableFrozenEquiv row).trans (standardPartsEquiv K _)

/-- The forward decomposition consists of the actual principal block and actual frozen rows. -/
theorem principalFrozenEquiv_apply (B : ExchangeMatrix row) :
    principalFrozenEquiv row B = (B.principal, B.matrix.submatrix Subtype.val id) := by
  apply Prod.ext
  · exact mutableFrozenEquiv_principal row B
  · ext a j
    simp [principalFrozenEquiv, standardPartsEquiv]

/-- The first component of the decomposition is the original principal exchange matrix. -/
@[simp]
theorem principalFrozenEquiv_fst (B : ExchangeMatrix row) :
    (principalFrozenEquiv row B).1 = B.principal := by
  rw [principalFrozenEquiv_apply]

/-- The second component contains exactly the original frozen entries. -/
@[simp]
theorem principalFrozenEquiv_snd (B : ExchangeMatrix row) :
    (principalFrozenEquiv row B).2 = B.matrix.submatrix Subtype.val id := by
  rw [principalFrozenEquiv_apply]

/-- Reconstructed matrices have the prescribed principal block. -/
@[simp]
theorem principalFrozenEquiv_symm_principal
    (p : ExchangeMatrix (Function.Embedding.refl K) × Matrix ((Set.range row)ᶜ : Set I) K ℤ) :
    ((principalFrozenEquiv row).symm p).principal = p.1 := by
  rw [← principalFrozenEquiv_fst, Equiv.apply_symm_apply]

/-- Reconstructed matrices have precisely the prescribed frozen block. -/
@[simp]
theorem principalFrozenEquiv_symm_frozen
    (p : ExchangeMatrix (Function.Embedding.refl K) × Matrix ((Set.range row)ᶜ : Set I) K ℤ) :
    ((principalFrozenEquiv row).symm p).matrix.submatrix Subtype.val id = p.2 := by
  rw [← principalFrozenEquiv_snd, Equiv.apply_symm_apply]

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
  by_cases hj : j = k
  · subst j
    simp
  · simp [matrixMutation_apply, ha, hj, principal_matrix]

end Mutation

end TauCeti.ExchangeMatrix
