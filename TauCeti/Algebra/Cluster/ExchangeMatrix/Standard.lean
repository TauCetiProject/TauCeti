/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Standard exchange matrices with prescribed frozen rows

A mutable-first matrix is equivalent to its principal exchange matrix and an arbitrary frozen
block. The inverse is the shared construction used by principal and degree-principal extensions.
It retains the principal matrix's chosen symmetrizer and its existing witness. The round trips use
Mathlib row-partition identities directly.
-/

public section

namespace TauCeti.ExchangeMatrix

/-- Standard mutable-first exchange matrices are reconstructed from a principal exchange matrix
and an arbitrary frozen-row matrix, without choosing a complement presentation. -/
def standardPartsEquiv (K J : Type*) :
    ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J) ≃
      ExchangeMatrix (Function.Embedding.refl K) × Matrix J K ℤ where
  toFun B := (B.principal, B.matrix.submatrix Sum.inr id)
  invFun p :=
    { matrix := Matrix.fromRows p.1.matrix p.2
      symmetrizer := p.1.symmetrizer
      -- Both row projections use the same chosen witness; do not reconstruct it.
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
    · dsimp only
      exact Matrix.toRows₂_fromRows p.1.matrix p.2

/-- Decomposing a standard presentation returns its principal and frozen blocks. -/
@[simp]
theorem standardPartsEquiv_apply {K J : Type*}
    (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) :
    standardPartsEquiv K J B = (B.principal, B.matrix.submatrix Sum.inr id) := by rfl

/-- The inverse assembles exactly the specified mutable and frozen rows. -/
@[simp]
theorem standardPartsEquiv_symm_matrix {K J : Type*}
    (p : ExchangeMatrix (Function.Embedding.refl K) × Matrix J K ℤ) :
    ((standardPartsEquiv K J).symm p).matrix = Matrix.fromRows p.1.matrix p.2 := by rfl

/-- The assembled standard presentation retains the principal block's chosen symmetrizer. -/
@[simp]
theorem standardPartsEquiv_symm_symmetrizer {K J : Type*}
    (p : ExchangeMatrix (Function.Embedding.refl K) × Matrix J K ℤ) :
    ((standardPartsEquiv K J).symm p).symmetrizer = p.1.symmetrizer := by rfl

end TauCeti.ExchangeMatrix
