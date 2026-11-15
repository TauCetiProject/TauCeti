/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Matrix.Block

import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Exchange matrices

The combinatorial datum of a cluster algebra is a *skew-symmetrizable* integer matrix: a square
matrix `B` for which some positive integers `s i` make `(s i * B i j)` skew-symmetric. Such a
family `s` is a *skew-symmetrizer* of `B`; the cluster literature calls it a symmetrizer of the
exchange matrix. Cluster algebras with frozen variables use a rectangular *extended* matrix
instead: its columns are indexed by the mutable indices `K`, its rows by all indices `I`, and an
embedding `row : K ↪ I` singles out the mutable rows, which form the skew-symmetrizable
*principal block*.

This file introduces skew-symmetrizers and the type of extended exchange matrices with a chosen
symmetrizer. It derives the sign pattern a skew-symmetrizer forces: the diagonal vanishes, and
entries in transposed positions have opposite signs.

## Main definitions

* `Matrix.IsSkewSymmetrizer B s`: the positive family `s` skew-symmetrizes the square integer
  matrix `B`, that is, `s i * B i j = -(s j * B j i)`.
* `TauCeti.ExchangeMatrix row`: an integer matrix with rows `I` and columns `K`, together with a
  skew-symmetrizer of its principal block along `row : K ↪ I`. Square exchange matrices are the
  case `row = Function.Embedding.refl K`.
* `TauCeti.ExchangeMatrix.submatrix`: restriction and relabelling of rows and columns along maps
  compatible with the mutable embeddings. It covers reindexing along equivalences, deleting
  frozen rows, and freezing mutable indices.
* `TauCeti.ExchangeMatrix.principal`: the principal block, as a square exchange matrix.
* `TauCeti.ExchangeMatrix.reindex`: the bijection between exchange matrices induced by
  equivalences of the index types that commute with the mutable embeddings.
* `TauCeti.ExchangeMatrix.sum`: the block diagonal sum of two exchange matrices.

## Main results

* `Matrix.IsSkewSymmetrizer.apply_self`: a skew-symmetrizable matrix has zero diagonal.
* `Matrix.IsSkewSymmetrizer.apply_pos_iff`, `Matrix.IsSkewSymmetrizer.apply_eq_zero_iff`: entries
  in transposed positions have opposite signs.
* `Matrix.IsSkewSymmetrizer.mul_posPart`, `Matrix.IsSkewSymmetrizer.mul_negPart`: a
  skew-symmetrizer exchanges the positive part of an entry with the negative part of the
  transposed entry.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  §4, for skew-symmetrizable and sign-skew-symmetric matrices.
* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and double
  Bruhat cells*, Duke Math. J. 126 (2005), §1, for extended exchange matrices and their
  principal parts.
-/

public section

variable {I I' I'' K K' K'' I₁ I₂ K₁ K₂ : Type*}

namespace Matrix

/-- The family `s` is a *skew-symmetrizer* of the square integer matrix `B`: its entries are
positive and `(s i * B i j)` is skew-symmetric. A matrix admitting one is called
skew-symmetrizable. In the theory of cluster algebras, where `B` is an exchange matrix, `s` is
called a symmetrizer of `B`. -/
@[mk_iff]
structure IsSkewSymmetrizer (B : Matrix K K ℤ) (s : K → ℤ) : Prop where
  /-- The entries of a skew-symmetrizer are positive. -/
  pos : ∀ i, 0 < s i
  /-- Scaling the rows by a skew-symmetrizer gives a skew-symmetric matrix. -/
  mul_apply : ∀ i j, s i * B i j = -(s j * B j i)

namespace IsSkewSymmetrizer

variable {B : Matrix K K ℤ} {s : K → ℤ}

/-- A skew-symmetrizable matrix has zero diagonal. -/
theorem apply_self (h : B.IsSkewSymmetrizer s) (i : K) : B i i = 0 := by
  have h2 : s i * B i i = 0 := by
    have := h.mul_apply i i
    omega
  exact (mul_eq_zero.mp h2).resolve_left (h.pos i).ne'

/-- In a skew-symmetrizable matrix, an entry is positive exactly when the entry in the
transposed position is negative. -/
theorem apply_pos_iff (h : B.IsSkewSymmetrizer s) {i j : K} : 0 < B i j ↔ B j i < 0 := by
  rw [← mul_pos_iff_of_pos_left (h.pos i), h.mul_apply, ← mul_neg,
    mul_pos_iff_of_pos_left (h.pos j), neg_pos]

/-- In a skew-symmetrizable matrix, an entry vanishes exactly when the entry in the transposed
position does. -/
theorem apply_eq_zero_iff (h : B.IsSkewSymmetrizer s) {i j : K} : B i j = 0 ↔ B j i = 0 := by
  rw [← mul_right_inj' (h.pos i).ne', h.mul_apply, mul_zero, neg_eq_zero, mul_eq_zero,
    or_iff_right (h.pos j).ne']

/-- A skew-symmetrizer exchanges the positive part of an entry with the negative part of the
entry in the transposed position. -/
theorem mul_posPart (h : B.IsSkewSymmetrizer s) (i j : K) :
    s i * (B i j)⁺ = s j * (B j i)⁻ := by
  rw [posPart_def, negPart_def, mul_max_of_nonneg _ _ (h.pos i).le,
    mul_max_of_nonneg _ _ (h.pos j).le, h.mul_apply, mul_neg, mul_zero, mul_zero]

/-- A skew-symmetrizer exchanges the negative part of an entry with the positive part of the
entry in the transposed position. -/
theorem mul_negPart (h : B.IsSkewSymmetrizer s) (i j : K) :
    s i * (B i j)⁻ = s j * (B j i)⁺ :=
  (h.mul_posPart j i).symm

/-- A skew-symmetrizer of `B` is a skew-symmetrizer of `-B`. -/
protected theorem neg (h : B.IsSkewSymmetrizer s) : (-B).IsSkewSymmetrizer s :=
  ⟨h.pos, fun i j ↦ by simp [h.mul_apply i j]⟩

/-- A skew-symmetrizer restricts along any map of index types, to a skew-symmetrizer of the
corresponding submatrix. -/
protected theorem submatrix (h : B.IsSkewSymmetrizer s) (e : K' → K) :
    (B.submatrix e e).IsSkewSymmetrizer (s ∘ e) :=
  ⟨fun i ↦ h.pos (e i), fun i j ↦ h.mul_apply (e i) (e j)⟩

/-- Skew-symmetrizers of two matrices assemble into a skew-symmetrizer of their block diagonal
sum. -/
protected theorem fromBlocks {B₁ : Matrix K₁ K₁ ℤ} {B₂ : Matrix K₂ K₂ ℤ} {s₁ : K₁ → ℤ}
    {s₂ : K₂ → ℤ} (h₁ : B₁.IsSkewSymmetrizer s₁) (h₂ : B₂.IsSkewSymmetrizer s₂) :
    (fromBlocks B₁ 0 0 B₂).IsSkewSymmetrizer (Sum.elim s₁ s₂) where
  pos := by rintro (i | i) <;> simp [h₁.pos, h₂.pos]
  mul_apply := by
    rintro (i | i) (j | j)
    · simpa using h₁.mul_apply i j
    · simp
    · simp
    · simpa using h₂.mul_apply i j

end IsSkewSymmetrizer

/-- The matrix with rows `(0, 1)` and `(-2, 0)` is not skew-symmetric, but it is
skew-symmetrizable: the family `(2, 1)` is a skew-symmetrizer. -/
example : (!![0, 1; -2, 0] : Matrix (Fin 2) (Fin 2) ℤ).IsSkewSymmetrizer ![2, 1] :=
  ⟨by decide, by decide⟩

end Matrix

namespace TauCeti

open Matrix

/-- An *exchange matrix* along the embedding `row : K ↪ I` of the mutable indices `K` into the
index type `I`: an integer matrix with rows indexed by `I` and columns by `K`, together with a
chosen symmetrizer of its *principal block*, the square matrix formed by the mutable rows.

The rows outside the range of `row` are the frozen rows; no condition is imposed on them. A
square exchange matrix, with no frozen rows, is an exchange matrix along
`Function.Embedding.refl K`. -/
@[ext]
structure ExchangeMatrix (row : K ↪ I) where
  /-- The underlying matrix, with rows indexed by `I` and columns by the mutable indices `K`. -/
  matrix : Matrix I K ℤ
  /-- The chosen symmetrizer of the principal block. -/
  symmetrizer : K → ℤ
  /-- The chosen family skew-symmetrizes the principal block. -/
  isSkewSymmetrizer : (matrix.submatrix row id).IsSkewSymmetrizer symmetrizer

namespace ExchangeMatrix

variable {row : K ↪ I} {row' : K' ↪ I'} {row'' : K'' ↪ I''} (B : ExchangeMatrix row)

/-- The symmetrizer of an exchange matrix is positive. -/
theorem symmetrizer_pos (k : K) : 0 < B.symmetrizer k :=
  B.isSkewSymmetrizer.pos k

/-- The symmetrizer of an exchange matrix skew-symmetrizes its mutable rows. -/
theorem symmetrizer_mul_matrix (i j : K) :
    B.symmetrizer i * B.matrix (row i) j = -(B.symmetrizer j * B.matrix (row j) i) :=
  B.isSkewSymmetrizer.mul_apply i j

/-- The diagonal of the principal block of an exchange matrix vanishes. -/
@[simp]
theorem matrix_row_self (k : K) : B.matrix (row k) k = 0 :=
  B.isSkewSymmetrizer.apply_self k

/-- Restrict and relabel the rows and columns of an exchange matrix along maps `f` and `g` that
are compatible with the mutable embeddings.

For equivalences `f` and `g` this is reindexing. For `g = id` and `f` injective it deletes
frozen rows. For `f = id` and `g` an embedding it freezes the mutable indices outside the range of
`g`, by deleting their columns. -/
def submatrix (f : I' → I) (g : K' → K) (h : ∀ k, f (row' k) = row (g k)) :
    ExchangeMatrix row' where
  matrix := B.matrix.submatrix f g
  symmetrizer := B.symmetrizer ∘ g
  isSkewSymmetrizer := by
    have hBlock : (B.matrix.submatrix f g).submatrix row' id =
        (B.matrix.submatrix row id).submatrix g g := by
      ext i j
      simp [h]
    rw [hBlock]
    exact B.isSkewSymmetrizer.submatrix g

@[simp]
theorem submatrix_matrix (f : I' → I) (g : K' → K) (h : ∀ k, f (row' k) = row (g k)) :
    (B.submatrix f g h).matrix = B.matrix.submatrix f g :=
  (rfl)

@[simp]
theorem submatrix_symmetrizer (f : I' → I) (g : K' → K) (h : ∀ k, f (row' k) = row (g k)) :
    (B.submatrix f g h).symmetrizer = B.symmetrizer ∘ g :=
  (rfl)

/-- Restricting along identity maps does nothing. The compatibility of the identity maps with the
mutable embedding is taken as an argument, so that the statement applies whatever its proof. -/
@[simp]
theorem submatrix_id (h : ∀ k, id (row k) = row (id k)) : B.submatrix id id h = B := by
  ext : 1 <;> simp

/-- Restricting twice is restricting along the composite maps. -/
@[simp]
theorem submatrix_submatrix (f : I' → I) (g : K' → K) (h : ∀ k, f (row' k) = row (g k))
    (f' : I'' → I') (g' : K'' → K') (h' : ∀ k, f' (row'' k) = row' (g' k)) :
    (B.submatrix f g h).submatrix f' g' h' = B.submatrix (f ∘ f') (g ∘ g') fun k ↦ by
      rw [Function.comp_apply, Function.comp_apply, h', h] := by
  ext : 1 <;> simp [Function.comp_assoc]

/-- The principal block of an exchange matrix, as a square exchange matrix with the same
symmetrizer. -/
def principal : ExchangeMatrix (Function.Embedding.refl K) :=
  B.submatrix row id fun k ↦ by rw [Function.Embedding.refl_apply, id_eq]

@[simp]
theorem principal_matrix : B.principal.matrix = B.matrix.submatrix row id :=
  (rfl)

@[simp]
theorem principal_symmetrizer : B.principal.symmetrizer = B.symmetrizer :=
  (rfl)

/-- A square exchange matrix is its own principal block. -/
@[simp]
theorem principal_eq_self (B : ExchangeMatrix (Function.Embedding.refl K)) : B.principal = B := by
  ext <;> simp

/-- Reindex exchange matrices along equivalences of the row and of the column index types that
commute with the mutable embeddings. -/
def reindex (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k)) :
    ExchangeMatrix row ≃ ExchangeMatrix row' where
  toFun B := B.submatrix eI.symm eK.symm fun k ↦ by
    rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]
  invFun B := B.submatrix eI eK h
  left_inv B := by simp
  right_inv B := by simp

@[simp]
theorem reindex_matrix (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k)) :
    (reindex eI eK h B).matrix = B.matrix.submatrix eI.symm eK.symm :=
  (rfl)

@[simp]
theorem reindex_symmetrizer (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k)) :
    (reindex eI eK h B).symmetrizer = B.symmetrizer ∘ eK.symm :=
  (rfl)

@[simp]
theorem reindex_symm_apply (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (B : ExchangeMatrix row') : (reindex eI eK h).symm B = B.submatrix eI eK h :=
  (rfl)

/-- Reindexing along identity equivalences is the identity. The compatibility of the identity
equivalences with the mutable embedding is taken as an argument, so that the statement applies
whatever its proof. -/
@[simp]
theorem reindex_refl (h : ∀ k, Equiv.refl I (row k) = row (Equiv.refl K k)) :
    reindex (Equiv.refl I) (Equiv.refl K) h = Equiv.refl (ExchangeMatrix row) := by
  ext B : 2 <;> simp

/-- Reindexing twice is reindexing along the composite equivalences. -/
theorem reindex_trans (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (eI' : I' ≃ I'') (eK' : K' ≃ K'') (h' : ∀ k, eI' (row' k) = row'' (eK' k)) :
    (reindex eI eK h).trans (reindex eI' eK' h') =
      reindex (eI.trans eI') (eK.trans eK') fun k ↦ by
        rw [Equiv.trans_apply, Equiv.trans_apply, h, h'] := by
  ext B : 2 <;> simp [Function.comp_assoc]

/-- The block diagonal sum of two exchange matrices: its mutable indices, its rows and its
symmetrizer are the disjoint unions of those of the summands, and no entry joins the two. -/
def sum {row₁ : K₁ ↪ I₁} {row₂ : K₂ ↪ I₂} (B₁ : ExchangeMatrix row₁) (B₂ : ExchangeMatrix row₂) :
    ExchangeMatrix (row₁.sumMap row₂) where
  matrix := fromBlocks B₁.matrix 0 0 B₂.matrix
  symmetrizer := Sum.elim B₁.symmetrizer B₂.symmetrizer
  isSkewSymmetrizer := by
    have hBlock : (fromBlocks B₁.matrix 0 0 B₂.matrix).submatrix (row₁.sumMap row₂) id =
        fromBlocks (B₁.matrix.submatrix row₁ id) 0 0 (B₂.matrix.submatrix row₂ id) := by
      ext (i | i) (j | j) <;> simp
    rw [hBlock]
    exact B₁.isSkewSymmetrizer.fromBlocks B₂.isSkewSymmetrizer

@[simp]
theorem sum_matrix {row₁ : K₁ ↪ I₁} {row₂ : K₂ ↪ I₂} (B₁ : ExchangeMatrix row₁)
    (B₂ : ExchangeMatrix row₂) : (B₁.sum B₂).matrix = fromBlocks B₁.matrix 0 0 B₂.matrix :=
  (rfl)

@[simp]
theorem sum_symmetrizer {row₁ : K₁ ↪ I₁} {row₂ : K₂ ↪ I₂} (B₁ : ExchangeMatrix row₁)
    (B₂ : ExchangeMatrix row₂) :
    (B₁.sum B₂).symmetrizer = Sum.elim B₁.symmetrizer B₂.symmetrizer :=
  (rfl)

end ExchangeMatrix

end TauCeti
