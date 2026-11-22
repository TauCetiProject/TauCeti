/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Matrix.ColumnRowPartitioned

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
* `TauCeti.ExchangeMatrix.extendFrozen`: extension by zero along a frozen embedding.
* `TauCeti.ExchangeMatrix.amalgamate`: block diagonal mutable factors sharing frozen vertices.
  Local frozen boundaries embed in the common boundary; each common vertex has one row.
  This is the rectangular mutable-column projection, without a frozen-frozen block.

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
* V. Fock and A. Goncharov, *Cluster X-varieties, amalgamation, and Poisson–Lie groups*,
  §2.2, for amalgamation along frozen vertices.
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

/-- Taking the principal block commutes with any compatible row and column restriction. -/
@[simp]
theorem principal_submatrix (f : I' → I) (g : K' → K)
    (h : ∀ k, f (row' k) = row (g k)) :
    (B.submatrix f g h).principal =
      B.principal.submatrix (row' := Function.Embedding.refl K') g g (fun _ ↦ rfl) := by
  ext : 1
  · rw [(B.submatrix f g h).principal_matrix, B.submatrix_matrix f g h,
      B.principal.submatrix_matrix g g (fun _ ↦ rfl), B.principal_matrix]
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, h]
  · rw [(B.submatrix f g h).principal_symmetrizer, B.submatrix_symmetrizer f g h,
      B.principal.submatrix_symmetrizer g g (fun _ ↦ rfl), B.principal_symmetrizer]

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

/-- Reindexing acts by compatible restriction along the inverse index equivalences. -/
theorem reindex_apply (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) :
    reindex eI eK h B = B.submatrix eI.symm eK.symm (fun k ↦ by
      rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]) :=
  (rfl)

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
@[simp]
theorem reindex_trans (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (eI' : I' ≃ I'') (eK' : K' ≃ K'') (h' : ∀ k, eI' (row' k) = row'' (eK' k)) :
    (reindex eI eK h).trans (reindex eI' eK' h') =
      reindex (eI.trans eI') (eK.trans eK') fun k ↦ by
        rw [Equiv.trans_apply, Equiv.trans_apply, h, h'] := by
  ext B : 2 <;> simp [Function.comp_assoc]

/-- Nested reindexing applications collapse to the composite relabelling. -/
@[simp]
theorem reindex_reindex (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k))
    (eI' : I' ≃ I'') (eK' : K' ≃ K'') (h' : ∀ k, eI' (row' k) = row'' (eK' k)) :
    reindex eI' eK' h' (reindex eI eK h B) =
      reindex (eI.trans eI') (eK.trans eK') (fun k ↦ by
        rw [Equiv.trans_apply, Equiv.trans_apply, h, h']) B := by
  simpa only [Equiv.trans_apply] using
    congrArg (fun e : ExchangeMatrix row ≃ ExchangeMatrix row'' ↦ e B)
      (reindex_trans eI eK h eI' eK' h')

/-- Taking principal blocks commutes with compatible relabelling. -/
@[simp]
theorem principal_reindex (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) :
    (reindex eI eK h B).principal =
      reindex (row := Function.Embedding.refl K) (row' := Function.Embedding.refl K')
        eK eK (fun _ ↦ by simp only [Function.Embedding.refl_apply]) B.principal := by
  rw [reindex_apply, reindex_apply]
  exact B.principal_submatrix eI.symm eK.symm _

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

section FrozenExtension

variable {J F G : Type*}

/-- Extend the frozen rows by zero along an embedding, keeping the principal matrix and its
chosen symmetrizer. -/
noncomputable def extendFrozen (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J))
    (e : J ↪ F) : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ F) where
  matrix := Matrix.fromRows (B.matrix.submatrix Sum.inl id)
    (Matrix.of fun f k ↦ Function.extend e (fun j ↦ B.matrix (Sum.inr j) k) 0 f)
  symmetrizer := B.symmetrizer
  isSkewSymmetrizer := by
    convert B.isSkewSymmetrizer using 1
    ext i k
    simp [Matrix.submatrix_apply, Function.Embedding.inl_apply]

variable (B : ExchangeMatrix (Function.Embedding.inl : K ↪ K ⊕ J)) (e : J ↪ F)

/-- Extending the boundary keeps each mutable entry. -/
@[simp] theorem extendFrozen_matrix_inl (i k : K) :
    (B.extendFrozen e).matrix (Sum.inl i) k = B.matrix (Sum.inl i) k := by
  simp [extendFrozen]

/-- The frozen-row portion of each mutable column is extended by zero along the embedding. -/
theorem extendFrozen_matrix_frozen (f : F) (k : K) :
    (B.extendFrozen e).matrix (Sum.inr f) k =
      Function.extend e (fun j ↦ B.matrix (Sum.inr j) k) 0 f := by
  simp only [extendFrozen, Matrix.fromRows_apply_inr, Matrix.of_apply]

/-- The original frozen rows are retained at their embedded vertices. -/
@[simp] theorem extendFrozen_matrix_inr (j : J) (k : K) :
    (B.extendFrozen e).matrix (Sum.inr (e j)) k = B.matrix (Sum.inr j) k := by
  rw [extendFrozen_matrix_frozen, e.injective.extend_apply]

/-- A vertex not in the factor's frozen image contributes a zero row. -/
@[simp] theorem extendFrozen_matrix_of_not_mem_range (f : F) (hf : f ∉ Set.range e) (k : K) :
    (B.extendFrozen e).matrix (Sum.inr f) k = 0 := by
  rw [extendFrozen_matrix_frozen, Function.extend_apply' _ _ _ hf]
  rfl

/-- Extension does not change the chosen symmetrizer. -/
@[simp] theorem extendFrozen_symmetrizer : (B.extendFrozen e).symmetrizer = B.symmetrizer := by
  rfl

/-- Restriction along the frozen embedding recovers the original exchange matrix. -/
@[simp] theorem submatrix_extendFrozen :
    (B.extendFrozen e).submatrix (Sum.map id e) id (fun _ ↦ by simp) = B := by
  ext : 1
  · ext (i | j) k <;> simp [submatrix_matrix]
  · simp

/-- Extending by the identity embedding does nothing. -/
@[simp] theorem extendFrozen_refl : B.extendFrozen (Function.Embedding.refl J) = B := by
  ext : 1
  · ext (i | j) k
    · simp
    · simpa only [Function.Embedding.refl_apply] using
        extendFrozen_matrix_inr B (Function.Embedding.refl J) j k
  · simp

/-- Extending frozen vertices in stages is extending along the composite embedding. -/
@[simp] theorem extendFrozen_extendFrozen (g : F ↪ G) :
    (B.extendFrozen e).extendFrozen g = B.extendFrozen (e.trans g) := by
  ext : 1
  · ext (i | f) k
    · simp
    · simp only [extendFrozen_matrix_frozen]
      exact congrFun (e.injective.extend_comp g.injective
        (fun j ↦ B.matrix (Sum.inr j) k) 0).symm f
  · simp

/-- Extending local frozen rows commutes with relabelling mutable, local frozen and common
frozen vertices. The local frozen embedding is transported along the inverse local equivalence. -/
theorem extendFrozen_reindex {K' J' F' : Type*}
    (eK : K ≃ K') (eJ : J ≃ J') (eF : F ≃ F') :
    (reindex (row' := (Function.Embedding.inl : K' ↪ K' ⊕ J'))
      (Equiv.sumCongr eK eJ) eK (fun _ ↦ by simp) B).extendFrozen
        ((eJ.symm.toEmbedding.trans e).trans eF.toEmbedding) =
      reindex (row' := (Function.Embedding.inl : K' ↪ K' ⊕ F'))
        (Equiv.sumCongr eK eF) eK (fun _ ↦ by simp) (B.extendFrozen e) := by
  ext : 1
  · ext (i | f) k
    · simp [reindex_matrix, Matrix.submatrix_apply]
    · simp only [extendFrozen_matrix_frozen, reindex_matrix, Matrix.submatrix_apply,
        Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr]
      let v : J → ℤ := fun j ↦ B.matrix (Sum.inr j) (eK.symm k)
      change Function.extend (eF ∘ (e ∘ eJ.symm)) (v ∘ eJ.symm) 0 f =
        Function.extend e v 0 (eF.symm f)
      rw [(e.injective.comp eJ.symm.injective).extend_comp eF.injective,
        Equiv.extend_apply, eJ.symm.injective.extend_comp e.injective]
      have he : Function.extend eJ.symm (v ∘ eJ.symm) (((0 : F' → ℤ) ∘ eF) ∘ e) = v := by
        funext j
        simp only [Equiv.extend_apply, Equiv.symm_symm, Function.comp_apply,
          Equiv.symm_apply_apply]
      rw [he]
      rfl
  · simp

end FrozenExtension

section Amalgamation

variable {A F : Type*} {M L : A → Type*} [DecidableEq A]

/-- Assemble factors whose local frozen vertices embed in a common boundary. Mathlib's
`Matrix.blockDiagonal'` assembles the principal blocks; frozen rows are extended by zero
and share one row per boundary vertex. -/
noncomputable def amalgamate (e : ∀ a, L a ↪ F)
    (Bs : ∀ a, ExchangeMatrix (Function.Embedding.inl : M a ↪ M a ⊕ L a)) :
    ExchangeMatrix (Function.Embedding.inl : (Σ a, M a) ↪ (Σ a, M a) ⊕ F) where
  matrix := Matrix.fromRows (Matrix.blockDiagonal' fun a ↦ (Bs a).matrix.submatrix Sum.inl id)
    (Matrix.of fun f j ↦ ((Bs j.1).extendFrozen (e j.1)).matrix (Sum.inr f) j.2)
  symmetrizer := fun j ↦ (Bs j.1).symmetrizer j.2
  isSkewSymmetrizer := by
    constructor
    · rintro ⟨a, k⟩
      exact (Bs a).isSkewSymmetrizer.pos k
    · rintro ⟨a, i⟩ ⟨b, j⟩
      by_cases h : a = b
      · subst b
        simpa [Matrix.submatrix_apply] using (Bs a).isSkewSymmetrizer.mul_apply i j
      · simp [Matrix.submatrix_apply, Matrix.blockDiagonal'_apply_ne, h, Ne.symm h]

variable (e : ∀ a, L a ↪ F)
variable (Bs : ∀ a, ExchangeMatrix (Function.Embedding.inl : M a ↪ M a ⊕ L a))

/-- Mutable entries in one factor are retained. -/
@[simp] theorem amalgamate_matrix_eq (a : A) (i j : M a) :
    (amalgamate e Bs).matrix (Sum.inl ⟨a, i⟩) ⟨a, j⟩ = (Bs a).matrix (Sum.inl i) j := by
  simp [amalgamate, Matrix.submatrix_apply]

/-- No mutable entry joins distinct factors. -/
@[simp] theorem amalgamate_matrix_ne {a b : A} (i : M a) (j : M b) (h : a ≠ b) :
    (amalgamate e Bs).matrix (Sum.inl ⟨a, i⟩) ⟨b, j⟩ = 0 := by
  simp [amalgamate, Matrix.blockDiagonal'_apply_ne, h]

/-- A frozen entry is the corresponding zero-padded factor entry. -/
@[simp] theorem amalgamate_matrix_frozen (f : F) (a : A) (k : M a) :
    (amalgamate e Bs).matrix (Sum.inr f) ⟨a, k⟩ =
      ((Bs a).extendFrozen (e a)).matrix (Sum.inr f) k := by
  simp only [amalgamate, Matrix.fromRows_apply_inr, Matrix.of_apply]

/-- The chosen symmetrizers are retained as data. -/
@[simp] theorem amalgamate_symmetrizer (a : A) (k : M a) :
    (amalgamate e Bs).symmetrizer ⟨a, k⟩ = (Bs a).symmetrizer k := by
  rfl

/-- Extracting a factor with the entire common boundary yields its zero extension. -/
@[simp] theorem submatrix_amalgamate_all_frozen (a : A) :
    (amalgamate e Bs).submatrix (Sum.map (Sigma.mk a) id) (Sigma.mk a)
      (fun _ ↦ by simp only [Function.Embedding.inl_apply, Sum.map_inl]) =
        (Bs a).extendFrozen (e a) := by
  ext : 1
  · ext (i | f) j <;> simp [submatrix_matrix]
  · funext k
    simp

/-- Restricting along the factor's mutable and frozen embeddings recovers that factor. -/
@[simp] theorem submatrix_amalgamate (a : A) :
    (amalgamate e Bs).submatrix (Sum.map (Sigma.mk a) (e a)) (Sigma.mk a)
      (fun _ ↦ by simp only [Function.Embedding.inl_apply, Sum.map_inl]) = Bs a := by
  have h := congrArg (fun C : ExchangeMatrix
      (Function.Embedding.inl : M a ↪ M a ⊕ F) ↦
        C.submatrix (row' := (Function.Embedding.inl : M a ↪ M a ⊕ L a))
          (Sum.map id (e a)) id (fun _ ↦ by simp))
      (submatrix_amalgamate_all_frozen e Bs a)
  rw [submatrix_submatrix] at h
  have hm : Sum.map (Sigma.mk (β := M) a) (id : F → F) ∘
      Sum.map (id : M a → M a) (e a) = Sum.map (Sigma.mk a) (e a) := by
    funext r
    cases r <;> rfl
  simpa only [hm, Function.comp_id, submatrix_extendFrozen] using h

/-- Restrictions to the zero-padded factors and absence of cross-factor entries characterize
an amalgamation: a frozen vertex outside a factor's image has zero entries in that
factor's columns. -/
theorem eq_amalgamate_iff
    (C : ExchangeMatrix (Function.Embedding.inl : (Σ a, M a) ↪ (Σ a, M a) ⊕ F)) :
    C = amalgamate e Bs ↔
      (∀ a, C.submatrix (Sum.map (Sigma.mk a) id) (Sigma.mk a)
        (fun _ ↦ by simp only [Function.Embedding.inl_apply, Sum.map_inl]) =
          (Bs a).extendFrozen (e a)) ∧
      ∀ a b, a ≠ b → ∀ i : M a, ∀ j : M b, C.matrix (Sum.inl ⟨a, i⟩) ⟨b, j⟩ = 0 := by
  constructor
  · rintro rfl
    exact ⟨submatrix_amalgamate_all_frozen e Bs, fun _ _ h _ _ ↦
      amalgamate_matrix_ne e Bs _ _ h⟩
  · rintro ⟨hf, hz⟩
    have hp (a : A) (r : M a ⊕ F) (k : M a) :=
      congrFun (congrFun (congrArg ExchangeMatrix.matrix (hf a)) r) k
    ext : 1
    · ext (⟨a, i⟩ | f) ⟨b, j⟩
      · by_cases hab : a = b
        · subst b
          simpa [submatrix_matrix] using hp a (Sum.inl i) j
        · rw [hz a b hab, amalgamate_matrix_ne e Bs i j hab]
      · simpa [submatrix_matrix] using hp b (Sum.inr f) j
    · funext ⟨a, k⟩
      have h := congrFun (congrArg ExchangeMatrix.symmetrizer (hf a)) k
      simpa using h

/-- Assembly commutes with permutations of factors, fibrewise mutable and local frozen
relabellings, and a common relabelling of frozen vertices. -/
theorem amalgamate_reindex {A' F' : Type*} [DecidableEq A'] {N Q : A' → Type*}
    (eA : A' ≃ A) (eM : ∀ a, M (eA a) ≃ N a)
    (eL : ∀ a, L (eA a) ≃ Q a) (eF : F ≃ F') :
    amalgamate (fun a ↦ ((eL a).symm.toEmbedding.trans (e (eA a))).trans eF.toEmbedding)
        (fun a ↦ reindex (row' := (Function.Embedding.inl : N a ↪ N a ⊕ Q a))
          (Equiv.sumCongr (eM a) (eL a)) (eM a) (fun _ ↦ by simp) (Bs (eA a))) =
      reindex (row' := Function.Embedding.inl)
        (Equiv.sumCongr (Equiv.sigmaCongr eA (fun a ↦ (eM a).symm)).symm eF)
        (Equiv.sigmaCongr eA (fun a ↦ (eM a).symm)).symm (fun _ ↦ rfl)
        (amalgamate e Bs) := by
  ext : 1
  · ext (⟨a, i⟩ | f) ⟨b, j⟩
    · by_cases hab : a = b
      · subst b
        simp [reindex_matrix, Matrix.submatrix_apply, Equiv.sigmaCongr]
      · have h : eA a ≠ eA b := eA.injective.ne hab
        simp [reindex_matrix, Matrix.submatrix_apply, Equiv.sigmaCongr, hab, h]
    · simp only [amalgamate_matrix_frozen]
      rw [extendFrozen_reindex]
      simp [reindex_matrix, Matrix.submatrix_apply, Equiv.sigmaCongr]
  · funext ⟨a, k⟩
    simp [reindex_symmetrizer, Equiv.sigmaCongr]

end Amalgamation

section Stages

variable {A F : Type*} {B G : A → Type*} {M L : ∀ a, B a → Type*}
  [DecidableEq A] [∀ a, DecidableEq (B a)]

/-- Grouping through individual intermediate frozen boundaries agrees with assembly along
the composite embeddings, after the canonical association of mutable indices. -/
theorem amalgamate_amalgamate (e : ∀ a b, L a b ↪ G a) (g : ∀ a, G a ↪ F)
    (Bs : ∀ a b, ExchangeMatrix (Function.Embedding.inl : M a b ↪ M a b ⊕ L a b)) :
    amalgamate g (fun a ↦ amalgamate (e a) (Bs a)) =
      reindex (row' := Function.Embedding.inl)
        (Equiv.sumCongr (Equiv.sigmaAssoc M) (Equiv.refl F)) (Equiv.sigmaAssoc M)
        (fun _ ↦ rfl) (amalgamate (fun p : Σ a, B a ↦ (e p.1 p.2).trans (g p.1))
          (fun p ↦ Bs p.1 p.2)) := by
  ext : 1
  · ext (⟨a, b, i⟩ | f) ⟨c, d, j⟩
    · by_cases hac : a = c
      · subst c
        by_cases hbd : b = d
        · subst d
          simp [reindex_matrix, Matrix.submatrix_apply, Equiv.sigmaAssoc]
        · have hp : (⟨a, b⟩ : Σ a, B a) ≠ ⟨a, d⟩ := by
            intro h
            exact hbd (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
          simp [reindex_matrix, Matrix.submatrix_apply, Equiv.sigmaAssoc, hbd, hp]
      · have hp : (⟨a, b⟩ : Σ a, B a) ≠ ⟨c, d⟩ := fun h ↦ hac (congrArg Sigma.fst h)
        simp [reindex_matrix, Matrix.submatrix_apply, Equiv.sigmaAssoc, hac, hp]
    · simp only [amalgamate_matrix_frozen]
      simp only [Equiv.sigmaAssoc, extendFrozen_matrix_frozen, amalgamate_matrix_frozen]
      exact congrFun ((e c d).injective.extend_comp (g c).injective
        (fun l ↦ (Bs c d).matrix (Sum.inr l) j) 0).symm f
  · funext ⟨a, b, k⟩
    simp [reindex_symmetrizer, Equiv.sigmaAssoc]

end Stages

end ExchangeMatrix

end TauCeti
