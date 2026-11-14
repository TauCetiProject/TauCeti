/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
public import TauCeti.Data.List.Involutive

/-!
# Finite mutation words on exchange matrices

Finite mutation words parameterize iterated mutations from an initial matrix. They provide
the matrix patterns underlying cluster and Y-seed patterns, and describe mutation classes
without choosing a path length. The raw rectangular matrix action propagates extended matrices
and frozen rows, without requiring a symmetrizer. For bundled exchange matrices it also
retains the chosen positive symmetrizer. Words act in reading order; restriction, relabelling
and block sums transport the whole pattern.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Definition 2.4.
-/

public section

namespace TauCeti

variable {I K I' K' : Type*} [DecidableEq I] [DecidableEq K]

/-- Mutate an arbitrary rectangular integer matrix along a finite word in reading order. -/
def matrixMutationWord (row : K ↪ I) (B : Matrix I K ℤ) (w : List K) : Matrix I K ℤ :=
  w.foldl (matrixMutation row) B

/-- The raw matrix word action is the left fold of single-step mutation. -/
theorem matrixMutationWord_eq_foldl (row : K ↪ I) (B : Matrix I K ℤ) (w : List K) :
    matrixMutationWord row B w = w.foldl (matrixMutation row) B := by rfl

@[simp]
theorem matrixMutationWord_nil (row : K ↪ I) (B : Matrix I K ℤ) :
    matrixMutationWord row B [] = B := by rfl

@[simp]
theorem matrixMutationWord_cons (row : K ↪ I) (B : Matrix I K ℤ) (k : K) (w : List K) :
    matrixMutationWord row B (k :: w) = matrixMutationWord row (matrixMutation row B k) w := by rfl

/-- Concatenation performs the left word before the right word. -/
@[simp]
theorem matrixMutationWord_append (row : K ↪ I) (B : Matrix I K ℤ) (u v : List K) :
    matrixMutationWord row B (u ++ v) = matrixMutationWord row (matrixMutationWord row B u) v :=
  List.foldl_append

/-- Equal adjacent directions cancel inside an arbitrary matrix mutation word. -/
theorem matrixMutationWord_append_cons_cons_self (row : K ↪ I) (B : Matrix I K ℤ)
    (u v : List K) (k : K) :
    matrixMutationWord row B (u ++ k :: k :: v) = matrixMutationWord row B (u ++ v) :=
  foldl_append_cons_cons_of_involutive _ (matrixMutation_involutive row k) u v B

/-- Reversing a matrix mutation word inverts its action. -/
@[simp]
theorem matrixMutationWord_matrixMutationWord_reverse (row : K ↪ I) (B : Matrix I K ℤ)
    (w : List K) : matrixMutationWord row (matrixMutationWord row B w) w.reverse = B :=
  foldl_reverse_foldl_of_involutive _ (matrixMutation_involutive row) w B

/-- A reversed matrix mutation word is also a right inverse. -/
@[simp]
theorem matrixMutationWord_reverse_matrixMutationWord (row : K ↪ I) (B : Matrix I K ℤ)
    (w : List K) : matrixMutationWord row (matrixMutationWord row B w.reverse) w = B :=
  foldl_foldl_reverse_of_involutive _ (matrixMutation_involutive row) w B

/-- Matrix negation commutes with the raw word action. -/
@[simp]
theorem matrixMutationWord_neg (row : K ↪ I) (B : Matrix I K ℤ) (w : List K) :
    matrixMutationWord row (-B) w = -matrixMutationWord row B w :=
  List.foldl_hom Neg.neg (fun B k ↦ matrixMutation_neg row B k)

/-- Injective row restriction transports raw matrix words. Column injectivity follows from
compatibility with the mutable embeddings and is not a separate assumption. -/
theorem matrixMutationWord_submatrix [DecidableEq I'] [DecidableEq K'] {row : K ↪ I}
    {row' : K' ↪ I'} {f : I' → I} {g : K' → K} (hf : Function.Injective f)
    (h : ∀ k, f (row' k) = row (g k)) (B : Matrix I K ℤ) (w : List K') :
    matrixMutationWord row' (B.submatrix f g) w =
      (matrixMutationWord row B (w.map g)).submatrix f g := by
  simp only [matrixMutationWord, List.foldl_map]
  exact List.foldl_hom (fun B : Matrix I K ℤ ↦ B.submatrix f g)
    (fun B k ↦ matrixMutation_submatrix hf h B k)

/-- Taking the principal block commutes with the raw word action. -/
theorem matrixMutationWord_refl_submatrix_row (row : K ↪ I) (B : Matrix I K ℤ) (w : List K) :
    matrixMutationWord (Function.Embedding.refl K) (B.submatrix row id) w =
      (matrixMutationWord row B w).submatrix row id :=
  by simpa only [List.map_id] using
    (matrixMutationWord_submatrix (row' := Function.Embedding.refl K) (g := id)
      row.injective (fun _ ↦ rfl) B w)

/-- Every word of square matrix mutations preserves a given skew-symmetrizer. -/
protected theorem _root_.Matrix.IsSkewSymmetrizer.matrixMutationWord {B : Matrix K K ℤ}
    {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (w : List K) :
    (matrixMutationWord (Function.Embedding.refl K) B w).IsSkewSymmetrizer s := by
  induction w generalizing B with
  | nil => exact h
  | cons k _w ih => exact ih (h.matrixMutation k)

section fromBlocks

variable {I₁ I₂ K₁ K₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
  [DecidableEq K₁] [DecidableEq K₂]
  (row₁ : K₁ ↪ I₁) (row₂ : K₂ ↪ I₂) (B₁ : Matrix I₁ K₁ ℤ) (B₂ : Matrix I₂ K₂ ℤ)

/-- An arbitrary interleaved word acts on each diagonal block by its corresponding subword. -/
theorem matrixMutationWord_fromBlocks (w : List (K₁ ⊕ K₂)) :
    matrixMutationWord (row₁.sumMap row₂) (Matrix.fromBlocks B₁ 0 0 B₂) w =
      Matrix.fromBlocks (matrixMutationWord row₁ B₁ (w.filterMap Sum.getLeft?)) 0 0
        (matrixMutationWord row₂ B₂ (w.filterMap Sum.getRight?)) := by
  induction w generalizing B₁ B₂ with
  | nil => simp
  | cons k w ih =>
    cases k with
    | inl k =>
      simpa only [matrixMutationWord_cons, List.filterMap_cons, Sum.getLeft?_inl,
        Sum.getRight?_inl, List.foldl_cons, matrixMutation_fromBlocks_inl] using
        ih (matrixMutation row₁ B₁ k) B₂
    | inr k =>
      simpa only [matrixMutationWord_cons, List.filterMap_cons, Sum.getLeft?_inr,
        Sum.getRight?_inr, List.foldl_cons, matrixMutation_fromBlocks_inr] using
        ih B₁ (matrixMutation row₂ B₂ k)

/-- A word in the first block leaves the second block unchanged. -/
@[simp]
theorem matrixMutationWord_fromBlocks_inl (w : List K₁) :
    matrixMutationWord (row₁.sumMap row₂) (Matrix.fromBlocks B₁ 0 0 B₂) (w.map Sum.inl) =
      Matrix.fromBlocks (matrixMutationWord row₁ B₁ w) 0 0 B₂ := by
  simpa [Function.comp_def] using matrixMutationWord_fromBlocks row₁ row₂ B₁ B₂ (w.map Sum.inl)

/-- A word in the second block leaves the first block unchanged. -/
@[simp]
theorem matrixMutationWord_fromBlocks_inr (w : List K₂) :
    matrixMutationWord (row₁.sumMap row₂) (Matrix.fromBlocks B₁ 0 0 B₂) (w.map Sum.inr) =
      Matrix.fromBlocks B₁ 0 0 (matrixMutationWord row₂ B₂ w) := by
  simpa [Function.comp_def] using matrixMutationWord_fromBlocks row₁ row₂ B₁ B₂ (w.map Sum.inr)

end fromBlocks

/-- Raw matrix mutation words act by bijections with reversed-word inverses. -/
def matrixMutationWordEquiv (row : K ↪ I) (w : List K) : Matrix I K ℤ ≃ Matrix I K ℤ :=
  foldlEquiv (matrixMutation row) (matrixMutation_involutive row) w

@[simp]
theorem matrixMutationWordEquiv_apply (row : K ↪ I) (w : List K) (B : Matrix I K ℤ) :
    matrixMutationWordEquiv row w B = matrixMutationWord row B w := by
  exact foldlEquiv_apply _ _ _ _

@[simp]
theorem matrixMutationWordEquiv_symm (row : K ↪ I) (w : List K) :
    (matrixMutationWordEquiv row w).symm = matrixMutationWordEquiv row w.reverse :=
  foldlEquiv_symm _ _ _

@[simp]
theorem matrixMutationWordEquiv_nil (row : K ↪ I) :
    matrixMutationWordEquiv row [] = Equiv.refl (Matrix I K ℤ) := foldlEquiv_nil _ _

/-- Concatenation composes the raw matrix word bijections in reading order. -/
theorem matrixMutationWordEquiv_append (row : K ↪ I) (u v : List K) :
    matrixMutationWordEquiv row (u ++ v) =
      (matrixMutationWordEquiv row u).trans (matrixMutationWordEquiv row v) :=
  foldlEquiv_append _ _ _ _

namespace ExchangeMatrix


variable {I K I' K' : Type*} [DecidableEq I] [DecidableEq K] {row : K ↪ I}

/-- Apply a finite sequence of mutations, with the first letter acting first. -/
def mutationWord (B : ExchangeMatrix row) (w : List K) : ExchangeMatrix row :=
  w.foldl mutation B

/-- The bundled word action is the left fold of single-step mutation. -/
theorem mutationWord_eq_foldl (B : ExchangeMatrix row) (w : List K) :
    B.mutationWord w = w.foldl mutation B := (rfl)

@[simp]
theorem mutationWord_nil (B : ExchangeMatrix row) : B.mutationWord [] = B := (rfl)

@[simp]
theorem mutationWord_cons (B : ExchangeMatrix row) (k : K) (w : List K) :
    B.mutationWord (k :: w) = (B.mutation k).mutationWord w := (rfl)

/-- Concatenation applies the left word followed by the right word. -/
@[simp]
theorem mutationWord_append (B : ExchangeMatrix row) (u v : List K) :
    B.mutationWord (u ++ v) = (B.mutationWord u).mutationWord v :=
  List.foldl_append

/-- Forgetting the symmetrizer commutes with a mutation word. -/
@[simp]
theorem mutationWord_matrix (B : ExchangeMatrix row) (w : List K) :
    (B.mutationWord w).matrix = matrixMutationWord row B.matrix w := by
  exact (List.foldl_hom (fun B : ExchangeMatrix row ↦ B.matrix)
    (fun B k ↦ (B.mutation_matrix k).symm)).symm

/-- Every word retains the original positive symmetrizer. -/
@[simp]
theorem mutationWord_symmetrizer (B : ExchangeMatrix row) (w : List K) :
    (B.mutationWord w).symmetrizer = B.symmetrizer := by
  induction w generalizing B with
  | nil => rfl
  | cons k w ih => simpa using ih (B.mutation k)

/-- Reversing a word undoes its mutations. -/
@[simp]
theorem mutationWord_mutationWord_reverse (B : ExchangeMatrix row) (w : List K) :
    (B.mutationWord w).mutationWord w.reverse = B :=
  foldl_reverse_foldl_of_involutive mutation mutation_involutive w B

/-- A reversed word also gives a right inverse to the bundled action. -/
@[simp]
theorem mutationWord_reverse_mutationWord (B : ExchangeMatrix row) (w : List K) :
    (B.mutationWord w.reverse).mutationWord w = B :=
  foldl_foldl_reverse_of_involutive mutation mutation_involutive w B

/-- Equal adjacent directions cancel inside a bundled mutation word. -/
theorem mutationWord_append_cons_cons_self (B : ExchangeMatrix row) (u v : List K) (k : K) :
    B.mutationWord (u ++ k :: k :: v) = B.mutationWord (u ++ v) :=
  foldl_append_cons_cons_of_involutive mutation (mutation_involutive k) u v B

/-- Every bundled mutation word acts bijectively. -/
def mutationWordEquiv (w : List K) : ExchangeMatrix row ≃ ExchangeMatrix row :=
  foldlEquiv mutation mutation_involutive w

@[simp]
theorem mutationWordEquiv_apply (w : List K) (B : ExchangeMatrix row) :
    mutationWordEquiv w B = B.mutationWord w := foldlEquiv_apply _ _ _ _

@[simp]
theorem mutationWordEquiv_symm (w : List K) :
    (mutationWordEquiv (row := row) w).symm = mutationWordEquiv w.reverse :=
  foldlEquiv_symm _ _ _

@[simp]
theorem mutationWordEquiv_nil :
    mutationWordEquiv (row := row) [] = Equiv.refl (ExchangeMatrix row) := foldlEquiv_nil _ _

/-- Word concatenation composes bundled mutation bijections in reading order. -/
theorem mutationWordEquiv_append (u v : List K) :
    mutationWordEquiv (row := row) (u ++ v) =
      (mutationWordEquiv u).trans (mutationWordEquiv v) := foldlEquiv_append _ _ _ _

/-- Restriction of rows and mutable indices transports the entire mutation word. -/
theorem submatrix_mutationWord [DecidableEq I'] [DecidableEq K'] {row' : K' ↪ I'}
    {f : I' → I} {g : K' → K} (hf : Function.Injective f)
    (h : ∀ k, f (row' k) = row (g k)) (B : ExchangeMatrix row) (w : List K') :
    (B.mutationWord (w.map g)).submatrix f g h =
      (B.submatrix f g h).mutationWord w := by
  simp only [mutationWord, List.foldl_map]
  exact (List.foldl_hom (fun B : ExchangeMatrix row ↦ B.submatrix f g h)
    (fun B k ↦ (B.submatrix_mutation hf h k).symm)).symm

/-- Taking the principal block commutes with every mutation word. -/
@[simp]
theorem principal_mutationWord (B : ExchangeMatrix row) (w : List K) :
    (B.mutationWord w).principal = B.principal.mutationWord w := by
  exact (List.foldl_hom (fun B : ExchangeMatrix row ↦ B.principal)
    (fun B k ↦ (B.principal_mutation k).symm)).symm

/-- Simultaneous relabelling transports every direction of a word. -/
theorem reindex_mutationWord [DecidableEq I'] [DecidableEq K'] {row' : K' ↪ I'}
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (B : ExchangeMatrix row) (w : List K) :
    reindex eI eK h (B.mutationWord w) = (reindex eI eK h B).mutationWord (w.map eK) := by
  simp only [mutationWord, List.foldl_map]
  exact (List.foldl_hom (reindex eI eK h)
    (fun B k ↦ B.mutation_reindex eI eK h k)).symm

section sum

variable {I₁ I₂ K₁ K₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
  [DecidableEq K₁] [DecidableEq K₂] {row₁ : K₁ ↪ I₁} {row₂ : K₂ ↪ I₂}
  (B₁ : ExchangeMatrix row₁) (B₂ : ExchangeMatrix row₂)

/-- Mutation by an arbitrary interleaved word splits into the two projected subwords. -/
theorem mutationWord_sum (w : List (K₁ ⊕ K₂)) :
    (B₁.sum B₂).mutationWord w =
      (B₁.mutationWord (w.filterMap Sum.getLeft?)).sum
        (B₂.mutationWord (w.filterMap Sum.getRight?)) := by
  ext : 1
  · simp only [mutationWord_matrix, sum_matrix]
    exact matrixMutationWord_fromBlocks row₁ row₂ B₁.matrix B₂.matrix w
  · simp

/-- A mutation word in the first summand fixes the second summand. -/
@[simp]
theorem mutationWord_sum_inl (w : List K₁) :
    (B₁.sum B₂).mutationWord (w.map Sum.inl) = (B₁.mutationWord w).sum B₂ := by
  simpa [Function.comp_def] using mutationWord_sum B₁ B₂ (w.map Sum.inl)

/-- A mutation word in the second summand fixes the first summand. -/
@[simp]
theorem mutationWord_sum_inr (w : List K₂) :
    (B₁.sum B₂).mutationWord (w.map Sum.inr) = B₁.sum (B₂.mutationWord w) := by
  simpa [Function.comp_def] using mutationWord_sum B₁ B₂ (w.map Sum.inr)

end sum

end ExchangeMatrix

end TauCeti
