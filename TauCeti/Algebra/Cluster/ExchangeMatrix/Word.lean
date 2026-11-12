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

Words act in reading order: the first letter mutates first. The action preserves the chosen
symmetrizer, reverses by reversing the word, and commutes with restriction and relabelling.
The raw matrix action is `List.foldl (matrixMutation row)`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Definition 2.4.
-/

public section

namespace TauCeti.ExchangeMatrix

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
    (B.mutationWord w).matrix = w.foldl (matrixMutation row) B.matrix := by
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
theorem mutationWord_reverse (B : ExchangeMatrix row) (w : List K) :
    (B.mutationWord w).mutationWord w.reverse = B :=
  foldl_reverse_foldl_of_involutive mutation mutation_involutive w B

/-- Restriction of rows and mutable indices transports the entire mutation word. -/
theorem submatrix_mutationWord [DecidableEq I'] [DecidableEq K'] {row' : K' ↪ I'}
    {f : I' → I} {g : K' → K} (hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ k, f (row' k) = row (g k)) (B : ExchangeMatrix row) (w : List K') :
    (B.mutationWord (w.map g)).submatrix f g h =
      (B.submatrix f g h).mutationWord w := by
  simp only [mutationWord, List.foldl_map]
  exact (List.foldl_hom (fun B : ExchangeMatrix row ↦ B.submatrix f g h)
    (fun B k ↦ (B.submatrix_mutation hf hg h k).symm)).symm

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

end TauCeti.ExchangeMatrix
