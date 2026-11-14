/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Simplicial spaces

A simplicial space is a simplicial object `X : SimplicialObject TopCat`. Each degeneracy
`X.σ i` is an embedding (`CategoryTheory.SimplicialObject.isEmbedding_σ`): the face
`X.δ i.castSucc` deleting the repeated simplex is a continuous left inverse
(`CategoryTheory.SimplicialObject.δ_comp_σ_self`), hence a closed embedding whenever the codomain
is Hausdorff (`CategoryTheory.SimplicialObject.isClosedEmbedding_σ`). Consequently, the degenerate
simplices in a degree form a closed subset whenever the degeneracies landing in that degree are
closed embeddings (`CategoryTheory.SimplicialObject.isClosed_degenerate_succ`,
`CategoryTheory.SimplicialObject.isClosed_degenerate`,
`CategoryTheory.SimplicialObject.isClosed_degenerate_of_t2Space`).
-/

public section

open CategoryTheory Simplicial Topology

namespace CategoryTheory.SimplicialObject

/-- Each degeneracy of a simplicial space is an embedding: the face deleting the repeated
simplex is a continuous left inverse. -/
theorem isEmbedding_σ (X : SimplicialObject TopCat) {n : ℕ} (i : Fin (n + 1)) :
    IsEmbedding (X.σ i) :=
  .of_leftInverse (f := X.δ i.castSucc)
    (fun x ↦ by rw [← ConcreteCategory.comp_apply, δ_comp_σ_self, ConcreteCategory.id_apply])
    (ContinuousMap.continuous _) (ContinuousMap.continuous _)

/-- Each degeneracy of a simplicial space into a Hausdorff level is a closed embedding. -/
theorem isClosedEmbedding_σ (X : SimplicialObject TopCat) {n : ℕ} [T2Space (X _⦋n + 1⦌)]
    (i : Fin (n + 1)) : IsClosedEmbedding (X.σ i) :=
  Function.LeftInverse.isClosedEmbedding (f := X.δ i.castSucc)
    (fun x ↦ by rw [← ConcreteCategory.comp_apply, δ_comp_σ_self, ConcreteCategory.id_apply])
    (ContinuousMap.continuous _) (ContinuousMap.continuous _)

/-- If every degeneracy `X.σ i` (`i : Fin (n + 1)`) is a closed embedding, the degenerate
`(n + 1)`-simplices form a closed subset of `X _⦋n + 1⦌`. -/
theorem isClosed_degenerate_succ (X : SimplicialObject TopCat) {n : ℕ}
    (hσ : ∀ i : Fin (n + 1), IsClosedEmbedding (X.σ i)) :
    IsClosed (X := X _⦋n + 1⦌) (SSet.degenerate (X ⋙ forget TopCat) (n + 1)) := by
  rw [SSet.degenerate_eq_iUnion_range_σ]
  exact isClosed_iUnion_of_finite fun i ↦ (hσ i).isClosed_range

/-- If all degeneracies of a simplicial space are closed embeddings, the degenerate simplices form
a closed subset in every degree. -/
theorem isClosed_degenerate (X : SimplicialObject TopCat)
    (hσ : ∀ {m : ℕ} (i : Fin (m + 1)), IsClosedEmbedding (X.σ i)) (n : ℕ) :
    IsClosed (X := X _⦋n⦌) (SSet.degenerate (X ⋙ forget TopCat) n) := by
  cases n with
  | zero => exact SSet.degenerate_zero (X ⋙ forget TopCat) ▸ isClosed_empty
  | succ m => exact X.isClosed_degenerate_succ hσ

/-- In any Hausdorff degree `X _⦋n⦌`, the degenerate `n`-simplices form a closed subset. -/
theorem isClosed_degenerate_of_t2Space (X : SimplicialObject TopCat) (n : ℕ) [T2Space (X _⦋n⦌)] :
    IsClosed (X := X _⦋n⦌) (SSet.degenerate (X ⋙ forget TopCat) n) := by
  cases n with
  | zero => exact SSet.degenerate_zero (X ⋙ forget TopCat) ▸ isClosed_empty
  | succ m => exact X.isClosed_degenerate_succ fun i ↦ X.isClosedEmbedding_σ i

end CategoryTheory.SimplicialObject
