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
(`CategoryTheory.SimplicialObject.δ_comp_σ_self`). When the target level is Hausdorff, this
retraction makes `X.σ i` a closed embedding (`CategoryTheory.SimplicialObject.isClosedEmbedding_σ`)
and the degenerate locus in that degree closed
(`CategoryTheory.SimplicialObject.isClosed_degenerate`).
-/

public section

open CategoryTheory Topology
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

universe u

/-- Each degeneracy of a simplicial space is an embedding: the face deleting the repeated
simplex is a continuous left inverse. -/
theorem isEmbedding_σ (X : SimplicialObject TopCat.{u}) {n : ℕ} (i : Fin (n + 1)) :
    IsEmbedding (X.σ i) :=
  .of_leftInverse (f := X.δ i.castSucc)
    (fun x ↦ by rw [← ConcreteCategory.comp_apply, δ_comp_σ_self, ConcreteCategory.id_apply])
    (ContinuousMap.continuous _) (ContinuousMap.continuous _)

/-- In a simplicial space whose `(n + 1)`-simplices form a Hausdorff space, each degeneracy
`X.σ i : X _⦋n⦌ ⟶ X _⦋n + 1⦌` is a closed embedding, as a continuous section of `X.δ i.castSucc`. -/
theorem isClosedEmbedding_σ (X : SimplicialObject TopCat.{u}) {n : ℕ} [T2Space (X _⦋n + 1⦌)]
    (i : Fin (n + 1)) : IsClosedEmbedding (X.σ i) :=
  Function.LeftInverse.isClosedEmbedding (f := X.δ i.castSucc)
    (fun x ↦ by rw [← ConcreteCategory.comp_apply, δ_comp_σ_self, ConcreteCategory.id_apply])
    (ContinuousMap.continuous _) (ContinuousMap.continuous _)

/-- In a simplicial space whose `n`-simplices form a Hausdorff space, the degenerate `n`-simplices
form a closed subset. -/
theorem isClosed_degenerate (X : SimplicialObject TopCat.{u}) (n : ℕ) [T2Space (X _⦋n⦌)] :
    IsClosed (X := X _⦋n⦌) (SSet.degenerate (X ⋙ forget TopCat) n) := by
  cases n with
  | zero => exact SSet.degenerate_zero (X ⋙ forget TopCat) ▸ isClosed_empty
  | succ n =>
    rw [SSet.degenerate_eq_iUnion_range_σ]
    exact isClosed_iUnion_of_finite fun i ↦ (X.isClosedEmbedding_σ i).isClosed_range

end CategoryTheory.SimplicialObject
