/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Simplicial spaces

A simplicial space is a simplicial object `X : SimplicialObject TopCat`. Each degeneracy
`X.σ i` is an embedding (`CategoryTheory.SimplicialObject.isEmbedding_σ`): the face
`X.δ i.castSucc` deleting the repeated simplex is a continuous left inverse
(`CategoryTheory.SimplicialObject.δ_comp_σ_self`). When the target level `X _⦋n + 1⦌` is
Hausdorff, this continuous retraction forces the image of `X.σ i` to be closed, so each degeneracy
is a closed embedding (`CategoryTheory.SimplicialObject.isClosedEmbedding_σ`).
-/

public section

open CategoryTheory Topology

open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- Each degeneracy of a simplicial space is an embedding: the face deleting the repeated
simplex is a continuous left inverse. -/
theorem isEmbedding_σ (X : SimplicialObject TopCat) {n : ℕ} (i : Fin (n + 1)) :
    IsEmbedding (X.σ i) :=
  .of_leftInverse (f := X.δ i.castSucc)
    (fun x ↦ by rw [← ConcreteCategory.comp_apply, δ_comp_σ_self, ConcreteCategory.id_apply])
    (ContinuousMap.continuous _) (ContinuousMap.continuous _)

/-- Each degeneracy of a simplicial space into a Hausdorff level is a closed embedding: its image
is a retract of the Hausdorff space `X _⦋n + 1⦌`. -/
theorem isClosedEmbedding_σ (X : SimplicialObject TopCat) {n : ℕ} [T2Space (X _⦋n + 1⦌)]
    (i : Fin (n + 1)) : IsClosedEmbedding (X.σ i) :=
  ⟨isEmbedding_σ X i,
    Function.LeftInverse.isClosed_range (f := X.δ i.castSucc)
      (fun x ↦ by rw [← ConcreteCategory.comp_apply, δ_comp_σ_self, ConcreteCategory.id_apply])
      (ContinuousMap.continuous _) (ContinuousMap.continuous _)⟩

end CategoryTheory.SimplicialObject
