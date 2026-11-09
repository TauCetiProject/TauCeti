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
(`CategoryTheory.SimplicialObject.δ_comp_σ_self`).
-/

public section

open CategoryTheory Topology

namespace CategoryTheory.SimplicialObject

/-- Each degeneracy of a simplicial space is an embedding: the face deleting the repeated
simplex is a continuous left inverse. -/
theorem isEmbedding_σ (X : SimplicialObject TopCat) {n : ℕ} (i : Fin (n + 1)) :
    IsEmbedding (X.σ i) :=
  .of_leftInverse (f := X.δ i.castSucc)
    (fun x ↦ by rw [← ConcreteCategory.comp_apply, δ_comp_σ_self, ConcreteCategory.id_apply])
    (ContinuousMap.continuous _) (ContinuousMap.continuous _)

end CategoryTheory.SimplicialObject
