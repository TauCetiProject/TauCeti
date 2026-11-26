/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Square.Embedding

/-!
# Tensor-flip parity of the two adjoint embeddings

Naturality of the tensor flip transfers the signs of the forward products
through trace duality to their transposes.
-/

public section

namespace TauCeti.AdjointSquare

open scoped TensorProduct

variable {K : Type*} [Field K] {n : ℕ} [NeZero (n : K)]

local notation "V" => LieAlgebra.SpecialLinear.sl (Fin n) K

/-- The tensor flip negates the image of the transposed Lie bracket. -/
@[simp]
theorem comm_alternatingEmbeddingMap_eq_neg (X : V) :
    TensorProduct.comm K V V (alternatingEmbeddingMap K n X) = -alternatingEmbeddingMap K n X := by
  apply squareTrace.injective
  apply LinearMap.ext
  intro t
  simp only [squareTrace_comm, alternatingEmbeddingMap_pairing,
    alternatingProductMap_comm_eq_neg, map_neg, LinearMap.neg_apply]

/-- The tensor flip fixes the image of the transposed symmetric product. -/
@[simp]
theorem comm_symmetricEmbeddingMap (X : V) :
    TensorProduct.comm K V V (symmetricEmbeddingMap K n X) = symmetricEmbeddingMap K n X := by
  apply squareTrace.injective
  apply LinearMap.ext
  intro t
  rw [squareTrace_comm, symmetricEmbeddingMap_pairing, symmetricProductMap_comm,
    symmetricEmbeddingMap_pairing]

end TauCeti.AdjointSquare
