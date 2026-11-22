/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Embedding

/-!
# Tensor-flip parity of the two adjoint embeddings

Naturality of the tensor flip transfers the signs of the forward products
through trace duality to their transposes.
-/

public section

namespace TauCeti.AdjointSquare

open scoped TensorProduct

variable {K : Type*} [Field K] [NeZero (3 : K)]

local notation "V" => LieAlgebra.SpecialLinear.sl (Fin 3) K

private theorem tensor_trace_ext {A B : V ⊗[K] V}
    (h : ∀ T, TensorProduct.dualDistrib K V V
        (TensorProduct.map (TauCeti.traceDual K 3).toLinearMap (TauCeti.traceDual K 3).toLinearMap
          A) T =
      TensorProduct.dualDistrib K V V
        (TensorProduct.map (TauCeti.traceDual K 3).toLinearMap (TauCeti.traceDual K 3).toLinearMap
          B) T) : A = B := by
  apply (TensorProduct.congr (TauCeti.traceDual K 3) (TauCeti.traceDual K 3)).injective
  apply (TensorProduct.dualDistribEquiv K V V).injective
  apply LinearMap.ext
  intro T
  -- Coercing `dualDistribEquiv` agrees with applying its `toLinearMap`.
  change (TensorProduct.dualDistribEquiv K V V).toLinearMap _ T =
    (TensorProduct.dualDistribEquiv K V V).toLinearMap _ T
  rw [TensorProduct.toLinearMap_dualDistribEquiv]
  exact h T

/-- The tensor flip negates the image of the transposed Lie bracket. -/
theorem comm_alternatingEmbeddingMap (X : V) :
    TensorProduct.comm K V V (alternatingEmbeddingMap X) = -alternatingEmbeddingMap X := by
  apply tensor_trace_ext
  intro T
  rw [TensorProduct.map_comm, ← TensorProduct.dualDistrib_apply_comm,
    alternatingEmbeddingMap_pairing, TauCeti.comm_alternatingProductMap, map_neg, map_neg,
    map_neg, LinearMap.neg_apply, alternatingEmbeddingMap_pairing]

/-- The tensor flip fixes the image of the transposed symmetric product. -/
theorem comm_symmetricEmbeddingMap (X : V) :
    TensorProduct.comm K V V (symmetricEmbeddingMap X) = symmetricEmbeddingMap X := by
  apply tensor_trace_ext
  intro T
  rw [TensorProduct.map_comm, ← TensorProduct.dualDistrib_apply_comm,
    symmetricEmbeddingMap_pairing, comm_symmetricProductMap, symmetricEmbeddingMap_pairing]

end TauCeti.AdjointSquare
