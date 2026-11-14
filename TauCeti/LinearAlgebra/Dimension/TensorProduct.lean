/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic

/-!
# The dimension of a tensor product of subspaces

Over a field, the image `Submodule.map₂ (TensorProduct.mk K M N) P Q` of the pure tensors of two
subspaces `P` and `Q` has dimension the product of their dimensions
(`Submodule.finrank_map₂_mk`). It is the image of `P ⊗ Q → M ⊗ N`, which is injective by flatness.
-/

public section

open Module

namespace Submodule

/-- The tensor product of two subspaces has dimension the product of their dimensions. -/
theorem finrank_map₂_mk {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : Submodule K M) (Q : Submodule K N) :
    finrank K (Submodule.map₂ (TensorProduct.mk K M N) P Q) = finrank K P * finrank K Q := by
  rw [← TensorProduct.range_mapIncl,
    LinearMap.finrank_range_of_inj (Module.Flat.tensorProduct_mapIncl_injective_of_right P Q),
    Module.finrank_tensorProduct]

end Submodule
