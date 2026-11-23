/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.RingTheory.Flat.Domain
-- Used in the proof of `TauCeti.finrank_piTensorPower`.
import TauCeti.LinearAlgebra.PiTensorProduct.Basis.Basic

/-!
# The rank of tensor products and tensor powers

Over an integral domain, the image `Submodule.map₂ (TensorProduct.mk R M N) P Q` of the pure
tensors of two free submodules `P` and `Q` has `finrank` the product of their `finrank`s
(`Submodule.finrank_map₂_tensorProductMk`). It is the image of `P ⊗ Q → M ⊗ N`, which is injective
because free modules are flat and `R` is a domain
(`TensorProduct.map_injective_of_flat_flat_of_isDomain`). Over a field every subspace is free, so
this computes the dimension of the tensor product of any two subspaces.

For finite tensor powers of coordinate spaces `κ → R`, `TauCeti.finrank_piTensorPower` computes the
`finrank` `Nat.card κ ^ Nat.card ι` from the coordinate monomial basis `TauCeti.piTensorPowerBasis`.
-/

public section

open Module
open scoped TensorProduct

namespace Submodule

/-- Over an integral domain, the submodule spanned by the pure tensors of two free submodules has
`finrank` the product of their `finrank`s. Over a field this is the dimension of the tensor product
of any two subspaces. -/
@[simp]
theorem finrank_map₂_tensorProductMk {R M N : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (P : Submodule R M) (Q : Submodule R N)
    [Module.Free R P] [Module.Free R Q] :
    finrank R (map₂ (TensorProduct.mk R M N) P Q) = finrank R P * finrank R Q := by
  rw [← TensorProduct.range_mapIncl,
    LinearMap.finrank_range_of_inj (TensorProduct.map_injective_of_flat_flat_of_isDomain
      P.subtype Q.subtype P.subtype_injective Q.subtype_injective),
    Module.finrank_tensorProduct]

end Submodule

namespace TauCeti

/-- **The dimension of `(κ → R)^{⊗ι}` is `Nat.card κ ^ Nat.card ι`**, read off the coordinate
monomial basis `TauCeti.piTensorPowerBasis`, whose index type is `ι → κ`. -/
theorem finrank_piTensorPower (R : Type*) [CommSemiring R] [StrongRankCondition R]
    (ι κ : Type*) [Finite ι] [Finite κ] :
    Module.finrank R (⨂[R] _ : ι, κ → R) = Nat.card κ ^ Nat.card ι := by
  rw [Module.finrank_eq_nat_card_basis (piTensorPowerBasis R ι κ), Nat.card_fun]

end TauCeti
