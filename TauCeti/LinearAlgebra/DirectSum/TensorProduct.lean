/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Naturality of tensor products with direct sums

Supplements Mathlib's `TensorProduct.directSumLeft`, which distributes a tensor product over a
direct sum in its first factor, with naturality in the second factor.

## Main results

* `TensorProduct.directSumLeft_lTensor`: `TensorProduct.directSumLeft` commutes with
  `LinearMap.lTensor` on the second tensor factor.
-/

public section

namespace TensorProduct

open scoped DirectSum TensorProduct

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  {ι : Type*} [DecidableEq ι] {M : ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, Module S (M i)]
  [∀ i, IsScalarTower R S (M i)]
  {N₁ N₂ : Type*} [AddCommMonoid N₁] [Module R N₁] [AddCommMonoid N₂] [Module R N₂]

/-- `TensorProduct.directSumLeft` is natural in the second tensor factor: applying `1 ⊗ f` before
distributing over the direct sum agrees with applying `1 ⊗ f` on each summand. -/
@[simp]
theorem directSumLeft_lTensor (f : N₁ →ₗ[R] N₂) (t : (⨁ i, M i) ⊗[R] N₁) :
    directSumLeft R S M N₂ (f.lTensor (⨁ i, M i) t) =
      DirectSum.lmap (fun i ↦ f.lTensor (M i)) (directSumLeft R S M N₁ t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    ext i
    simp [directSumLeft_tmul]
  | add t₁ t₂ h₁ h₂ => simp [map_add, h₁, h₂]

end TensorProduct
