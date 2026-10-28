/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Products of pure tensors

In the tensor product `A ⊗[R] B` of commutative `R`-algebras, a finite product of pure tensors
is the pure tensor of the products: `∏ i ∈ s, a i ⊗ₜ b i = (∏ i ∈ s, a i) ⊗ₜ ∏ i ∈ s, b i`.
This is the multiplicative counterpart of `TensorProduct.sum_tmul` and `TensorProduct.tmul_sum`,
and extends `Algebra.TensorProduct.tmul_pow` from powers to products.
-/

public section

open TensorProduct

namespace Algebra.TensorProduct

variable {R A B ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [CommSemiring B]
  [Algebra R B]

/-- A finite product of pure tensors is the pure tensor of the products. -/
@[simp]
theorem prod_tmul (s : Finset ι) (a : ι → A) (b : ι → B) :
    ∏ i ∈ s, a i ⊗ₜ[R] b i = (∏ i ∈ s, a i) ⊗ₜ[R] ∏ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [one_def]
  | insert i s hi ih => simp [Finset.prod_insert hi, ih]

end Algebra.TensorProduct
