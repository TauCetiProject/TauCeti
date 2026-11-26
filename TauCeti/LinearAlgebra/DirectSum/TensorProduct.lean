/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Components of tensor products of direct sums

Mathlib's `TensorProduct.directSumLeft` and `TensorProduct.directSumRight` distribute a tensor
product over a direct sum in one factor. This file identifies their components with the tensor
products of the component projections, and deduces that an element of
`(⨁ i, M₁ i) ⊗ (⨁ j, M₂ j)` is determined by its bihomogeneous components
`(component i ⊗ component j) z`. This is the extensionality principle needed to compare maps
into a tensor square of a graded object one bidegree at a time, as for the coproduct of a tensor
coalgebra.

## Main results

* `TensorProduct.directSumLeft_apply`, `TensorProduct.directSumRight_apply`: the components of
  the distributivity equivalences are the component projections tensored with the identity.
* `TensorProduct.ext_map_component`: an element of a tensor product of two direct sums is
  determined by its bihomogeneous components.
-/

public section

open scoped DirectSum TensorProduct

namespace TensorProduct

variable {R : Type*} [CommSemiring R] {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]
  {M₁ : ι₁ → Type*} {M₂ : ι₂ → Type*} {M₁' M₂' : Type*}
  [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)] [∀ i, AddCommMonoid (M₂ i)]
  [∀ i, Module R (M₂ i)] [AddCommMonoid M₁'] [Module R M₁'] [AddCommMonoid M₂'] [Module R M₂']

section Algebra

variable {S : Type*} [Semiring S] [Algebra R S]

/-- The `i`-th component of `(⨁ i, M₁ i) ⊗ M₂' ≃ ⨁ i, M₁ i ⊗ M₂'` is the `i`-th component
projection tensored with the identity. -/
theorem directSumLeft_apply [∀ i, Module S (M₁ i)] [∀ i, IsScalarTower R S (M₁ i)]
    (z : (⨁ i, M₁ i) ⊗[R] M₂') (i : ι₁) :
    directSumLeft R S M₁ M₂' z i = (DirectSum.component R ι₁ M₁ i).rTensor M₂' z := by
  induction z using TensorProduct.inductionOn with
  | tmul m n => rw [directSumLeft_tmul, LinearMap.rTensor_tmul, DirectSum.apply_eq_component R]
  | add z w hz hw => simp only [map_add, DirectSum.add_apply, hz, hw]

/-- The `i`-th component of `M₁' ⊗ (⨁ i, M₂ i) ≃ ⨁ i, M₁' ⊗ M₂ i` is the `i`-th component
projection tensored with the identity. -/
theorem directSumRight_apply [Module S M₁'] [IsScalarTower R S M₁'] (z : M₁' ⊗[R] ⨁ i, M₂ i)
    (i : ι₂) :
    directSumRight R S M₁' M₂ z i = (DirectSum.component R ι₂ M₂ i).lTensor M₁' z := by
  induction z using TensorProduct.inductionOn with
  | tmul m n => rw [directSumRight_tmul, LinearMap.lTensor_tmul, DirectSum.apply_eq_component R]
  | add z w hz hw => simp only [map_add, DirectSum.add_apply, hz, hw]

end Algebra

omit [DecidableEq ι₁] [DecidableEq ι₂] in
/-- An element of a tensor product of two direct sums is determined by its bihomogeneous
components. -/
theorem ext_map_component {z w : (⨁ i, M₁ i) ⊗[R] ⨁ j, M₂ j}
    (h : ∀ i j, map (DirectSum.component R ι₁ M₁ i) (DirectSum.component R ι₂ M₂ j) z =
      map (DirectSum.component R ι₁ M₁ i) (DirectSum.component R ι₂ M₂ j) w) : z = w := by
  classical
  refine (directSumLeft R R M₁ _).injective (DFinsupp.ext fun i ↦ ?_)
  rw [directSumLeft_apply, directSumLeft_apply]
  refine (directSumRight R R (M₁ i) M₂).injective (DFinsupp.ext fun j ↦ ?_)
  rw [directSumRight_apply, directSumRight_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    LinearMap.lTensor_comp_rTensor, h]

end TensorProduct
