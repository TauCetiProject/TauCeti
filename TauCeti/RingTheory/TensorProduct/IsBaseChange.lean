/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of a tensor product, and injectivity of the lifted map

If `f : M →ₗ[R] N` and `g : M' →ₗ[R] N'` exhibit the `S`-modules `N` and `N'` as base changes of
`M` and `M'` along `R → S`, then `m ⊗ m' ↦ f m ⊗ g m'` exhibits `N ⊗[S] N'` as the base change of
`M ⊗[R] M'`. On the concrete models this is Mathlib's
`TensorProduct.AlgebraTensorModule.distribBaseChange`,
`S ⊗[R] (M ⊗[R] M') ≃ (S ⊗[R] M) ⊗[S] (S ⊗[R] M')`; the statement here is its form for the
abstract `IsBaseChange` interface, alongside Mathlib's `IsBaseChange.prodMap` for products.
Mathlib's `isBaseChange_tensorProduct_map` is the analogous statement when only one factor is
base changed and the tensor product stays over the base ring.

If `f : M →ₗ[R] N` exhibits `N` as the base change of `M` along `R → S`, then the `S`-linear map
`S ⊗[R] M →ₗ[S] N` it induces, Mathlib's `LinearMap.liftBaseChange`, is injective: it is the
equivalence `IsBaseChange.equiv`.

## Main results

* `IsBaseChange.tensorProduct`: a tensor product of base changes is a base change of the tensor
  product.
* `IsBaseChange.liftBaseChange_injective`: the map `S ⊗[R] M →ₗ[S] N` induced by a base change is
  injective.
-/

public section

open scoped TensorProduct

variable {R S M M' N N' : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommMonoid N'] [Module R N'] [Module S N'] [IsScalarTower R S N']

/-- **Base change commutes with tensor products.** If `f` and `g` exhibit `N` and `N'` as base
changes of `M` and `M'` along `R → S`, then `m ⊗ m' ↦ f m ⊗ g m'` exhibits `N ⊗[S] N'` as the
base change of `M ⊗[R] M'`. -/
theorem IsBaseChange.tensorProduct {f : M →ₗ[R] N} {g : M' →ₗ[R] N'}
    (hf : IsBaseChange S f) (hg : IsBaseChange S g) :
    IsBaseChange S (TensorProduct.mapOfCompatibleSMul S R R N N' ∘ₗ TensorProduct.map f g) := by
  refine IsBaseChange.of_equiv
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R S M M').trans
      (TensorProduct.congr hf.equiv hg.equiv)) fun x ↦ ?_
  induction x with
  | tmul m m' => simp [IsBaseChange.equiv_tmul]
  | add x y hx hy => simp_all [TensorProduct.tmul_add]

/-- If `f` exhibits `N` as the base change of `M` along `R → S`, then the induced `S`-linear map
`f.liftBaseChange S : S ⊗[R] M →ₗ[S] N` is injective, since it is the equivalence `hf.equiv`. -/
theorem IsBaseChange.liftBaseChange_injective {f : M →ₗ[R] N} (hf : IsBaseChange S f) :
    Function.Injective (f.liftBaseChange S) := by
  have : f.liftBaseChange S = hf.equiv.toLinearMap := by
    ext
    simp [IsBaseChange.equiv_tmul]
  rw [this]
  exact hf.equiv.injective
