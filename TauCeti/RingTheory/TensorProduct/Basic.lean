/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Products of pure tensors and bilinear multiplication lifts

In the tensor product `A ⊗[R] B` of commutative `R`-algebras, a finite product of pure tensors
is the pure tensor of the products: `∏ i ∈ s, a i ⊗ₜ b i = (∏ i ∈ s, a i) ⊗ₜ ∏ i ∈ s, b i`.
This is the multiplicative counterpart of `TensorProduct.sum_tmul` and `TensorProduct.tmul_sum`,
and extends `Algebra.TensorProduct.tmul_pow` from powers to products. For ordered list products
neither factor needs to be commutative.

For `R`-linear maps `f : M →ₗ[R] C` and `g : N →ₗ[R] C` into an `R`-algebra (or non-unital,
non-associative `R`-bilinear multiplication target) `C`, `LinearMap.mulMap f g` is the induced
`R`-linear map `M ⊗[R] N →ₗ[R] C` sending `m ⊗ₜ n` to `f m * g n`.
-/

public section

open TensorProduct

namespace LinearMap

section MulMap

variable {R M N C : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [NonUnitalNonAssocSemiring C] [Module R C]
  [SMulCommClass R C C] [IsScalarTower R C C]

/-- The `R`-linear map `M ⊗[R] N →ₗ[R] C` sending `m ⊗ₜ n` to `f m * g n`. -/
def mulMap (f : M →ₗ[R] C) (g : N →ₗ[R] C) : M ⊗[R] N →ₗ[R] C :=
  LinearMap.mul' R C ∘ₗ TensorProduct.map f g

/-- Evaluating `LinearMap.mulMap` on a pure tensor multiplies the values of the two linear maps. -/
@[simp]
theorem mulMap_tmul (f : M →ₗ[R] C) (g : N →ₗ[R] C) (m : M) (n : N) :
    mulMap f g (m ⊗ₜ[R] n) = f m * g n := by
  simp [mulMap]

end MulMap

end LinearMap

/-- The ordered product of pure tensors is the pure tensor of the ordered products.
Neither algebra is required to be commutative. -/
theorem List.prod_map_tmul {R A B ι : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    (l : List ι) (a : ι → A) (b : ι → B) :
    (l.map fun i ↦ a i ⊗ₜ[R] b i).prod = (l.map a).prod ⊗ₜ[R] (l.map b).prod := by
  induction l with
  | nil => simp [Algebra.TensorProduct.one_def]
  | cons i l ih => simp only [List.map_cons, List.prod_cons, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

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

omit [CommSemiring B] [Algebra R B] in
/-- The product of a list of pure tensors in `A ⊗[R] B`, with `A` commutative, is the pure tensor
of the product of the left factors and the ordered product of the right factors. -/
theorem list_prod_ofFn_tmul [Semiring B] [Algebra R B] {n : ℕ} (a : Fin n → A) (b : Fin n → B) :
    (List.ofFn fun t ↦ a t ⊗ₜ[R] b t).prod = (∏ t, a t) ⊗ₜ[R] (List.ofFn b).prod := by
  simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_def] using
    List.prod_map_tmul (R := R) (List.ofFn (fun i : Fin n ↦ i)) a b

end Algebra.TensorProduct
