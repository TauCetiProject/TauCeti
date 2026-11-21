/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Products of pure tensors

In the tensor product `A ⊗[R] B` of commutative `R`-algebras, a finite product of pure tensors
is the pure tensor of the products: `∏ i ∈ s, a i ⊗ₜ b i = (∏ i ∈ s, a i) ⊗ₜ ∏ i ∈ s, b i`.
This is the multiplicative counterpart of `TensorProduct.sum_tmul` and `TensorProduct.tmul_sum`,
and extends `Algebra.TensorProduct.tmul_pow` from powers to products. For ordered list products
neither factor needs to be commutative. Likewise, multiplying two adjacent entries of a tuple of
pure tensors (`Fin.contractNth`) multiplies the adjacent entries of both factor tuples.

For any `A ⊗[R] B`-algebra `Q` forming scalar towers with both `A` and `B`,
`TauCeti.algebraMap_tensorProduct_tmul` expands `algebraMap (A ⊗[R] B) Q (a ⊗ₜ b)` as the product
`algebraMap A Q a * algebraMap B Q b`.
-/

public section

open TensorProduct

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

/-- Multiplying two adjacent entries of a tuple of pure tensors multiplies the adjacent entries of
both factor tuples. Neither algebra is required to be commutative. -/
@[simp]
theorem Algebra.TensorProduct.contractNth_tmul {R A B : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Semiring B] [Algebra R B] {n : ℕ} (j : Fin (n + 1)) (a : Fin (n + 1) → A)
    (b : Fin (n + 1) → B) (i : Fin n) :
    Fin.contractNth j (· * ·) (fun k ↦ a k ⊗ₜ[R] b k) i =
      Fin.contractNth j (· * ·) a i ⊗ₜ[R] Fin.contractNth j (· * ·) b i := by
  simp only [Fin.contractNth]
  split_ifs <;> simp [Algebra.TensorProduct.tmul_mul_tmul]

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

namespace TauCeti

section RightAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- In any `A ⊗[R] B`-algebra `Q` compatible with both factors, `algebraMap` sends a pure tensor
`a ⊗ₜ b` to `algebraMap A Q a * algebraMap B Q b`. -/
theorem algebraMap_tensorProduct_tmul {R A B Q : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Semiring Q] [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) Q]
    [Algebra A Q] [Algebra B Q] [IsScalarTower A (A ⊗[R] B) Q] [IsScalarTower B (A ⊗[R] B) Q]
    (a : A) (b : B) :
    algebraMap (A ⊗[R] B) Q (a ⊗ₜ[R] b) = algebraMap A Q a * algebraMap B Q b := by
  have hab : a ⊗ₜ[R] b = algebraMap A (A ⊗[R] B) a * algebraMap B (A ⊗[R] B) b := by
    simp [Algebra.TensorProduct.right_algebraMap_apply]
  rw [hab, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

end RightAlgebra

end TauCeti
