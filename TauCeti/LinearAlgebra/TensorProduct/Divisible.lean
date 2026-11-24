/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Divisibility in tensor products

Let `R` be a commutative ring and `r : R`. Call an `R`-module `M` *`r`-divisible* if
multiplication by `r` is surjective on `M`. This file proves:

* if `M` is `r`-divisible, so are `M ⊗[R] N` and `N ⊗[R] M`;
* if `M` and `N` are both `r`-divisible, multiplication by `r` on `M ⊗[R] N` is also injective.
  Neither `M` nor `N` needs to be `r`-torsion free: the `r`-torsion `M[r]` of `M` is killed by
  tensoring with the `r`-divisible module `N`, and right exactness of `⊗[R] N` applied to
  `0 → M[r] → M → M → 0` shows that multiplication by `r` on `M ⊗[R] N` has kernel the image
  of `M[r] ⊗[R] N`.

For `R = ℤ` these are the statements on uniquely `p`-divisible abelian groups behind the unique
divisibility of Milnor K-groups of algebraically closed fields in degrees at least two: the
degree-`n` tensor power of the multiplicative group is uniquely divisible for `n ≥ 2`. Passing to
the quotient by a divisible group of relations is `IsSMulRegular.quotient_of_le_smul` in
`TauCeti.RingTheory.Regular.IsSMulRegular`.

## Main results

* `TensorProduct.surjective_smul_of_surjective_left`,
  `TensorProduct.surjective_smul_of_surjective_right`: a tensor product with an `r`-divisible
  factor is `r`-divisible.
* `TensorProduct.isSMulRegular_of_surjective_smul`: multiplication by `r` is injective on the
  tensor product of two `r`-divisible modules.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Proposition 6.4.1 and Exercise 7.3.
-/

public section

open scoped TensorProduct

variable {R M N : Type*} {r : R}

namespace TensorProduct

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Tensoring on the right with any module preserves `r`-divisibility. -/
theorem surjective_smul_of_surjective_left (hM : Function.Surjective fun m : M ↦ r • m) :
    Function.Surjective fun x : M ⊗[R] N ↦ r • x := by
  -- Multiplication by `r` as a linear map, on `M` and on `M ⊗[R] N`.
  have hf : ⇑(DistribSMul.toLinearMap R M r) = fun m ↦ r • m :=
    funext (DistribSMul.toLinearMap_apply R M r)
  have hg : ⇑(DistribSMul.toLinearMap R (M ⊗[R] N) r) = fun x ↦ r • x :=
    funext (DistribSMul.toLinearMap_apply R _ r)
  rw [← hf] at hM
  rw [← hg, ← LinearMap.rTensor_smul_action]
  exact LinearMap.rTensor_surjective N hM

/-- Tensoring on the left with any module preserves `r`-divisibility. -/
theorem surjective_smul_of_surjective_right (hN : Function.Surjective fun n : N ↦ r • n) :
    Function.Surjective fun x : M ⊗[R] N ↦ r • x := by
  -- Multiplication by `r` as a linear map, on `N` and on `M ⊗[R] N`.
  have hf : ⇑(DistribSMul.toLinearMap R N r) = fun n ↦ r • n :=
    funext (DistribSMul.toLinearMap_apply R N r)
  have hg : ⇑(DistribSMul.toLinearMap R (M ⊗[R] N) r) = fun x ↦ r • x :=
    funext (DistribSMul.toLinearMap_apply R _ r)
  rw [← hf] at hN
  rw [← hg, ← LinearMap.lTensor_smul_action]
  exact LinearMap.lTensor_surjective M hN

end Semiring

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- If multiplication by `r` is surjective on both `M` and `N`, it is injective on `M ⊗[R] N`.
No torsion-freeness of `M` or `N` is needed. -/
theorem isSMulRegular_of_surjective_smul (hM : Function.Surjective fun m : M ↦ r • m)
    (hN : Function.Surjective fun n : N ↦ r • n) : IsSMulRegular (M ⊗[R] N) r := by
  -- Multiplication by `r` as a linear map, on `M` and on `M ⊗[R] N`.
  set f := DistribSMul.toLinearMap R M r
  have hf : ⇑f = fun m ↦ r • m := funext (DistribSMul.toLinearMap_apply R M r)
  have hg : ⇑(DistribSMul.toLinearMap R (M ⊗[R] N) r) = fun x ↦ r • x :=
    funext (DistribSMul.toLinearMap_apply R _ r)
  rw [← hf] at hM
  -- Right exactness of `⊗[R] N` on `M[r] → M → M → 0`.
  have hexact := rTensor_exact N (LinearMap.exact_subtype_ker_map f) hM
  rw [LinearMap.rTensor_smul_action, hg] at hexact
  -- The `r`-torsion of `M` dies after tensoring with the `r`-divisible module `N`.
  have hzero : (LinearMap.ker f).subtype.rTensor N = 0 := by
    ext k n
    obtain ⟨n, rfl⟩ := hN n
    have hk : r • (k : M) = 0 := by
      rw [← DistribSMul.toLinearMap_apply R M r]
      exact LinearMap.mem_ker.1 k.property
    simp [smul_tmul', hk]
  refine isSMulRegular_iff_right_eq_zero_of_smul.2 fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := (hexact x).1 hx
  simp [hzero]

end TensorProduct
