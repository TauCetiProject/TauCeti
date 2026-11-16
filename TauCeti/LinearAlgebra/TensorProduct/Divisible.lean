/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Divisibility in tensor products and quotients

Let `R` be a commutative ring and `r : R`. Call an `R`-module `M` *`r`-divisible* if
multiplication by `r` is surjective on `M`. This file proves:

* if `M` is `r`-divisible, so are `M ⊗[R] N` and `N ⊗[R] M`;
* if `M` and `N` are both `r`-divisible, multiplication by `r` on `M ⊗[R] N` is also injective.
  Neither `M` nor `N` needs to be `r`-torsion free: the `r`-torsion `M[r]` of `M` is killed by
  tensoring with the `r`-divisible module `N`, and right exactness of `⊗[R] N` applied to
  `0 → M[r] → M → M → 0` shows that multiplication by `r` on `M ⊗[R] N` has kernel the image
  of `M[r] ⊗[R] N`;
* if multiplication by `r` is injective on `M` and a submodule `P` is `r`-divisible, then
  multiplication by `r` is injective on `M ⧸ P`.

For `R = ℤ` these are the statements on uniquely `p`-divisible abelian groups behind the unique
divisibility of Milnor K-groups of algebraically closed fields in degrees at least two: the
degree-`n` tensor power of the multiplicative group is uniquely divisible for `n ≥ 2`, and so is
its quotient by a divisible group of relations. The hypothesis on the relations cannot be
dropped: `ℤ ⊆ ℚ` is not `p`-divisible, and `ℚ ⧸ ℤ` has nonzero `p`-torsion.

## Main results

* `TensorProduct.surjective_smul_of_surjective_left`,
  `TensorProduct.surjective_smul_of_surjective_right`: a tensor product with an `r`-divisible
  factor is `r`-divisible.
* `TensorProduct.isSMulRegular_of_surjective_smul`: multiplication by `r` is injective on the
  tensor product of two `r`-divisible modules.
* `IsSMulRegular.quotient_of_le_smul`: multiplication by `r` stays injective on the quotient by
  an `r`-divisible submodule.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Proposition 6.4.1 and Exercise 7.3.
-/

public section

open scoped Pointwise TensorProduct

variable {R M N : Type*} {r : R}

namespace TensorProduct

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Tensoring on the right with any module preserves `r`-divisibility. -/
theorem surjective_smul_of_surjective_left (hM : Function.Surjective fun m : M ↦ r • m) :
    Function.Surjective fun x : M ⊗[R] N ↦ r • x := by
  have h := LinearMap.rTensor_surjective N (g := DistribSMul.toLinearMap R M r) hM
  rwa [LinearMap.rTensor_smul_action] at h

/-- Tensoring on the left with any module preserves `r`-divisibility. -/
theorem surjective_smul_of_surjective_right (hN : Function.Surjective fun n : N ↦ r • n) :
    Function.Surjective fun x : M ⊗[R] N ↦ r • x := by
  have h := LinearMap.lTensor_surjective M (g := DistribSMul.toLinearMap R N r) hN
  rwa [LinearMap.lTensor_smul_action] at h

end Semiring

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- If multiplication by `r` is surjective on both `M` and `N`, it is injective on `M ⊗[R] N`.
No torsion-freeness of `M` or `N` is needed. -/
theorem isSMulRegular_of_surjective_smul (hM : Function.Surjective fun m : M ↦ r • m)
    (hN : Function.Surjective fun n : N ↦ r • n) : IsSMulRegular (M ⊗[R] N) r := by
  set f := DistribSMul.toLinearMap R M r
  -- Right exactness of `⊗[R] N` on `M[r] → M → M → 0`.
  have hexact := rTensor_exact N (LinearMap.exact_subtype_ker_map f) hM
  rw [LinearMap.rTensor_smul_action] at hexact
  -- The `r`-torsion of `M` dies after tensoring with the `r`-divisible module `N`.
  have hzero : (LinearMap.ker f).subtype.rTensor N = 0 := by
    ext k n
    obtain ⟨n, rfl⟩ := hN n
    have hk : r • (k : M) = 0 := k.2
    simp [smul_tmul', hk]
  refine isSMulRegular_iff_right_eq_zero_of_smul.2 fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := (hexact x).1 hx
  simp [hzero]

end TensorProduct

/-- If multiplication by `r` is injective on `M` and the submodule `P` is `r`-divisible, that is
`P ≤ r • P`, then multiplication by `r` is injective on `M ⧸ P`. -/
theorem IsSMulRegular.quotient_of_le_smul [CommRing R] [AddCommGroup M] [Module R M]
    (h : IsSMulRegular M r) {P : Submodule R M} (hP : P ≤ r • P) : IsSMulRegular (M ⧸ P) r :=
  (h.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul P).2 (inf_le_right.trans hP)
