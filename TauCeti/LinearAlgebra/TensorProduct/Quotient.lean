/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Cokernels commute with tensor products, heterobasically

Tensoring is right exact: for a linear map `f : M' → M` and a module `N`, the cokernel of
`f ⊗ 𝟙 N` is `(M ⧸ range f) ⊗ N`. Mathlib proves this over a commutative ring, as the exactness
of the tensored pair (`rTensor_exact`) and as the isomorphism `LinearMap.rTensor.equiv`. When
`M'` and `M` are modules over an `R`-algebra `A` and `f` is `A`-linear, the comparison isomorphism
is `A`-linear for the module structure of `TensorProduct.AlgebraTensorModule` on the left factor,
and this file records that heterobasic form.

The heterobasic version is what identifies the base change of a module presented by generators
and relations over a noncommutative algebra `A` with the module presented by the base-changed
relations, for instance the rationalisation of a module over an integral group ring `ℤ_p[G]`.

## Main definitions

* `TensorProduct.AlgebraTensorModule.quotientRangeTensorEquiv`: the `A`-linear
  isomorphism `(M ⧸ range f) ⊗[R] N ≃ₗ[A] (M ⊗[R] N) ⧸ range (f ⊗ 𝟙 N)`.

## Main results

* `TensorProduct.AlgebraTensorModule.ker_rTensor_mkQ`: the kernel of the tensored
  quotient map `mkQ ⊗ 𝟙 N` is the range of `f ⊗ 𝟙 N`.
* `TensorProduct.AlgebraTensorModule.rTensor_mkQ_surjective`: the tensored quotient map
  is surjective.
-/

public section

namespace TensorProduct.AlgebraTensorModule

open LinearMap

variable {R A M M' N : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  [AddCommGroup N] [Module R N]

/-- Tensoring the exact pair `M' → M → M ⧸ range f` with `N` keeps it exact: the kernel of
`mkQ ⊗ 𝟙 N` is the range of `f ⊗ 𝟙 N`, as `A`-submodules of `M ⊗[R] N`. -/
theorem ker_rTensor_mkQ (f : M' →ₗ[A] M) :
    ker (AlgebraTensorModule.rTensor R N (range f).mkQ) =
      range (AlgebraTensorModule.rTensor R N f) := by
  have hexact : Function.Exact (f.restrictScalars R) ((range f).mkQ.restrictScalars R) := by
    rw [LinearMap.exact_iff, ker_restrictScalars, Submodule.ker_mkQ, range_restrictScalars]
  have hsurj : Function.Surjective ((range f).mkQ.restrictScalars R) :=
    Submodule.mkQ_surjective (range f)
  have h := (rTensor_exact N hexact hsurj).linearMap_ker_eq
  ext x
  rw [SetLike.ext_iff] at h
  simpa only [mem_ker, mem_range, AlgebraTensorModule.coe_rTensor] using h x

omit [Module A M'] [IsScalarTower R A M'] in
/-- The tensored quotient map `mkQ ⊗ 𝟙 N` is surjective. -/
theorem rTensor_mkQ_surjective (p : Submodule A M) :
    Function.Surjective (AlgebraTensorModule.rTensor R N p.mkQ) := by
  rw [AlgebraTensorModule.coe_rTensor]
  exact rTensor_surjective N (Submodule.mkQ_surjective p)

/-- **Cokernels commute with tensor products.** For an `A`-linear map `f : M' → M` and an
`R`-module `N`, the base change `(M ⧸ range f) ⊗[R] N` of the cokernel of `f` is the cokernel of
`f ⊗ 𝟙 N`, as left `A`-modules. -/
noncomputable def quotientRangeTensorEquiv (f : M' →ₗ[A] M) :
    ((M ⧸ range f) ⊗[R] N) ≃ₗ[A] (M ⊗[R] N) ⧸ range (AlgebraTensorModule.rTensor R N f) :=
  ((AlgebraTensorModule.rTensor R N (range f).mkQ).quotKerEquivOfSurjective
      (rTensor_mkQ_surjective (range f))).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_rTensor_mkQ f))

@[simp]
theorem quotientRangeTensorEquiv_mk_tmul (f : M' →ₗ[A] M) (x : M) (n : N) :
    quotientRangeTensorEquiv (N := N) f (Submodule.Quotient.mk x ⊗ₜ[R] n) =
      Submodule.Quotient.mk (x ⊗ₜ[R] n) := by
  rw [quotientRangeTensorEquiv, LinearEquiv.trans_apply, ← Submodule.mkQ_apply,
    ← AlgebraTensorModule.rTensor_tmul, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk]

@[simp]
theorem quotientRangeTensorEquiv_symm_mk_tmul (f : M' →ₗ[A] M) (x : M) (n : N) :
    (quotientRangeTensorEquiv (N := N) f).symm (Submodule.Quotient.mk (x ⊗ₜ[R] n)) =
      Submodule.Quotient.mk x ⊗ₜ[R] n :=
  (LinearEquiv.symm_apply_eq _).mpr (quotientRangeTensorEquiv_mk_tmul f x n).symm

end TensorProduct.AlgebraTensorModule
