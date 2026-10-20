/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Tensoring a product of scalars

The tensor product of a pair of copies of a commutative semiring with a module is
equivalent to a pair of copies of that module.
-/

public section

open TensorProduct

namespace TauCeti.TensorProduct

variable {R : Type*} {M : Type*}
  [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Tensoring a pair of scalars with `M` produces a pair of elements of `M`. -/
noncomputable def prodScalarLeftEquiv : (R × R) ⊗[R] M ≃ₗ[R] (M × M) :=
  _root_.TensorProduct.prodLeft R R R R M ≪≫ₗ
    (_root_.TensorProduct.lid R M).prodCongr (_root_.TensorProduct.lid R M)

@[simp]
theorem prodScalarLeftEquiv_tmul (a b : R) (m : M) :
    prodScalarLeftEquiv ((a, b) ⊗ₜ[R] m) = (a • m, b • m) := by
  simp only [prodScalarLeftEquiv, LinearEquiv.trans_apply,
    _root_.TensorProduct.prodLeft_tmul, LinearEquiv.prodCongr_apply,
    _root_.TensorProduct.lid_tmul]

@[simp]
theorem prodScalarLeftEquiv_symm_apply (m n : M) :
    prodScalarLeftEquiv.symm (m, n) =
      (1, 0) ⊗ₜ[R] m + (0, 1) ⊗ₜ[R] n := by
  apply (prodScalarLeftEquiv (R := R) (M := M)).injective
  simp only [LinearEquiv.apply_symm_apply, map_add, prodScalarLeftEquiv_tmul,
    one_smul, zero_smul, Prod.mk_add_mk, zero_add, add_zero]

end TauCeti.TensorProduct
