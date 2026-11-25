/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight

/-!
# Weight spaces of tensor products

Let `π : C → R[X]` be a bialgebra morphism, so that corestriction along `π` restricts a
representation of the group with coordinate bialgebra `C` to the diagonalizable group `D(X)`. This
file shows that the weight spaces of `TauCeti.DiagonalizableGroup.weightSpace` are compatible with
tensor products: weights add on tensor products.

## Main results

* `TauCeti.DiagonalizableGroup.tmul_mem_weightSpace_tensor`: the tensor product of an `x`-weight
  vector and a `y`-weight vector is an `x * y`-weight vector of the tensor-product comodule.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed. (2003), Part I, §2.11.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.DiagonalizableGroup

variable {R : Type*} [CommSemiring R] {X : Type*}
variable {C : Type*} [Semiring C]
variable {V : Type*} [AddCommMonoid V] [Module R V]

section Tensor

variable [Bialgebra R C] [Monoid X] [Comodule R C V]
variable {W : Type*} [AddCommMonoid W] [Module R W] [Comodule R C W]

attribute [local instance] Comodule.tensor

/-- **Weights add on tensor products.** For a bialgebra morphism `π : C → R[X]`, the tensor
product of an `x`-weight vector `v` and a `y`-weight vector `w` is an `x * y`-weight vector of the
diagonal tensor-product comodule. -/
theorem tmul_mem_weightSpace_tensor (π : C →ₐc[R] MonoidAlgebra R X) {x y : X} {v : V} {w : W}
    (hv : v ∈ weightSpace V (π : C →ₗc[R] MonoidAlgebra R X) x)
    (hw : w ∈ weightSpace W (π : C →ₗc[R] MonoidAlgebra R X) y) :
    v ⊗ₜ[R] w ∈ weightSpace (V ⊗[R] W) (π : C →ₗc[R] MonoidAlgebra R X) (x * y) := by
  rw [mem_weightSpace] at hv hw ⊢
  rw [← LinearMap.lTensor_def] at hv hw ⊢
  have h := LinearMap.congr_fun (Comodule.lTensor_comp_tensorCombine (R := R) (C := C)
    (M := V) (N := W) (π : C →ₐ[R] MonoidAlgebra R X))
    (Comodule.coact (R := R) (C := C) (M := V) v ⊗ₜ[R] Comodule.coact (R := R) (C := C) (M := W) w)
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul] at h
  rw [Comodule.tensor_coact, Comodule.tensorCoact_tmul]
  -- `lTensor_comp_tensorCombine` takes `π` as an algebra map, while `weightSpace` uses `π` as a
  -- coalgebra map; both underlying linear maps are `π` itself
  have hπ : (π : C →ₐ[R] MonoidAlgebra R X).toLinearMap =
      (π : C →ₗc[R] MonoidAlgebra R X).toLinearMap := rfl
  rw [hπ] at h
  rw [h, hv, hw, Comodule.tensorCombine_tmul_tmul, MonoidAlgebra.single_mul_single, one_mul]

end Tensor

end TauCeti.DiagonalizableGroup
