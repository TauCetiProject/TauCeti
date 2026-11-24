/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation

/-!
# Weight spaces of tensor products and duals

Let `π : C → R[X]` be a bialgebra morphism, so that corestriction along `π` restricts a
representation of the group with coordinate bialgebra `C` to the diagonalizable group `D(X)`. This
file shows that the weight spaces of `TauCeti.DiagonalizableGroup.weightSpace` are compatible with
tensor products and duals: weights add on tensor products, and a functional of weight `x` pairs
trivially with every vector of weight `y` unless `x * y = 1`.

## Main results

* `TauCeti.DiagonalizableGroup.tmul_mem_weightSpace_tensor`: the tensor product of an `x`-weight
  vector and a `y`-weight vector is an `x * y`-weight vector of the tensor-product comodule.
* `TauCeti.DiagonalizableGroup.apply_eq_zero_of_mem_weightSpace_dual`: on a finite projective
  comodule over a Hopf algebra, a functional of weight `x` for the dual coaction vanishes on every
  vector of weight `y` with `x * y ≠ 1`.

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

section Dual

variable [CommMonoid X] [HopfAlgebra R C] [Comodule R C V] [Module.Finite R V]
  [Module.Projective R V]

attribute [local instance] Comodule.dual

/-- **Weights negate in the dual.** For a bialgebra morphism `π : C → R[X]` out of a Hopf
algebra, a functional `φ` of weight `x` for the dual coaction on a finite projective comodule `V`
vanishes on every vector `v` of weight `y` with `x * y ≠ 1`. -/
theorem apply_eq_zero_of_mem_weightSpace_dual (π : C →ₐc[R] MonoidAlgebra R X) {x y : X}
    {φ : Module.Dual R V} {v : V}
    (hφ : φ ∈ weightSpace (Module.Dual R V) (π : C →ₗc[R] MonoidAlgebra R X) x)
    (hv : v ∈ weightSpace V (π : C →ₗc[R] MonoidAlgebra R X) y) (hxy : x * y ≠ 1) :
    φ v = 0 := by
  have h := TauCeti.Comodule.baseChangeEvaluation_dual_endOfPoint_invariant (R := R) (H := C)
    (M := V) (A := MonoidAlgebra R X) (toConv (π : C →ₐ[R] MonoidAlgebra R X))
    (1 ⊗ₜ[R] φ) (1 ⊗ₜ[R] v)
  rw [ofConv_toConv, ← AlgHom.id_comp (π : C →ₐ[R] MonoidAlgebra R X)] at h
  rw [endOfPoint_tmul_of_mem_weightSpace _ π (AlgHom.id R (MonoidAlgebra R X)) 1 hφ,
    endOfPoint_tmul_of_mem_weightSpace _ π (AlgHom.id R (MonoidAlgebra R X)) 1 hv] at h
  simp only [TauCeti.Module.Dual.baseChangeEvaluation_tmul, AlgHom.coe_id, id_eq, one_mul,
    MonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    MonoidAlgebra.single_mul_single, mul_one] at h
  by_contra h₀
  exact hxy ((MonoidAlgebra.single_left_inj h₀).mp h)

end Dual

end TauCeti.DiagonalizableGroup
