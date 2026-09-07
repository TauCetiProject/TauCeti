/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor-product basis coordinates

This file records how contractions against one factor of a tensor product detect equality when
that factor is free. It also proves that the coordinates in bases obtained by scalar extension
commute with a map of the scalar-extension algebras.

## Main declarations

* `TauCeti.Comodule.tensorComponent`: contraction against the right factor of a tensor product.
* `TauCeti.Comodule.tensor_eq_of_forall_tensorComponent_eq`: contractions against a free right
  factor detect equality.
* `Module.Basis.map_baseChange_repr`: applying a scalar map to a coordinate in a base-changed
  basis agrees with first mapping the tensor and then taking its coordinate.
* `Module.Basis.map_toMatrixAlgEquiv_baseChange`: matrices in base-changed bases commute with
  scalar maps when the represented endomorphisms are intertwined by tensor-product base change.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Apply a linear functional to the right factor of a tensor. -/
noncomputable def tensorComponent (phi : N →ₗ[R] R) : M ⊗[R] N →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap ∘ₗ phi.lTensor M

/-- A right tensor component sends a pure tensor to the corresponding scalar multiple. -/
@[simp]
theorem tensorComponent_tmul (phi : N →ₗ[R] R) (m : M) (n : N) :
    tensorComponent (R := R) (M := M) phi (m ⊗ₜ[R] n) = phi n • m := by
  simp [tensorComponent]

/-- The coordinates of a tensor in a basis of its right factor are its tensor components. -/
theorem equivFinsuppOfBasisRight_apply {ι : Type*} [DecidableEq ι]
    (b : Module.Basis ι R N) (t : M ⊗[R] N) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b t i =
      tensorComponent (R := R) (M := M) (b.coord i) t := by
  rw [TensorProduct.equivFinsuppOfBasisRight_apply]
  rfl

/-- Equality of all contractions against the right factor detects equality in a tensor product
over a commutative semiring when the right factor is free. -/
theorem tensor_eq_of_forall_tensorComponent_eq [Module.Free R N] {x y : M ⊗[R] N}
    (h : ∀ φ : Module.Dual R N,
      tensorComponent (R := R) (M := M) φ x = tensorComponent (R := R) (M := M) φ y) :
    x = y := by
  classical
  let b := Module.Free.chooseBasis R N
  apply (TensorProduct.equivFinsuppOfBasisRight b (M := M)).injective
  ext i
  rw [equivFinsuppOfBasisRight_apply, equivFinsuppOfBasisRight_apply]
  exact h (b.coord i)

/-- Contraction by the zero functional is the zero linear map. -/
@[simp]
theorem tensorComponent_zero :
    tensorComponent (R := R) (M := M) (0 : N →ₗ[R] R) = 0 := by
  refine TensorProduct.ext' fun m n => ?_
  simp

end TauCeti.Comodule

namespace Module.Basis

universe u v w x

variable {R : Type u} [CommSemiring R]
variable {M : Type x} [AddCommMonoid M] [Module R M]
variable {ι : Type*}

section Repr

variable {S : Type v} [Semiring S] [Algebra R S]
variable {T : Type w} [Semiring T] [Algebra R T]

/-- Coordinates in a base-changed basis are natural in the scalar-extension algebra. -/
@[simp] theorem map_baseChange_repr (b : Basis ι R M) (φ : S →ₗ[R] T)
    (z : S ⊗[R] M) (i : ι) :
    φ ((b.baseChange S).repr z i) =
      (b.baseChange T).repr
        (TensorProduct.map φ LinearMap.id z) i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul s m => simp

end Repr

section Matrix

variable {S : Type v} [CommSemiring S] [Algebra R S]
variable {T : Type w} [CommSemiring T] [Algebra R T]
variable [Fintype ι] [DecidableEq ι]

/-- Matrices in base-changed bases commute with a scalar map when the corresponding
endomorphisms are intertwined by tensor-product base change. -/
theorem map_toMatrixAlgEquiv_baseChange (b : Basis ι R M) (φ : S →ₐ[R] T)
    (f : S ⊗[R] M →ₗ[S] S ⊗[R] M) (g : T ⊗[R] M →ₗ[T] T ⊗[R] M)
    (h : ∀ z, TensorProduct.map φ.toLinearMap LinearMap.id (f z) =
      g (TensorProduct.map φ.toLinearMap LinearMap.id z)) :
    (LinearMap.toMatrixAlgEquiv (b.baseChange S) f).map φ =
      LinearMap.toMatrixAlgEquiv (b.baseChange T) g := by
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrixAlgEquiv_apply,
    LinearMap.toMatrixAlgEquiv_apply, ← AlgHom.toLinearMap_apply,
    map_baseChange_repr b φ.toLinearMap]
  apply congrArg (fun z => (b.baseChange T).repr z i)
  rw [h]
  simp only [baseChange_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
    LinearMap.id_apply, map_one]

end Matrix

end Module.Basis
