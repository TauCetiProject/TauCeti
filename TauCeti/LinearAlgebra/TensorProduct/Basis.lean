/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor-product basis coordinates

This file records how contractions against one factor of a tensor product detect equality when
that factor is free. It also proves that the coordinates in bases obtained by scalar extension
commute with a map of the scalar-extension algebras.

## Main declarations

* `TensorProduct.tensor_eq_of_forall_tensorComponent_eq`: contractions against a projective right
  factor detect equality.
* `Module.Basis.map_baseChange_repr`: applying a scalar map to a coordinate in a base-changed
  basis agrees with first mapping the tensor and then taking its coordinate.
* `Module.Basis.map_toMatrixAlgEquiv_baseChange`: matrices in base-changed bases commute with
  scalar maps when the represented endomorphisms are intertwined by tensor-product base change.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace TensorProduct

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Equality of all contractions against the right factor detects equality in a tensor product
over a commutative semiring when the right factor is projective. -/
theorem tensor_eq_of_forall_tensorComponent_eq [Module.Projective R N] {x y : M ⊗[R] N}
    (h : ∀ φ : Module.Dual R N,
      tensorComponent (R := R) (M := M) φ x = tensorComponent (R := R) (M := M) φ y) :
    x = y := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R N)
  let b := Finsupp.basisSingleOne (R := R) (ι := N)
  have hmap : TensorProduct.map LinearMap.id s x = TensorProduct.map LinearMap.id s y := by
    apply (TensorProduct.equivFinsuppOfBasisRight b (M := M)).injective
    ext i
    rw [TensorProduct.equivFinsuppOfBasisRight_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply]
    calc
      TensorProduct.rid R M
          ((b.coord i).lTensor M (TensorProduct.map LinearMap.id s x)) =
          tensorComponent (b.coord i) (TensorProduct.map LinearMap.id s x) := by
            simp [tensorComponent]
      _ = LinearMap.id (tensorComponent ((b.coord i).comp s) x) :=
        tensorComponent_map (b.coord i) LinearMap.id s x
      _ = LinearMap.id (tensorComponent ((b.coord i).comp s) y) := by
        rw [h ((b.coord i).comp s)]
      _ = tensorComponent (b.coord i) (TensorProduct.map LinearMap.id s y) :=
        (tensorComponent_map (b.coord i) LinearMap.id s y).symm
      _ = TensorProduct.rid R M
          ((b.coord i).lTensor M (TensorProduct.map LinearMap.id s y)) := by
            simp [tensorComponent]
  let p : (N →₀ R) →ₗ[R] N := Finsupp.linearCombination R id
  have hleft (z : M ⊗[R] N) :
      TensorProduct.map LinearMap.id p (TensorProduct.map LinearMap.id s z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m n =>
        simp only [TensorProduct.map_tmul, LinearMap.id_apply]
        rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
  calc
    x = TensorProduct.map LinearMap.id p (TensorProduct.map LinearMap.id s x) := (hleft x).symm
    _ = TensorProduct.map LinearMap.id p (TensorProduct.map LinearMap.id s y) := congrArg _ hmap
    _ = y := hleft y

end TensorProduct

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
