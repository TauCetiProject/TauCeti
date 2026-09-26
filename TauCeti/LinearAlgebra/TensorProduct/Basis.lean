/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor-product basis coordinates

This file records how contractions against one factor of a tensor product detect equality when
that factor is free. It also proves that the coordinates in bases obtained by scalar extension
commute with a map of the scalar-extension algebras, and that over a basis with at most one
index a scalar extension consists of pure tensors.

## Main declarations

* `TensorProduct.tensor_eq_of_forall_tensorComponent_eq`: contractions against a projective right
  factor detect equality.
* `Module.Basis.map_baseChange_repr`: applying a scalar map to a coordinate in a base-changed
  basis agrees with first mapping the tensor and then taking its coordinate.
* `Module.Basis.eq_baseChange_repr_tmul_of_subsingleton`: over a basis with at most one index,
  every element of a scalar extension is the pure tensor of its unique coordinate with the
  corresponding basis vector.
* `Module.Basis.baseChange_toMatrix_baseChange`: change-of-basis matrices between base-changed
  bases are obtained by mapping entries.
* `Module.Basis.map_toMatrixAlgEquiv_baseChange`: matrices in base-changed bases commute with
  scalar maps when the represented endomorphisms are intertwined by tensor-product base change.
* `Module.Basis.toMatrix_baseChange_baseChange`: matrices of scalar-extended endomorphisms
  are obtained by mapping entries.
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
      _root_.LinearMap.tensorComponent (R := R) (M := M) φ x =
        _root_.LinearMap.tensorComponent (R := R) (M := M) φ y) :
    x = y := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R N)
  let b := Finsupp.basisSingleOne (R := R) (ι := N)
  have hcomponent (φ : (N →₀ R) →ₗ[R] R) (t : M ⊗[R] (N →₀ R)) :
      TensorProduct.rid R M (φ.lTensor M t) =
        _root_.LinearMap.tensorComponent φ t := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m n => simp
  have hmap : TensorProduct.map LinearMap.id s x = TensorProduct.map LinearMap.id s y := by
    apply (TensorProduct.equivFinsuppOfBasisRight b (M := M)).injective
    ext i
    rw [TensorProduct.equivFinsuppOfBasisRight_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply]
    calc
      TensorProduct.rid R M
          ((b.coord i).lTensor M (TensorProduct.map LinearMap.id s x)) =
          _root_.LinearMap.tensorComponent (b.coord i)
            (TensorProduct.map LinearMap.id s x) := by
            exact hcomponent (b.coord i) _
      _ = LinearMap.id (_root_.LinearMap.tensorComponent ((b.coord i).comp s) x) :=
        _root_.LinearMap.tensorComponent_map (b.coord i) LinearMap.id s x
      _ = LinearMap.id (_root_.LinearMap.tensorComponent ((b.coord i).comp s) y) := by
        rw [h ((b.coord i).comp s)]
      _ = _root_.LinearMap.tensorComponent (b.coord i)
          (TensorProduct.map LinearMap.id s y) :=
        (_root_.LinearMap.tensorComponent_map (b.coord i) LinearMap.id s y).symm
      _ = TensorProduct.rid R M
          ((b.coord i).lTensor M (TensorProduct.map LinearMap.id s y)) := by
            exact (hcomponent (b.coord i) _).symm
  let p : (N →₀ R) →ₗ[R] N := Finsupp.linearCombination R id
  have hleft (z : M ⊗[R] N) :
      TensorProduct.map LinearMap.id p (TensorProduct.map LinearMap.id s z) = z := by
    induction z using TensorProduct.inductionOn with
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
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul s m => simp

/-- Over a basis with at most one index, every element of a scalar extension is the pure tensor
of its unique coordinate with the corresponding basis vector.  This isolates the tensor
bookkeeping needed to reduce statements about rank-at-most-one scalar extensions to scalar
multiples of a single vector. -/
theorem eq_baseChange_repr_tmul_of_subsingleton [Subsingleton ι] (b : Basis ι R M)
    (z : S ⊗[R] M) (i : ι) :
    z = (b.baseChange S).repr z i ⊗ₜ b i := by
  let _ : Fintype ι := Fintype.ofFinite ι
  conv_lhs => rw [← (b.baseChange S).sum_repr z]
  rw [Fintype.sum_subsingleton _ i, baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

end Repr

section Matrix

variable {S : Type v} [CommSemiring S] [Algebra R S]
variable {T : Type w} [CommSemiring T] [Algebra R T]

/-- The change-of-basis matrix between two base-changed bases is the entrywise scalar extension
of the change-of-basis matrix between the original bases. -/
@[simp] theorem baseChange_toMatrix_baseChange {ι' : Type*} (b : Basis ι R M)
    (b' : Basis ι' R M) :
    (b.baseChange S).toMatrix (b'.baseChange S) = (b.toMatrix b').map (algebraMap R S) := by
  ext i j
  simp [toMatrix_apply, baseChange_apply, Algebra.smul_def]

variable [Fintype ι] [DecidableEq ι]

/-- The matrix of a scalar-extended endomorphism is the entrywise scalar extension of its
matrix in the original basis. -/
theorem toMatrix_baseChange_baseChange (b : Basis ι R M) (f : M →ₗ[R] M) :
    LinearMap.toMatrix (b.baseChange S) (b.baseChange S) (f.baseChange S) =
      (LinearMap.toMatrix b b f).map (algebraMap R S) := by
  ext i j
  simp [LinearMap.toMatrix_apply, baseChange_apply, Algebra.smul_def]

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
