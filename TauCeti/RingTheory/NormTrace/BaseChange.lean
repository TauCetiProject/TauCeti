/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Norm and trace under scalar extension

This file records the compatibility of algebra norms and traces with scalar extension.
The multiplication-matrix identity holds over semirings; the norm identities also allow
noncommutative algebras.

## Main results

* `TauCeti.Algebra.norm_baseChange_tmul`, `TauCeti.Algebra.trace_baseChange_tmul`: the norm and
  trace of `1 ⊗ x ∈ A ⊗[K] B` over `A` are the images of those of `x`.
* `TauCeti.Algebra.leftMulMatrix_rTensor`, `TauCeti.Algebra.norm_rTensor`: for a free `K`-algebra
  `B` of finite rank, the matrix of multiplication and the norm of `P ⊗[K] B` over `P` are
  compatible with every `K`-algebra map `φ : P →ₐ[K] T`. Taking `P` to be a polynomial ring and `φ`
  an evaluation map, the norm on every base change `T ⊗[K] B` is a specialization of the generic
  norm form.
* `TauCeti.Algebra.norm_sum_X_tmul_tensorProductBasis`: the generic norm form of `T ⊗[K] B` over
  `T` is the image of that of `B` over `K`.
* `TauCeti.Algebra.charpoly_lmul_eq_norm`: the characteristic polynomial of multiplication by
  `x ∈ T ⊗[K] B` over `T` is the norm of `X - x` over `T[X]`.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u

section Semiring

variable {K : Type u} [CommSemiring K] {B : Type*} [Semiring B] [Algebra K B]

section LeftMulMatrix

variable {P T : Type*} [CommSemiring P] [Algebra K P] [CommSemiring T] [Algebra K T]

/-- The matrix of multiplication on `P ⊗[K] B`, in the basis induced by a basis of `B`, maps
entrywise along a `K`-algebra map `φ : P →ₐ[K] T` to that of the corresponding element of
`T ⊗[K] B`. -/
theorem Algebra.leftMulMatrix_rTensor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K B) (φ : P →ₐ[K] T) (x : P ⊗[K] B) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis T b)
        (Algebra.TensorProduct.rTensor B φ x) =
      φ.mapMatrix (Algebra.leftMulMatrix (Algebra.TensorProduct.basis P b) x) := by
  have key (y : P ⊗[K] B) (i : ι) : (Algebra.TensorProduct.basis T b).repr
      (Algebra.TensorProduct.rTensor B φ y) i = φ ((Algebra.TensorProduct.basis P b).repr y i) := by
    induction y using TensorProduct.inductionOn with
    | tmul p m => simp
    | add y z hy hz => simp [hy, hz]
  ext i j
  simp [Algebra.leftMulMatrix_eq_repr_mul, ← key]

end LeftMulMatrix

variable [Module.Free K B] [Module.Finite K B]
variable {P T : Type*} [CommRing P] [Algebra K P] [CommRing T] [Algebra K T]

/-- The norm of `P ⊗[K] B` over `P` commutes with base change along a `K`-algebra map
`φ : P →ₐ[K] T`. -/
theorem Algebra.norm_rTensor (φ : P →ₐ[K] T) (x : P ⊗[K] B) :
    Algebra.norm T (Algebra.TensorProduct.rTensor B φ x) = φ (Algebra.norm P x) := by
  classical
  let b := Module.Free.chooseBasis K B
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis T b),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis P b),
    Algebra.leftMulMatrix_rTensor]
  exact (φ.toRingHom.map_det _).symm

/-- The characteristic polynomial of multiplication by `x ∈ T ⊗[K] B` over `T` is the norm of
`X - x` over `T[X]`. -/
theorem Algebra.charpoly_lmul_eq_norm (x : T ⊗[K] B) :
    (Algebra.lmul T (T ⊗[K] B) x).charpoly =
      Algebra.norm (Polynomial T) (algebraMap (Polynomial T) _ Polynomial.X -
        Algebra.TensorProduct.rTensor B (IsScalarTower.toAlgHom K T (Polynomial T)) x) := by
  classical
  -- In the bases induced by a basis of `B`, both sides are the determinant of `X • 1 - M`, where
  -- `M` is the matrix of multiplication by `x` over `T`.
  let b := Module.Free.chooseBasis K B
  rw [← LinearMap.charpoly_toMatrix _ (Algebra.TensorProduct.basis T b),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis (Polynomial T) b), map_sub,
    AlgHom.commutes, Algebra.leftMulMatrix_rTensor, ← Algebra.leftMulMatrix_apply, Matrix.charpoly]
  refine congrArg Matrix.det (Matrix.ext fun i j ↦ ?_)
  by_cases h : i = j
  · simp [h, Matrix.charmatrix_apply_eq, Matrix.algebraMap_matrix_apply, Polynomial.algebraMap_eq]
  · simp [h, Matrix.charmatrix_apply_ne, Matrix.algebraMap_matrix_apply, Polynomial.algebraMap_eq]

end Semiring

variable {K : Type u} [CommRing K]
variable {A B : Type*} [CommRing A] [Algebra K A]

section Norm

variable [Ring B] [Algebra K B]
variable [Module.Free K B] [Module.Finite K B]

/-- Norm commutes with scalar extension on a pure tensor. -/
@[simp]
theorem Algebra.norm_baseChange_tmul (x : B) :
    Algebra.norm A ((1 : A) ⊗ₜ[K] x) = algebraMap K A (Algebra.norm K x) := by
  simp only [Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

end Norm

section GenericNorm

variable [Ring B] [Algebra K B]
variable {T : Type*} [CommRing T] [Algebra K T]

/-- The generic norm form of `T ⊗[K] B` over `T`, the norm of `∑ j, Xⱼ ⊗ bⱼ` for the basis of
`T ⊗[K] B` induced by a basis `b` of `B`, is the image under `K → T` of the generic norm form of `B`
in the basis `b`. -/
theorem Algebra.norm_sum_X_tmul_tensorProductBasis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K B) :
    Algebra.norm (MvPolynomial ι T)
        (∑ j, (MvPolynomial.X j : MvPolynomial ι T) ⊗ₜ[T] Algebra.TensorProduct.basis T b j) =
      MvPolynomial.map (algebraMap K T) (Algebra.norm (MvPolynomial ι K)
        (∑ j, (MvPolynomial.X j : MvPolynomial ι K) ⊗ₜ[K] b j)) := by
  let := Module.Free.of_basis b
  let := Module.Finite.of_basis b
  -- Reassociate and remove the middle copy of `T`, allowing `B` to be noncommutative.
  let e := (Algebra.TensorProduct.assoc K T (MvPolynomial ι T) (MvPolynomial ι T) T B).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid T (MvPolynomial ι T)
      (MvPolynomial ι T)) (.refl : B ≃ₐ[K] B))
  refine Eq.trans ?_ (Algebra.norm_rTensor (MvPolynomial.mapAlgHom (Algebra.ofId K T)) _)
  rw [← Algebra.norm_eq_of_algEquiv e]
  simp [e]

end GenericNorm

section Trace

variable [CommRing B] [Algebra K B]
variable [Module.Free K B] [Module.Finite K B]

/-- Trace commutes with scalar extension on a pure tensor. -/
@[simp]
theorem Algebra.trace_baseChange_tmul (x : B) :
    Algebra.trace A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x) =
      algebraMap K A (Algebra.trace K B x) := by
  simp only [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

end Trace

end TauCeti
