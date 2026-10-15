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

variable {K : Type u} [CommRing K]
variable {A B : Type*} [CommRing A] [Algebra K A]

section Norm

variable [Ring B] [Algebra K B]
variable [Module.Free K B] [Module.Finite K B]

/-- Norm commutes with scalar extension on a pure tensor. -/
@[simp]
theorem Algebra.norm_baseChange_tmul (x : B) :
    Algebra.norm A ((1 : A) ⊗ₜ[K] x) = algebraMap K A (Algebra.norm K x) := by
  rw [Algebra.norm_apply]
  calc
    LinearMap.det (Algebra.lmul A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x)) =
        LinearMap.det ((Algebra.lmul K B x).baseChange A) := by
          rw [Algebra.baseChange_lmul]
    _ = algebraMap K A (LinearMap.det (Algebra.lmul K B x)) :=
      LinearMap.det_baseChange (R := K) (M := B) (f := Algebra.lmul K B x) (A := A)
    _ = algebraMap K A (Algebra.norm K x) := by
      rw [Algebra.norm_apply]

variable {P T : Type*} [CommRing P] [Algebra K P] [CommRing T] [Algebra K T]

omit [Module.Free K B] [Module.Finite K B] in
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

/-- The norm of `P ⊗[K] B` over `P` commutes with base change along a `K`-algebra map
`φ : P →ₐ[K] T`. -/
theorem Algebra.norm_rTensor (φ : P →ₐ[K] T) (x : P ⊗[K] B) :
    Algebra.norm T (Algebra.TensorProduct.rTensor B φ x) = φ (Algebra.norm P x) := by
  classical
  let b := Module.Free.chooseBasis K B
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis T b),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis P b), φ.map_det,
    Algebra.leftMulMatrix_rTensor]

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

end Norm

section GenericNorm

variable [CommRing B] [Algebra K B] [Module.Free K B] [Module.Finite K B]
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
  refine Eq.trans ?_ (Algebra.norm_rTensor (MvPolynomial.mapAlgHom (Algebra.ofId K T)) _)
  rw [← Algebra.norm_eq_of_algEquiv
    (Algebra.TensorProduct.cancelBaseChange K T (MvPolynomial ι T) (MvPolynomial ι T) B)]
  simp

end GenericNorm

section Trace

variable [CommRing B] [Algebra K B]
variable [Module.Free K B] [Module.Finite K B]

/-- Trace commutes with scalar extension on a pure tensor. -/
@[simp]
theorem Algebra.trace_baseChange_tmul (x : B) :
    Algebra.trace A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x) =
      algebraMap K A (Algebra.trace K B x) := by
  rw [Algebra.trace_apply]
  calc
    LinearMap.trace A (TensorProduct K A B)
        (Algebra.lmul A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x)) =
        LinearMap.trace A (TensorProduct K A B) ((Algebra.lmul K B x).baseChange A) := by
          rw [Algebra.baseChange_lmul]
    _ = algebraMap K A (LinearMap.trace K B (Algebra.lmul K B x)) :=
      LinearMap.trace_baseChange (R := K) (M := B) (f := Algebra.lmul K B x) (A := A)
    _ = algebraMap K A (Algebra.trace K B x) := by
      rw [Algebra.trace_apply]

end Trace

end TauCeti
