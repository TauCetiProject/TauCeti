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
import TauCeti.RingTheory.TensorProduct.Finite

/-!
# Norm and trace under scalar extension

This file records the compatibility of algebra norms and traces with scalar extension.
The multiplication-matrix identity holds over semirings; the norm identities also allow
noncommutative algebras.

## Main results

* `TauCeti.Algebra.norm_baseChange_tmul`, `TauCeti.Algebra.trace_baseChange_tmul`: the norm and
  trace of `1 ⊗ x ∈ A ⊗[K] B` over `A` are the images of those of `x`.
* `TauCeti.Algebra.trace_tmul_mul_smul`, `TauCeti.Algebra.sum_trace_mul_smul_baseChange_eq`:
  trace-dual expansions `x = ∑ᵢ Tr_{B/K}(x bᵢ) • yᵢ` extend linearly to `A ⊗[K] B`.
* `TauCeti.Algebra.leftMulMatrix_rTensor`, `TauCeti.Algebra.norm_rTensor`: the matrix of
  multiplication on `P ⊗[K] B` (for a finite `K`-basis of `B`) and the norm of `P ⊗[K] B` over `P`
  (for a free `K`-algebra `B`, finite or not) are compatible with every `K`-algebra map
  `φ : P →ₐ[K] T`. When `B` has a finite `K`-basis, taking `P` to be a polynomial ring and `φ` an
  evaluation map shows that the norm on every base change `T ⊗[K] B` is a specialization of the
  generic norm form.
* `TauCeti.Algebra.norm_sum_X_tmul_tensorProductBasis`: the generic norm form of `T ⊗[K] B` over
  `T` is the image of that of `B` over `K`.
* `Module.Basis.norm_sum_tmul_eq_aeval`: the norm of `∑ j, xⱼ ⊗ bⱼ` over `T` is the generic norm
  form of `B` evaluated at `x`.
* `TauCeti.Algebra.charpoly_lmul_eq_norm`: for a finite free `K`-algebra `B`, the characteristic
  polynomial of multiplication by `x ∈ T ⊗[K] B` over `T` is the norm of `X - x` over `T[X]`.
* `TauCeti.Algebra.trace_baseChange_tmul_of_isScalarTower`: for a tower `R → S → T` and an
  `R`-algebra `C` with `S ⊗[R] C` free over `S`, the trace of `1 ⊗ c` in `T ⊗[R] C` is the
  image of its trace in `S ⊗[R] C`.
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

variable [Module.Free K B]
variable {P T : Type*} [CommRing P] [Algebra K P] [CommRing T] [Algebra K T]

/-- The norm of `P ⊗[K] B` over `P` commutes with base change along a `K`-algebra map
`φ : P →ₐ[K] T`. When `B` is not finite over `K` both norms are `1`. -/
theorem Algebra.norm_rTensor (φ : P →ₐ[K] T) (x : P ⊗[K] B) :
    Algebra.norm T (Algebra.TensorProduct.rTensor B φ x) = φ (Algebra.norm P x) := by
  classical
  by_cases hfin : Module.Finite K B
  · let b := Module.Free.chooseBasis K B
    rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis T b),
      Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis P b),
      Algebra.leftMulMatrix_rTensor]
    exact (φ.toRingHom.map_det _).symm
  · nontriviality T
    have : Nontrivial P := φ.toRingHom.domain_nontrivial
    rw [Algebra.norm_eq_one_of_not_module_finite (mt Module.Finite.of_baseChange hfin),
      Algebra.norm_eq_one_of_not_module_finite (mt Module.Finite.of_baseChange hfin), map_one]

variable [Module.Finite K B]

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
variable [Module.Free K B]

/-- Norm commutes with scalar extension on a pure tensor. When `B` is not finite over `K` both
norms are `1`. -/
@[simp]
theorem Algebra.norm_baseChange_tmul (x : B) :
    Algebra.norm A ((1 : A) ⊗ₜ[K] x) = algebraMap K A (Algebra.norm K x) := by
  simpa [← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.lid K B) ((1 : K) ⊗ₜ[K] x)] using
    Algebra.norm_rTensor (Algebra.ofId K A) ((1 : K) ⊗ₜ[K] x)

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
  -- Reassociate and remove the middle copy of `T`, allowing `B` to be noncommutative.
  let e := (Algebra.TensorProduct.assoc K T (MvPolynomial ι T) (MvPolynomial ι T) T B).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid T (MvPolynomial ι T)
      (MvPolynomial ι T)) (.refl : B ≃ₐ[K] B))
  refine Eq.trans ?_ (Algebra.norm_rTensor (MvPolynomial.mapAlgHom (Algebra.ofId K T)) _)
  rw [← Algebra.norm_eq_of_algEquiv e]
  simp [e]

/-- The norm of `∑ j, xⱼ ⊗ bⱼ` in `T ⊗[K] B` over `T` is the generic norm form of `B` in the basis
`b`, evaluated at `x`. -/
theorem _root_.Module.Basis.norm_sum_tmul_eq_aeval {ι : Type*} [Fintype ι] (b : Module.Basis ι K B)
    (x : ι → T) :
    Algebra.norm T (∑ j, x j ⊗ₜ[K] b j) = MvPolynomial.aeval x
      (Algebra.norm (MvPolynomial ι K) (∑ j, (MvPolynomial.X j : MvPolynomial ι K) ⊗ₜ[K] b j)) := by
  let := Module.Free.of_basis b
  rw [← Algebra.norm_rTensor]
  simp

end GenericNorm

section Trace

variable [CommRing B] [Algebra K B]
variable [Module.Free K B]

/-- Trace commutes with scalar extension on a pure tensor. When `B` is not finite over `K` both
traces are `0`. -/
@[simp]
theorem Algebra.trace_baseChange_tmul (x : B) :
    Algebra.trace A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x) =
      algebraMap K A (Algebra.trace K B x) := by
  by_cases hfin : Module.Finite K B
  · simp only [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  · nontriviality A
    have hfin' : ¬ Module.Finite A (A ⊗[K] B) := mt Module.Finite.of_baseChange hfin
    rw [Algebra.trace_eq_zero_of_not_exists_basis K fun ⟨_, ⟨b⟩⟩ ↦ hfin (.of_basis b),
      Algebra.trace_eq_zero_of_not_exists_basis A fun ⟨_, ⟨b⟩⟩ ↦ hfin' (.of_basis b)]
    simp

/-- The trace pairing and scalar multiplication commute with scalar extension on pure tensors. -/
theorem Algebra.trace_tmul_mul_smul (a : A) (x b y : B) :
    Algebra.trace A (A ⊗[K] B) ((a ⊗ₜ[K] x) * (1 ⊗ₜ[K] b)) • ((1 : A) ⊗ₜ[K] y) =
      a ⊗ₜ[K] (Algebra.trace K B (x * b) • y) := by
  have ha : a ⊗ₜ[K] (x * b) = a • ((1 : A) ⊗ₜ[K] (x * b)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, map_smul, Algebra.trace_baseChange_tmul]
  simp only [smul_eq_mul, TensorProduct.smul_tmul', mul_one, mul_comm a, ← Algebra.smul_def,
    TensorProduct.smul_tmul]

/-- Trace-dual expansions extend linearly to any base change `A ⊗[K] B`: if
`x = ∑ᵢ Tr_{B/K}(x * bᵢ) • yᵢ` for all `x ∈ B`, then `ξ = ∑ᵢ Tr(ξ * (1 ⊗ bᵢ)) • (1 ⊗ yᵢ)` for
all `ξ ∈ A ⊗[K] B`. -/
theorem Algebra.sum_trace_mul_smul_baseChange_eq {ι : Type*} [Fintype ι] (b y : ι → B)
    (h : ∀ x : B, ∑ i, Algebra.trace K B (x * b i) • y i = x) (ξ : A ⊗[K] B) :
    ∑ i, Algebra.trace A (A ⊗[K] B) (ξ * (1 ⊗ₜ[K] b i)) • ((1 : A) ⊗ₜ[K] y i) = ξ := by
  induction ξ using TensorProduct.inductionOn with
  | add ξ η hξ hη =>
    conv_rhs => rw [← hξ, ← hη]
    simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib]
  | tmul a x =>
    conv_rhs => rw [← h x, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Algebra.trace_tmul_mul_smul a x (b i) (y i)

end Trace

section TraceTower

variable {R S T C : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing C] [Algebra R S]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra R C]
  [Module.Free S (S ⊗[R] C)]

/-- Let `R → S → T` be a tower of rings and `C` an `R`-algebra with `S ⊗[R] C` free over
`S`. The trace of `1 ⊗ c` in `T ⊗[R] C` over `T` is the image of the trace of `1 ⊗ c` in
`S ⊗[R] C` over `S`. -/
theorem Algebra.trace_baseChange_tmul_of_isScalarTower (c : C) :
    Algebra.trace T (T ⊗[R] C) (1 ⊗ₜ c) =
      algebraMap S T (Algebra.trace S (S ⊗[R] C) (1 ⊗ₜ c)) := by
  rw [← Algebra.trace_baseChange_tmul (A := T),
    ← Algebra.trace_eq_of_algEquiv (Algebra.TensorProduct.cancelBaseChange R S T T C)]
  simp

end TraceTower

end TauCeti
