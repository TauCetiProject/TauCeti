/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import TauCeti.RingTheory.TensorProduct.Finite
import TauCeti.RingTheory.TensorProduct.Free
import TauCeti.LinearAlgebra.Trace.RestrictScalars

/-!
# Norm and trace under scalar extension

This file records the compatibility of algebra norms and traces with scalar extension.
The multiplication-matrix identity holds over semirings; the norm identities also allow
noncommutative algebras.

## Main results

* `TauCeti.Algebra.norm_baseChange_tmul`, `TauCeti.Algebra.trace_baseChange_tmul`, and
  `TauCeti.Algebra.trace_tmul`: the norm and trace of pure tensors in `A ⊗[K] B` over `A` are
  computed from those in `B` over `K`.
* `TauCeti.Algebra.trace_tmul_mul_smul` and `TauCeti.Algebra.sum_trace_mul_smul_tmul_eq`:
  trace-pairing scalar multiplication and trace-dual expansions pass from `B / K` to the scalar
  extension `A ⊗[K] B / A`.
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
* `Module.Basis.norm_baseChange_equivFun_symm` gives the norm in scalar-extended basis
  coordinates as a determinant, and `Module.Basis.norm_baseChange_equivFun_symm_smul` gives its
  homogeneity. For the coordinates of the unit or of a product, `LinearEquiv.symm_apply_apply`
  reduces the norm computation to `map_one` or `map_mul` for `Algebra.norm`.
* `Module.Basis.one_le_abs_norm_baseChange_intCast` bounds the absolute norm of a nonzero
  integer coordinate vector in a rational division algebra with integral structure constants.
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
  ext i j
  have hj : Algebra.TensorProduct.rTensor B φ (Algebra.TensorProduct.basis P b j) =
      Algebra.TensorProduct.basis T b j := by simp
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← hj, ← map_mul]
  exact Algebra.TensorProduct.basis_repr_rTensor b φ _ i

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
  simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, Matrix.algebraMap_matrix_apply,
    Polynomial.algebraMap_eq]

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

section BasisCoordinates

variable {R S B : Type*} [CommSemiring R] [CommRing S] [Ring B] [Algebra R S] [Algebra R B]
variable {ι : Type*} [Fintype ι]

/-- The regular norm in scalar-extended basis coordinates is the determinant of the
left-multiplication matrix obtained by mapping the structure constants along `algebraMap R S`. -/
theorem _root_.Module.Basis.norm_baseChange_equivFun_symm [DecidableEq ι]
    (b : Module.Basis ι R B) (x : ι → S) :
    Algebra.norm S ((b.baseChange S).equivFun.symm x) =
      (Matrix.of fun i j => ∑ k, x k * algebraMap R S (b.repr (b k * b j) i)).det := by
  rw [Algebra.norm_eq_matrix_det (b.baseChange S)]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.equivFun_symm_apply,
    Module.Basis.baseChange_apply, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Module.Basis.baseChange_repr_tmul, Matrix.of_apply]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply, mul_one]

/-- The coordinate norm is homogeneous of degree equal to the number of basis vectors. -/
theorem _root_.Module.Basis.norm_baseChange_equivFun_symm_smul
    (b : Module.Basis ι R B) (r : S) (x : ι → S) :
    Algebra.norm S ((b.baseChange S).equivFun.symm (r • x)) =
      r ^ Fintype.card ι * Algebra.norm S ((b.baseChange S).equivFun.symm x) := by
  rw [map_smul, Algebra.smul_def, map_mul, Algebra.norm_algebraMap_of_basis (b.baseChange S)]

end BasisCoordinates

/-- A nonzero integer coordinate vector has absolute regular norm at least one in
a rational division algebra basis with integral structure constants. -/
theorem _root_.Module.Basis.one_le_abs_norm_baseChange_intCast {ι D : Type*} [Finite ι]
    [DivisionRing D] [Algebra ℚ D] (b : Module.Basis ι ℚ D)
    (h : ∀ i j k, ∃ z : ℤ, (z : ℚ) = b.repr (b k * b j) i) (z : ι → ℤ)
    (hz : z ≠ 0) :
    1 ≤ |Algebra.norm ℝ ((b.baseChange ℝ).equivFun.symm fun i => (z i : ℝ))| := by
  classical
  let := Fintype.ofFinite ι
  let x := b.equivFun.symm (fun i => (z i : ℚ))
  have hx : x ≠ 0 := by
    intro hx
    apply hz
    have he : b.equivFun x = 0 := by rw [hx, map_zero]
    funext i
    simpa only [x, LinearEquiv.apply_symm_apply, Pi.zero_apply, Int.cast_eq_zero]
      using congrFun he i
  have hreal : (b.baseChange ℝ).equivFun.symm (fun i => (z i : ℝ)) = 1 ⊗ₜ[ℚ] x := by
    apply (b.baseChange ℝ).equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    rw [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
      ← Module.Basis.equivFun_apply, Rat.smul_one_eq_cast]
    dsimp only [x]
    rw [LinearEquiv.apply_symm_apply, Rat.cast_intCast]
  let m : Matrix ι ι ℤ := Matrix.of fun i j => ∑ k, z k * (h i j k).choose
  have hm : m.map (fun n => (n : ℝ)) =
      Matrix.of (fun i j => ∑ k, (z k : ℝ) * (b.repr (b k * b j) i : ℝ)) := by
    ext i j
    simp only [m, Matrix.map_apply, Matrix.of_apply, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simpa only [Rat.cast_intCast] using
      congrArg (fun q : ℚ => (q : ℝ)) (h i j k).choose_spec
  have hnorm : Algebra.norm ℝ ((b.baseChange ℝ).equivFun.symm fun i => (z i : ℝ)) =
      (m.det : ℝ) := by
    simp only [b.norm_baseChange_equivFun_symm, eq_ratCast, ← hm, ← Int.cast_det]
  have hne : m.det ≠ 0 := by
    intro he
    rw [he, Int.cast_zero, hreal, TauCeti.Algebra.norm_baseChange_tmul] at hnorm
    exact (Algebra.norm_ne_zero_iff_of_basis b).mpr hx
      ((algebraMap ℚ ℝ).injective (by simpa using hnorm))
  rw [hnorm, ← Int.cast_abs, ← Int.cast_one]
  exact_mod_cast Int.one_le_abs hne

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
    rw [Algebra.trace_eq_zero_of_not_finite hfin,
      Algebra.trace_eq_zero_of_not_finite (mt Module.Finite.of_baseChange hfin)]
    simp

/-- Trace on a scalar extension evaluates on any pure tensor `a ⊗ₜ x` as
`a * algebraMap K A (Algebra.trace K B x)`. When `B` is not finite over `K` both sides are `0`. -/
theorem Algebra.trace_tmul (a : A) (x : B) :
    Algebra.trace A (A ⊗[K] B) (a ⊗ₜ[K] x) = a * algebraMap K A (Algebra.trace K B x) := by
  conv_lhs => rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul']
  rw [map_smul, Algebra.trace_baseChange_tmul, smul_eq_mul]

/-- Scalar multiplication and the trace pairing commute with scalar extension on pure tensors. -/
theorem Algebra.trace_tmul_mul_smul (a : A) (x b y : B) :
    Algebra.trace A (A ⊗[K] B) ((a ⊗ₜ[K] x) * (1 ⊗ₜ[K] b)) • ((1 : A) ⊗ₜ[K] y) =
      a ⊗ₜ[K] (Algebra.trace K B (x * b) • y) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.trace_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, mul_comm a, ← Algebra.smul_def,
    TensorProduct.smul_tmul]

/-- **Trace-dual expansions pass to scalar extensions.** If `x = ∑ᵢ Tr_{B/K}(x bᵢ) yᵢ` for every
`x : B`, then the same expansion holds for every `ξ : A ⊗[K] B` over `A`. -/
theorem Algebra.sum_trace_mul_smul_tmul_eq {ι : Type*} [Fintype ι] (b y : ι → B)
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

variable {R S T C : Type*} [CommSemiring R] [CommRing S] [CommRing T] [CommSemiring C]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra R C]
  [Module.Free S (S ⊗[R] C)]

/-- Let `R → S → T` be a tower of commutative semirings, with `S` and `T` rings, and `C` a
commutative `R`-algebra with `S ⊗[R] C` free over `S`. The trace of `1 ⊗ c` in `T ⊗[R] C` over
`T` is the image of the trace of `1 ⊗ c` in `S ⊗[R] C` over `S`. -/
theorem Algebra.trace_baseChange_tmul_of_isScalarTower (c : C) :
    Algebra.trace T (T ⊗[R] C) (1 ⊗ₜ c) =
      algebraMap S T (Algebra.trace S (S ⊗[R] C) (1 ⊗ₜ c)) := by
  rw [← Algebra.trace_baseChange_tmul (A := T),
    ← Algebra.trace_eq_of_algEquiv (Algebra.TensorProduct.cancelBaseChange R S T T C)]
  simp

end TraceTower

end TauCeti
