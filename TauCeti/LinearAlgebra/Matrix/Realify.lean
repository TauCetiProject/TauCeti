/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The realification of a matrix over an RCLike field

An `m × n` matrix `A` over an `RCLike` field induces an `ℝ`-linear map, and splitting its entries
into real and imaginary parts gives the real `(m ⊕ m) × (n ⊕ n)` matrix

`Matrix.realify A = !![Re A, -Im A; Im A, Re A]`,

the *realification* of `A`. It is additive and multiplicative and turns the conjugate transpose
into the transpose, so it carries Hermitian matrices to symmetric ones and `*`-congruence to
congruence. This is what lets real quadratic-form theory be applied to Hermitian forms.

## Main definitions

* `Matrix.realify`: the real matrix of the `ℝ`-linear map a complex matrix induces.
* `TauCeti.realifyReflection`: the reflection of `ℝ^ι ⊕ ℝ^ι` negating the second summand, which
  realises entrywise conjugation as a congruence of realifications.

## Main results

* `Matrix.realify_mul`, `Matrix.realify_one`, `Matrix.realify_add`, `Matrix.realify_smul`:
  realification is real-linear and multiplicative.
* `Matrix.realify_conjTranspose`: the conjugate transpose becomes the transpose.
* `Matrix.IsHermitian.isSymm_realify`: a Hermitian matrix realifies to a symmetric one.
* `Matrix.realify_map_ofReal`: a real matrix realifies to two diagonal copies of itself.
* `Matrix.isUnit_det_realify`: realification preserves invertibility.
* `Matrix.realify_map_starRingEnd`: entrywise conjugation becomes congruence by the reflection
  `TauCeti.realifyReflection` that negates the imaginary coordinates.
-/

public section

open scoped Matrix

variable {l m n ι : Type*}

namespace TauCeti

/-- The reflection of `ℝ^ι ⊕ ℝ^ι` negating the second summand, which realises conjugation as a
congruence of realifications. -/
def realifyReflection (ι : Type*) [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 1 0 0 (-1)

@[simp]
theorem realifyReflection_transpose [DecidableEq ι] :
    (realifyReflection ι)ᵀ = realifyReflection ι := by
  simp [realifyReflection, Matrix.fromBlocks_transpose]

@[simp]
theorem realifyReflection_mul_self [Fintype ι] [DecidableEq ι] :
    realifyReflection ι * realifyReflection ι = 1 := by
  simp [realifyReflection, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem isUnit_det_realifyReflection [Fintype ι] [DecidableEq ι] :
    IsUnit (realifyReflection ι).det :=
  Matrix.isUnit_det_of_left_inverse realifyReflection_mul_self

end TauCeti

namespace Matrix

open TauCeti

/-- The realification of a matrix over an `RCLike` field, obtained by splitting its entries into
real and imaginary parts. -/
def realify {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) : Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  fromBlocks (A.map RCLike.re) (-(A.map RCLike.im)) (A.map RCLike.im) (A.map RCLike.re)

@[simp]
theorem realify_apply_inl_inl {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (i : m) (j : n) :
    A.realify (Sum.inl i) (Sum.inl j) = RCLike.re (A i j) := by simp [realify]

@[simp]
theorem realify_apply_inl_inr {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (i : m) (j : n) :
    A.realify (Sum.inl i) (Sum.inr j) = -RCLike.im (A i j) := by simp [realify]

@[simp]
theorem realify_apply_inr_inl {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (i : m) (j : n) :
    A.realify (Sum.inr i) (Sum.inl j) = RCLike.im (A i j) := by simp [realify]

@[simp]
theorem realify_apply_inr_inr {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) (i : m) (j : n) :
    A.realify (Sum.inr i) (Sum.inr j) = RCLike.re (A i j) := by simp [realify]

@[simp]
theorem realify_zero {𝕜 : Type*} [RCLike 𝕜] : (0 : Matrix m n 𝕜).realify = 0 := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp

/-- Realification preserves addition. -/
@[simp]
theorem realify_add {𝕜 : Type*} [RCLike 𝕜] (A B : Matrix m n 𝕜) :
    (A + B).realify = A.realify + B.realify := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp
  ring

@[simp]
theorem realify_neg {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) :
    (-A).realify = -A.realify := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp

/-- Realification commutes with real scalar multiplication. -/
@[simp]
theorem realify_smul {𝕜 : Type*} [RCLike 𝕜] (r : ℝ) (A : Matrix m n 𝕜) :
    (r • A).realify = r • A.realify := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;>
    simp [RCLike.smul_re, RCLike.smul_im]

/-- A matrix with real entries realifies to two diagonal copies of itself. -/
@[simp]
theorem realify_map_ofReal {𝕜 : Type*} [RCLike 𝕜] (M : Matrix m n ℝ) :
    (M.map (algebraMap ℝ 𝕜)).realify = fromBlocks M 0 0 M := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp

/-- Realification preserves the identity matrix. -/
@[simp]
theorem realify_one {𝕜 : Type*} [RCLike 𝕜] [DecidableEq ι] :
    (1 : Matrix ι ι 𝕜).realify = 1 := by
  rw [← Matrix.map_one (algebraMap ℝ 𝕜) (by simp) (by simp), realify_map_ofReal, fromBlocks_one]

/-- Realification preserves matrix multiplication. -/
@[simp]
theorem realify_mul {𝕜 : Type*} [RCLike 𝕜] [Fintype n] (A : Matrix m n 𝕜)
    (B : Matrix n l 𝕜) :
    (A * B).realify = A.realify * B.realify := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, RCLike.mul_re, RCLike.mul_im,
      Finset.sum_sub_distrib, Finset.sum_add_distrib] <;> ring

/-- Realification turns the conjugate transpose into the transpose. -/
@[simp]
theorem realify_conjTranspose {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m n 𝕜) :
    (Aᴴ).realify = (A.realify)ᵀ := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp [conjTranspose_apply]

/-- Realification carries Hermitian matrices to symmetric ones. -/
theorem IsHermitian.isSymm_realify {𝕜 : Type*} [RCLike 𝕜] {A : Matrix ι ι 𝕜}
    (hA : Matrix.IsHermitian A) :
    A.realify.IsSymm := by
  rw [Matrix.IsSymm, ← realify_conjTranspose, hA.eq]

/-- Realification preserves invertibility. -/
theorem isUnit_det_realify {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι 𝕜} (h : IsUnit A.det) :
    IsUnit (A.realify).det := by
  refine Matrix.isUnit_det_of_left_inverse (B := (A⁻¹).realify) ?_
  rw [← realify_mul, Matrix.nonsing_inv_mul _ h, realify_one]

/-- Entrywise conjugation becomes congruence by the reflection negating the imaginary
coordinates. -/
theorem realify_map_starRingEnd {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) :
    (A.map (starRingEnd 𝕜)).realify =
      realifyReflection ι * A.realify * (realifyReflection ι)ᵀ := by
  rw [realifyReflection_transpose]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;>
    simp [realifyReflection, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      Finset.sum_ite_eq', Finset.sum_ite_eq]

end Matrix
