/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The realification of a complex matrix

A complex `m × n` matrix `A` induces an `ℝ`-linear map `ℂ^n → ℂ^m`, and splitting a complex
vector into its real and imaginary parts identifies `ℂ^n` with `ℝ^n ⊕ ℝ^n`. In those coordinates
that map is given by the real `(m ⊕ m) × (n ⊕ n)` matrix

`Matrix.realify A = !![Re A, -Im A; Im A, Re A]`,

the *realification* of `A`. It is additive and multiplicative and turns the conjugate transpose
into the transpose, so it carries Hermitian matrices to symmetric ones and `*`-congruence to
congruence. This is what lets real quadratic-form theory be applied to Hermitian complex forms.

## Main definitions

* `Matrix.realify`: the real matrix of the `ℝ`-linear map a complex matrix induces.
* `TauCeti.realifyReflection`: the reflection of `ℝ^ι ⊕ ℝ^ι` negating the second summand, which
  realises entrywise complex conjugation as a congruence of realifications.

## Main results

* `Matrix.realify_mul`, `Matrix.realify_one`, `Matrix.realify_add`: realification is additive
  and multiplicative.
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

/-- The reflection of `ℝ^ι ⊕ ℝ^ι` negating the second summand, which realises complex
conjugation as a congruence of realifications. -/
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
  (Matrix.isUnit_iff_isUnit_det _).mp
    ⟨⟨realifyReflection ι, realifyReflection ι, realifyReflection_mul_self,
      realifyReflection_mul_self⟩, rfl⟩

end TauCeti

namespace Matrix

open TauCeti

/-- The realification of a complex matrix: the real matrix of the `ℝ`-linear map it induces
from `ℂ^n` to `ℂ^m`, read in the coordinates `ℂ^n ≃ ℝ^n ⊕ ℝ^n` given by real and imaginary
parts. -/
def realify (A : Matrix m n ℂ) : Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  fromBlocks (A.map Complex.re) (-(A.map Complex.im)) (A.map Complex.im) (A.map Complex.re)

@[simp]
theorem realify_apply_inl_inl (A : Matrix m n ℂ) (i : m) (j : n) :
    A.realify (Sum.inl i) (Sum.inl j) = (A i j).re := by simp [realify]

@[simp]
theorem realify_apply_inl_inr (A : Matrix m n ℂ) (i : m) (j : n) :
    A.realify (Sum.inl i) (Sum.inr j) = -(A i j).im := by simp [realify]

@[simp]
theorem realify_apply_inr_inl (A : Matrix m n ℂ) (i : m) (j : n) :
    A.realify (Sum.inr i) (Sum.inl j) = (A i j).im := by simp [realify]

@[simp]
theorem realify_apply_inr_inr (A : Matrix m n ℂ) (i : m) (j : n) :
    A.realify (Sum.inr i) (Sum.inr j) = (A i j).re := by simp [realify]

@[simp]
theorem realify_zero : (0 : Matrix m n ℂ).realify = 0 := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp

/-- Realification preserves addition. -/
@[simp]
theorem realify_add (A B : Matrix m n ℂ) : (A + B).realify = A.realify + B.realify := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp
  ring

@[simp]
theorem realify_neg (A : Matrix m n ℂ) : (-A).realify = -A.realify := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp

/-- A matrix with real entries realifies to two diagonal copies of itself. -/
@[simp]
theorem realify_map_ofReal (M : Matrix m n ℝ) :
    (M.map ((↑) : ℝ → ℂ)).realify = fromBlocks M 0 0 M := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp

/-- Realification preserves the identity matrix. -/
@[simp]
theorem realify_one [DecidableEq ι] : (1 : Matrix ι ι ℂ).realify = 1 := by
  rw [← Matrix.map_one ((↑) : ℝ → ℂ) (by simp) (by simp), realify_map_ofReal, fromBlocks_one]

/-- Realification preserves matrix multiplication. -/
@[simp]
theorem realify_mul [Fintype n] (A : Matrix m n ℂ) (B : Matrix n l ℂ) :
    (A * B).realify = A.realify * B.realify := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Complex.re_sum, Complex.im_sum,
      Complex.mul_re, Complex.mul_im, Finset.sum_sub_distrib, Finset.sum_add_distrib] <;> ring

/-- Realification turns the conjugate transpose into the transpose. -/
@[simp]
theorem realify_conjTranspose (A : Matrix m n ℂ) : (Aᴴ).realify = (A.realify)ᵀ := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> simp [conjTranspose_apply]

/-- Realification carries Hermitian matrices to symmetric ones. -/
theorem IsHermitian.isSymm_realify {A : Matrix ι ι ℂ} (hA : Matrix.IsHermitian A) :
    A.realify.IsSymm := by
  rw [Matrix.IsSymm, ← realify_conjTranspose, hA.eq]

/-- Realification preserves invertibility. -/
theorem isUnit_det_realify [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (h : IsUnit A.det) :
    IsUnit (A.realify).det := by
  have h₁ : A.realify * (A⁻¹).realify = 1 := by
    rw [← realify_mul, Matrix.mul_nonsing_inv _ h, realify_one]
  have h₂ : (A⁻¹).realify * A.realify = 1 := by
    rw [← realify_mul, Matrix.nonsing_inv_mul _ h, realify_one]
  exact (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨A.realify, (A⁻¹).realify, h₁, h₂⟩, rfl⟩

/-- Entrywise complex conjugation becomes congruence by the reflection negating the imaginary
coordinates. -/
theorem realify_map_starRingEnd [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (A.map (starRingEnd ℂ)).realify =
      realifyReflection ι * A.realify * (realifyReflection ι)ᵀ := by
  rw [realifyReflection_transpose]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;>
    simp [realifyReflection, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      Finset.sum_ite_eq', Finset.sum_ite_eq]

end Matrix
