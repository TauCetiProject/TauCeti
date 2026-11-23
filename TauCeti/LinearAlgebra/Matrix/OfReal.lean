/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.DetDescent
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse

/-!
# Real matrices as complex matrices

A real matrix `N` is viewed as a complex matrix through the entrywise coercion
`N.map ((↑) : ℝ → ℂ)`. This file records that a real orthogonal matrix is unitary and a real
symmetric matrix Hermitian as a complex matrix, that the determinant does not change, and how the
real Gram matrix `Re (Mᴴ M)` of the columns of a complex matrix `M` behaves: it transforms by
congruence under a real change of basis, and it is positive definite when `Mᴴ M` is, in particular
when `M` has independent columns. The imaginary part `Im (Mᴴ M)`, the matrix of the symplectic
form `Im ⟪·, ·⟫` on the columns, transforms by the same congruence.

## Main results

* `Matrix.map_ofReal_mul_transpose_map_ofReal_eq_one`: an orthogonal real matrix `O` satisfies
  `O Oᵀ = 1` as a complex matrix.
* `Matrix.map_ofReal_mem_unitaryGroup`: an orthogonal real matrix is unitary.
* `Matrix.IsHermitian.map_ofReal`: a real symmetric matrix is Hermitian.
* `Matrix.map_ofReal_mul`, `Matrix.map_ofReal_one`, `Matrix.trace_map_ofReal`: the entrywise
  coercion is multiplicative, preserves the identity and commutes with the trace.
* `Matrix.isUnit_map_ofReal_iff`: a real matrix is invertible exactly when it is invertible as a
  complex matrix.
* `Matrix.det_map_ofReal`: the determinant of a real matrix is unchanged as a complex matrix.
* `Matrix.map_re_conjTranspose_mul_self_mul_map_ofReal`: the real Gram matrix of `M N` for a real
  matrix `N` is `Nᵀ Re (Mᴴ M) N`.
* `Matrix.map_im_conjTranspose_mul_self_mul_map_ofReal`: likewise, the imaginary part of the Gram
  matrix of `M N` is `Nᵀ Im (Mᴴ M) N`.
* `Matrix.PosDef.map_re`: the real part of a positive definite complex matrix is positive
  definite.
* `Matrix.PosDef.map_re_conjTranspose_mul_self`: the real Gram matrix of a complex matrix with
  independent columns is positive definite.
-/

public section

open scoped ComplexOrder

namespace Matrix

variable {l m n : Type*}

/-- The complex image `O` of an orthogonal real matrix `O` satisfies `O Oᵀ = 1`. -/
theorem map_ofReal_mul_transpose_map_ofReal_eq_one [Fintype n] [DecidableEq n] {O : Matrix n n ℝ}
    (hO : O ∈ orthogonalGroup n ℝ) : O.map ((↑) : ℝ → ℂ) * (O.map ((↑) : ℝ → ℂ))ᵀ = 1 := by
  rw [← transpose_map]
  -- `N.map (↑)` is `Complex.ofRealHom.mapMatrix N`, which is multiplicative.
  exact (map_mul Complex.ofRealHom.mapMatrix _ _).symm.trans
    ((congrArg _ ((mem_orthogonalGroup_iff _ _).1 hO)).trans (map_one _))

/-- An orthogonal real matrix is unitary as a complex matrix. -/
theorem map_ofReal_mem_unitaryGroup [Fintype n] [DecidableEq n] {O : Matrix n n ℝ}
    (hO : O ∈ orthogonalGroup n ℝ) : O.map ((↑) : ℝ → ℂ) ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose,
    ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial, transpose_map]
  exact map_ofReal_mul_transpose_map_ofReal_eq_one hO

/-- A real symmetric matrix is Hermitian as a complex matrix. -/
theorem IsHermitian.map_ofReal {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (A.map ((↑) : ℝ → ℂ)).IsHermitian :=
  hA.map _ fun _ ↦ by simp

/-- The entrywise coercion of real matrices to complex matrices is multiplicative. -/
@[simp]
theorem map_ofReal_mul [Fintype m] (X : Matrix l m ℝ) (Y : Matrix m n ℝ) :
    (X * Y).map ((↑) : ℝ → ℂ) = X.map (↑) * Y.map (↑) :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- The entrywise coercion of the real identity matrix is the complex identity matrix. -/
theorem map_ofReal_one [DecidableEq n] : (1 : Matrix n n ℝ).map ((↑) : ℝ → ℂ) = 1 :=
  Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

/-- The trace of a real matrix, viewed as a complex matrix, is the coercion of its trace. -/
@[simp]
theorem trace_map_ofReal [Fintype n] (X : Matrix n n ℝ) :
    trace (X.map ((↑) : ℝ → ℂ)) = ((trace X : ℝ) : ℂ) :=
  (AddMonoidHom.map_trace Complex.ofRealHom X).symm

/-- A real square matrix is invertible exactly when it is invertible as a complex matrix: the
case `ℝ → ℂ` of `Matrix.isUnit_map_iff`. -/
@[simp]
theorem isUnit_map_ofReal_iff [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} :
    IsUnit (M.map ((↑) : ℝ → ℂ)) ↔ IsUnit M :=
  isUnit_map_iff Complex.ofRealHom M

/-- The determinant of the complex image of a real matrix is the image of its determinant. -/
@[simp]
theorem det_map_ofReal [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    (M.map ((↑) : ℝ → ℂ)).det = M.det :=
  (Complex.ofRealHom.map_det M).symm

/-- The real Gram matrix `Re ((M N)ᴴ (M N))` of the columns of `M N`, for a real matrix `N`, is
`Nᵀ Re (Mᴴ M) N`. -/
theorem map_re_conjTranspose_mul_self_mul_map_ofReal [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (N : Matrix n l ℝ) :
    ((M * N.map ((↑) : ℝ → ℂ))ᴴ * (M * N.map ((↑) : ℝ → ℂ))).map Complex.re =
      Nᵀ * (Mᴴ * M).map Complex.re * N := by
  rw [conjTranspose_mul, ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ]
  exact ((map_algebraMap_mul Complex.reLm Nᵀ _).trans
    (congrArg (Nᵀ * ·) (map_mul_algebraMap Complex.reLm N (Mᴴ * M)))).trans
      (Matrix.mul_assoc _ _ _).symm

/-- The imaginary part `Im ((M N)ᴴ (M N))` of the Gram matrix of the columns of `M N`, for a real
matrix `N`, is `Nᵀ Im (Mᴴ M) N`. -/
theorem map_im_conjTranspose_mul_self_mul_map_ofReal [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (N : Matrix n l ℝ) :
    ((M * N.map ((↑) : ℝ → ℂ))ᴴ * (M * N.map ((↑) : ℝ → ℂ))).map Complex.im =
      Nᵀ * (Mᴴ * M).map Complex.im * N := by
  rw [conjTranspose_mul, ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ]
  exact ((map_algebraMap_mul Complex.imLm Nᵀ _).trans
    (congrArg (Nᵀ * ·) (map_mul_algebraMap Complex.imLm N (Mᴴ * M)))).trans
      (Matrix.mul_assoc _ _ _).symm

/-- The real part of a positive definite complex matrix is positive definite. -/
theorem PosDef.map_re [Finite n] {K : Matrix n n ℂ} (hK : K.PosDef) :
    (K.map Complex.re).PosDef := by
  have := Fintype.ofFinite n
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · ext i j
    have := congrFun (congrFun hK.1 i) j
    simp only [conjTranspose_apply, RCLike.star_def] at this
    simp only [conjTranspose_apply, map_apply, star_trivial, ← this, Complex.conj_re]
  · set xc : n → ℂ := fun i ↦ (x i : ℂ)
    have hxc : xc ≠ 0 := fun h ↦ hx (funext fun i ↦ by simpa [xc] using congrFun h i)
    have hre : (star xc ⬝ᵥ (K *ᵥ xc)).re = star x ⬝ᵥ (K.map Complex.re *ᵥ x) := by
      simp [xc, dotProduct, mulVec, Complex.re_sum, Finset.mul_sum]
    rw [← hre]
    exact (Complex.pos_iff.1 (hK.dotProduct_mulVec_pos hxc)).1

/-- The real Gram matrix `Re (Mᴴ M)` of a complex matrix `M` with linearly independent columns is
positive definite. -/
theorem PosDef.map_re_conjTranspose_mul_self [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (hM : Function.Injective M.mulVec) : ((Mᴴ * M).map Complex.re).PosDef :=
  (PosDef.conjTranspose_mul_self M hM).map_re

end Matrix
