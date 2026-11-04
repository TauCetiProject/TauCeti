/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Real matrices as complex matrices

A real matrix `N` is viewed as a complex matrix through the entrywise coercion
`N.map ((↑) : ℝ → ℂ)`. This file records that the entrywise real part `Complex.re` is real-linear
for left and right multiplication by real matrices, that a real orthogonal matrix is unitary as a
complex matrix, and how the real Gram matrix `Re (Mᴴ M)` of the columns of a complex matrix `M`
behaves: it transforms by congruence under a real change of basis, and it is positive definite
when `Mᴴ M` is.

## Main results

* `Matrix.map_re_map_ofReal_mul`, `Matrix.map_re_mul_map_ofReal`: the real part of a complex
  matrix multiplied by a real matrix.
* `Matrix.map_ofReal_mem_unitaryGroup`: an orthogonal real matrix is unitary.
* `Matrix.map_re_conjTranspose_mul_self_mul_map_ofReal`: the real Gram matrix of `M N` for a real
  matrix `N` is `Nᵀ Re (Mᴴ M) N`.
* `Matrix.PosDef.map_re`: the real part of a positive definite complex matrix is positive
  definite.
-/

public section

open scoped ComplexOrder

namespace Matrix

variable {l m n : Type*}

/-- The real part of a real matrix times a complex matrix is the real matrix times the real
part. -/
theorem map_re_map_ofReal_mul [Fintype m] (N : Matrix l m ℝ) (K : Matrix m n ℂ) :
    (N.map ((↑) : ℝ → ℂ) * K).map Complex.re = N * K.map Complex.re := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum]

/-- The real part of a complex matrix times a real matrix is the real part times the real
matrix. -/
theorem map_re_mul_map_ofReal [Fintype m] (K : Matrix l m ℂ) (N : Matrix m n ℝ) :
    (K * N.map ((↑) : ℝ → ℂ)).map Complex.re = K.map Complex.re * N := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum]

/-- An orthogonal real matrix is unitary as a complex matrix. -/
theorem map_ofReal_mem_unitaryGroup [Fintype n] [DecidableEq n] {O : Matrix n n ℝ}
    (hO : O ∈ orthogonalGroup n ℝ) : O.map ((↑) : ℝ → ℂ) ∈ unitaryGroup n ℂ := by
  rw [mem_orthogonalGroup_iff'] at hO
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose,
    ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial]
  exact (map_mul Complex.ofRealHom.mapMatrix _ _).symm.trans ((congrArg _ hO).trans (map_one _))

/-- The real Gram matrix `Re ((M N)ᴴ (M N))` of the columns of `M N`, for a real matrix `N`, is
`Nᵀ Re (Mᴴ M) N`. -/
theorem map_re_conjTranspose_mul_self_mul_map_ofReal [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (N : Matrix n l ℝ) :
    ((M * N.map ((↑) : ℝ → ℂ))ᴴ * (M * N.map ((↑) : ℝ → ℂ))).map Complex.re =
      Nᵀ * (Mᴴ * M).map Complex.re * N := by
  rw [conjTranspose_mul, ← conjTranspose_map _ fun _ ↦ (Complex.conj_ofReal _).symm,
    conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ,
    map_re_map_ofReal_mul, map_re_mul_map_ofReal, Matrix.mul_assoc]

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

end Matrix
