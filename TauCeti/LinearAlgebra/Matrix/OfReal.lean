/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Real matrices as complex matrices

A real matrix `N` is viewed as a complex matrix through the entrywise coercion
`N.map ((↑) : ℝ → ℂ)`. This file records that this embedding is multiplicative, that the entrywise
real part `Complex.re` is real-linear for left and right multiplication by real matrices, and
that a real orthogonal matrix is unitary as a complex matrix.

## Main results

* `Matrix.map_ofReal_mul`, `Matrix.map_ofReal_one`: the coercion of real matrices to complex
  matrices is multiplicative and unital.
* `Matrix.map_re_map_ofReal_mul`, `Matrix.map_re_mul_map_ofReal`: the real part of a complex
  matrix multiplied by a real matrix.
* `Matrix.map_ofReal_mem_unitaryGroup`: an orthogonal real matrix is unitary.
-/

public section

namespace Matrix

variable {l m n : Type*}

/-- The coercion of real matrices to complex matrices is multiplicative. -/
theorem map_ofReal_mul [Fintype m] (N : Matrix l m ℝ) (N' : Matrix m n ℝ) :
    (N * N').map ((↑) : ℝ → ℂ) = N.map (↑) * N'.map (↑) :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- The coercion of the real identity matrix is the complex identity matrix. -/
theorem map_ofReal_one [DecidableEq n] : (1 : Matrix n n ℝ).map ((↑) : ℝ → ℂ) = 1 :=
  Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one

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
    conjTranspose_eq_transpose_of_trivial, ← map_ofReal_mul, hO, map_ofReal_one]

end Matrix
