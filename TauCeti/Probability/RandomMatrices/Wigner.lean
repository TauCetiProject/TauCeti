/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Wigner matrices

The normalized Wigner matrix built from the upper-triangular entries of an infinite array.
-/

public section

noncomputable section

namespace Matrix

/-- Index set of the strictly upper-triangular positions of an infinite matrix. -/
abbrev StrictUpper := {ij : ℕ × ℕ // ij.1 < ij.2}

/-- The normalized Wigner matrix `Wₙ / √n` built from the top-left `n × n` corner of an infinite
array: complex entries above the diagonal, their conjugates below it, and real entries on it. -/
def wignerMatrix {Ω : Type*} (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j ↦ ((Real.sqrt n)⁻¹ : ℂ) *
    if h : i.val < j.val then ξ ⟨(i.val, j.val), h⟩ ω
    else if h' : j.val < i.val then star (ξ ⟨(j.val, i.val), h'⟩ ω)
    else (η i.val ω : ℂ)

/-- The normalized Wigner matrix is Hermitian for every sample point. -/
theorem wignerMatrix_isHermitian {Ω : Type*} (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : (wignerMatrix ξ η n ω).IsHermitian := by
  ext i j
  simp only [wignerMatrix, conjTranspose_apply, of_apply, star_mul', star_inv₀,
    Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp [h, h.not_gt]
  · simp [Fin.ext h]
  · simp [h, h.not_gt]

end Matrix
