/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Matrix.Normed

/-!
# Smooth matrix and vector products

Matrix multiplication, matrix-vector multiplication, vector dot products, and outer products
preserve smoothness of families. These rules use the usual finite-product norms, without choosing
a matrix algebra norm, and support smooth paths assembled from elementary matrices and vectors.
-/

public section

open scoped ContDiff Matrix Matrix.Norms.Elementwise

variable {𝕜 R E : Type*} [NontriviallyNormedField 𝕜]
  [NormedRing R] [NormedAlgebra 𝕜 R] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] {k : ℕ∞ω}

/-- The product of two smooth matrix families is smooth. -/
@[fun_prop]
theorem ContDiff.matrix_mul {f : E → Matrix m n R} {g : E → Matrix n p R}
    (hf : ContDiff 𝕜 k f) (hg : ContDiff 𝕜 k g) :
    ContDiff 𝕜 k (fun x => f x * g x) := by
  refine contDiff_pi' fun i => contDiff_pi' fun j => ?_
  simp only [Matrix.mul_apply]
  fun_prop

/-- The dot product of two smooth vector families is smooth. -/
@[fun_prop]
theorem ContDiff.dotProduct {f g : E → n → R}
    (hf : ContDiff 𝕜 k f) (hg : ContDiff 𝕜 k g) :
    ContDiff 𝕜 k (fun x => f x ⬝ᵥ g x) := by
  simp only [_root_.dotProduct]
  fun_prop

/-- Applying a smooth matrix family to a smooth vector family is smooth. -/
@[fun_prop]
theorem ContDiff.matrix_mulVec {f : E → Matrix m n R} {g : E → n → R}
    (hf : ContDiff 𝕜 k f) (hg : ContDiff 𝕜 k g) :
    ContDiff 𝕜 k (fun x => f x *ᵥ g x) := by
  refine contDiff_pi' fun i => ?_
  simp only [Matrix.mulVec]
  exact (contDiff_pi.mp hf i).dotProduct hg

/-- The outer product of two smooth vector families is smooth. -/
@[fun_prop]
theorem ContDiff.matrix_vecMulVec {f : E → m → R} {g : E → n → R}
    (hf : ContDiff 𝕜 k f) (hg : ContDiff 𝕜 k g) :
    ContDiff 𝕜 k (fun x => Matrix.vecMulVec (f x) (g x)) := by
  refine contDiff_pi' fun i => contDiff_pi' fun j => ?_
  simp only [Matrix.vecMulVec_apply]
  fun_prop
