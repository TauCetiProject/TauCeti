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
# Smooth matrix products

Matrix multiplication preserves smoothness of families. This rule uses the usual finite-product
norms, without choosing a matrix algebra norm, and supports smooth paths assembled from
elementary matrices.
-/

public section

open scoped ContDiff Matrix.Norms.Elementwise

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
