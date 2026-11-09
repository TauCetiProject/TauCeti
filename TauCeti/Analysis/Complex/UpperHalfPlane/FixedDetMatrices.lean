/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Integral matrices of fixed determinant acting on the upper half-plane

For `n ≠ 0`, an integral `2 × 2` matrix `A` of determinant `n` acts on the upper half-plane
through its image `FixedDetMatrices.toGLReal hn A` in `GL(2, ℝ)`. For `0 < n` this is the Möbius
transformation `τ ↦ (a τ + b) / (c τ + d)`; for `n < 0` it is that transformation followed by
complex conjugation, `τ ↦ conj ((a τ + b) / (c τ + d))`, as for Mathlib's action of `GL(2, ℝ)`
on the upper half-plane. This file records that left multiplication by `SL(2, ℤ)` on `A`
becomes composition of the actions, and that for `0 < n` the action is holomorphic.

## Main results

* `FixedDetMatrices.toGLReal_smul_smul`: the action of `g • A` is that of `A` followed by `g`.
* `FixedDetMatrices.mdifferentiable_toGLReal_smul`: for `0 < n` the action of `A` is holomorphic.
-/

public section

open Matrix UpperHalfPlane
open scoped MatrixGroups Manifold

namespace FixedDetMatrices

variable {n : ℤ}

/-- The action of `g • A` on the upper half-plane is that of `A` followed by that of `g`. -/
theorem toGLReal_smul_smul (hn : n ≠ 0) (g : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ n)
    (τ : ℍ) : toGLReal hn (g • A) • τ = g • toGLReal hn A • τ := by
  rw [toGLReal_smul, mul_smul]
  exact (MulAction.compHom_smul_def _ _ _).symm

/-- For `0 < n`, the action of an integral matrix of determinant `n` on the upper half-plane is
holomorphic. -/
theorem mdifferentiable_toGLReal_smul (hn : 0 < n) (A : FixedDetMatrix (Fin 2) ℤ n) :
    MDiff fun τ : ℍ ↦ toGLReal hn.ne' A • τ :=
  mdifferentiable_smul (by rw [det_toGLReal]; exact_mod_cast hn)

end FixedDetMatrices
