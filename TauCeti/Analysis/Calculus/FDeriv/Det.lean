/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The derivative of the determinant at the identity

The determinant of a square matrix over a complete nontrivially normed field is a polynomial in
the entries, hence differentiable, and its derivative at the identity matrix is the trace:

`det (1 + H) = 1 + trace H + o(H)`.

This is Jacobi's formula at the identity. Along a line it is the statement that the polynomial
`t ↦ det (1 + t • B)` has linear coefficient `trace B`, which Mathlib records as
`Matrix.derivative_det_one_add_X_smul`; differentiability of the determinant then upgrades that
directional derivative to the Fréchet derivative.

The normed structure on matrices is Mathlib's `L∞` operator norm, available through
`open scoped Matrix.Norms.Operator`; any other norm on the finite-dimensional space of matrices
gives the same derivative.

## Main results

* `Matrix.hasDerivAt_det_one_add_smul`: `t ↦ det (1 + t • B)` has derivative `trace B` at `0`.
* `Matrix.differentiable_det`: the determinant is differentiable.
* `Matrix.hasFDerivAt_det_one`: **the derivative of the determinant at the identity is the
  trace.**
-/

public section

open Polynomial
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The determinant along the line through the identity in the direction `B` has derivative
`trace B` at the identity. -/
theorem hasDerivAt_det_one_add_smul (B : Matrix n n 𝕜) :
    HasDerivAt (fun t : 𝕜 => det (1 + t • B)) (trace B) 0 := by
  have h := (det (1 + (X : 𝕜[X]) • B.map C)).hasDerivAt 0
  rw [derivative_det_one_add_X_smul] at h
  convert h using 1
  funext t
  simp [eval_det, ← smul_eq_mul_diagonal]

variable [CompleteSpace 𝕜]

/-- The determinant is differentiable: it is a sum of products of matrix entries. -/
theorem differentiable_det : Differentiable 𝕜 (det : Matrix n n 𝕜 → 𝕜) := by
  have hentry (i j : n) : Differentiable 𝕜 (fun M : Matrix n n 𝕜 => M i j) :=
    (LinearMap.toContinuousLinearMap (entryLinearMap 𝕜 𝕜 i j)).differentiable
  simp_rw [_root_.funext det_apply, Units.smul_def, zsmul_eq_mul]
  refine Differentiable.fun_sum fun σ _ => Differentiable.const_mul (fun M => ?_) _
  exact (HasFDerivAt.finsetProd fun i _ => (hentry (σ i) i M).hasFDerivAt).differentiableAt

/-- **The derivative of the determinant at the identity is the trace** (Jacobi's formula at the
identity). -/
theorem hasFDerivAt_det_one :
    HasFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      (LinearMap.toContinuousLinearMap (traceLinearMap n 𝕜 𝕜)) 1 := by
  have hD := (differentiable_det (𝕜 := 𝕜) (n := n) 1).hasFDerivAt
  suffices h : fderiv 𝕜 det (1 : Matrix n n 𝕜) =
      LinearMap.toContinuousLinearMap (traceLinearMap n 𝕜 𝕜) by rwa [h] at hD
  refine ContinuousLinearMap.ext fun B => ?_
  have h := hD.comp_hasDerivAt_of_eq (0 : 𝕜)
    (((hasDerivAt_id (0 : 𝕜)).smul_const B).const_add 1) (by simp)
  simp only [id, one_smul] at h
  -- `h` is stated for the operator-norm addition on matrices; restating it with the default
  -- matrix addition, to which it is definitionally equal, lets it meet the line derivative.
  have h' : HasDerivAt (fun t : 𝕜 => det (1 + t • B)) (fderiv 𝕜 det 1 B) 0 := h
  simpa using h'.unique (hasDerivAt_det_one_add_smul B)

end Matrix
