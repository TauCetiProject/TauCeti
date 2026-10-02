/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.Algebra.Lie.GeneralLinear.Basic
public import TauCeti.Analysis.Normed.Algebra.MatrixExponential

/-!
# Matrix exponential lines in the special linear group

This file identifies the real matrices whose whole exponential line consists of matrices of
determinant one: they are exactly the trace-zero matrices, the elements of Mathlib's special
linear Lie algebra `LieAlgebra.SpecialLinear.sl n ℝ`. It is the special linear companion of the
orthogonal and symplectic characterizations in
`TauCeti/Geometry/Lie/Exponential/Matrix/SpecialOrthogonal.lean` and
`TauCeti/Geometry/Lie/Exponential/Matrix/Symplectic.lean`.

Both directions are read off `Matrix.det_exp`: the determinant of `exp (t • A)` is
`exp (t * trace A)`, and a real exponential is `1` exactly at `0`. Over `ℝ` the single value
`t = 1` already detects the trace, unlike the complex case, where `exp (2πi) = 1`.

## Main results

* `Matrix.det_exp_eq_one_of_mem_sl`: the exponential of a trace-zero matrix has determinant one.
* `Matrix.forall_det_exp_smul_eq_one_iff_mem_sl`: a real matrix generates a one-parameter
  subgroup of determinant-one matrices exactly when it lies in the special linear Lie algebra.
-/

public section

open NormedSpace
open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The exponential of a trace-zero matrix over `ℝ` or `ℂ` has determinant one. -/
theorem det_exp_eq_one_of_mem_sl {𝕂 : Type*} [RCLike 𝕂] (A : Matrix n n 𝕂)
    (hA : A ∈ LieAlgebra.SpecialLinear.sl n 𝕂) : (exp A).det = 1 := by
  rw [det_exp, LieAlgebra.SpecialLinear.mem_sl_iff.mp hA, exp_zero]

/-- A real matrix generates a one-parameter subgroup of determinant-one matrices exactly when it
has trace zero, that is, exactly when it lies in the special linear Lie algebra. -/
@[simp]
theorem forall_det_exp_smul_eq_one_iff_mem_sl (A : Matrix n n ℝ) :
    (∀ t : ℝ, (exp (t • A)).det = 1) ↔ A ∈ LieAlgebra.SpecialLinear.sl n ℝ := by
  refine ⟨fun h => ?_, fun hA t =>
    det_exp_eq_one_of_mem_sl (t • A) ((LieAlgebra.SpecialLinear.sl n ℝ).smul_mem t hA)⟩
  have h1 := h 1
  rw [one_smul, det_exp, ← Real.exp_eq_exp_ℝ, Real.exp_eq_one_iff] at h1
  exact LieAlgebra.SpecialLinear.mem_sl_iff.mpr h1

end Matrix
