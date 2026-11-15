/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.Algebra.Lie.GeneralLinear.Basic
public import TauCeti.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.Geometry.Lie.Exponential.OneParameter

/-!
# Matrix exponential lines in the special linear group

This file identifies the matrices over `ℝ` or `ℂ` (any `RCLike` field) whose whole exponential
line consists of matrices of determinant one: they are exactly the trace-zero matrices, the
elements of Mathlib's special linear Lie algebra `LieAlgebra.SpecialLinear.sl n 𝕂`. It is the
special linear companion of the orthogonal and symplectic characterizations in
`TauCeti/Geometry/Lie/Exponential/Matrix/SpecialOrthogonal.lean` and
`TauCeti/Geometry/Lie/Exponential/Matrix/Symplectic.lean`.

Both directions are read off `Matrix.det_exp`: the determinant of `exp (t • A)` is
`exp (t • trace A)`. One single value of `t` is not enough to recover the trace once the field is
not `ℝ`: over `ℂ` a matrix of trace `2πi` already has `det (exp A) = 1`. What the whole line
gives is a comparison of two exponential lines in the field, `t ↦ exp (t • trace A)` and the
constant line `t ↦ exp (t • 0)`, and exponential lines determine their generators
(`TauCeti.eq_of_forall_exp_smul_eq`), so `trace A = 0`.

## Main results

* `Matrix.det_exp_eq_one_of_mem_sl`: the exponential of a trace-zero matrix has determinant one.
* `Matrix.forall_det_exp_smul_eq_one_iff_mem_sl`: a matrix generates a one-parameter
  subgroup of determinant-one matrices exactly when it lies in the special linear Lie algebra.
-/

public section

open NormedSpace
open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕂 : Type*} [RCLike 𝕂]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The exponential of a trace-zero matrix over `ℝ` or `ℂ` has determinant one. -/
theorem det_exp_eq_one_of_mem_sl (A : Matrix n n 𝕂)
    (hA : A ∈ LieAlgebra.SpecialLinear.sl n 𝕂) : (exp A).det = 1 := by
  rw [det_exp, LieAlgebra.SpecialLinear.mem_sl_iff.mp hA, exp_zero]

/-- A matrix generates a one-parameter subgroup of determinant-one matrices exactly when it
has trace zero, that is, exactly when it lies in the special linear Lie algebra.

Over `ℂ` a single time is not enough: `exp` is `1` on the whole lattice `2πiℤ`, so a matrix of
trace `2πi` has `det (exp A) = 1` without having trace zero. The hypothesis is the whole line, and
it is exactly what pins the trace down. -/
@[simp]
theorem forall_det_exp_smul_eq_one_iff_mem_sl (A : Matrix n n 𝕂) :
    (∀ t : ℝ, (exp (t • A)).det = 1) ↔ A ∈ LieAlgebra.SpecialLinear.sl n 𝕂 := by
  constructor
  · intro h
    rw [LieAlgebra.SpecialLinear.mem_sl_iff]
    -- The line `t ↦ exp (t • trace A)` in `𝕂` is constantly `1`, which is the exponential line
    -- of `0`, and a line determines its generator.
    refine TauCeti.eq_of_forall_exp_smul_eq (y := (0 : 𝕂)) fun t => ?_
    rw [smul_zero, exp_zero, ← trace_smul, ← det_exp]
    exact h t
  · intro hA t
    refine det_exp_eq_one_of_mem_sl (t • A) ?_
    -- Real scalars act through `𝕂`, over which `sl` is a Lie subalgebra.
    rw [← algebraMap_smul 𝕂 t A]
    exact (LieAlgebra.SpecialLinear.sl n 𝕂).smul_mem _ hA

end Matrix
