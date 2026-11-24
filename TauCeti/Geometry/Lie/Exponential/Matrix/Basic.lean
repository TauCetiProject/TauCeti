/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.Analysis.Matrix.Normed
public import TauCeti.Geometry.Lie.Exponential.Units.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose

/-!
# Matrix exponentials as units

The Banach-algebra exponential `TauCeti.expUnit` on finite square matrices respects inverse
transpose. The statements use Mathlib's scoped `L∞` operator norm, and apply to matrices over
any complete normed commutative rational algebra.

## Main results

* `Matrix.inverseTranspose_expUnit`: inverse transpose sends `expUnit X` to `expUnit (-Xᵀ)`.
-/

public section

open scoped Matrix Matrix.Norms.Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Matrix

variable {R : Type*} [NormedCommRing R] [NormedAlgebra ℚ R] [CompleteSpace R]

/-- Inverse transpose carries the exponential of `X` to the exponential of `-Xᵀ`. -/
@[simp]
theorem inverseTranspose_expUnit (X : Matrix n n R) :
    GeneralLinearGroup.inverseTranspose (TauCeti.expUnit X) = TauCeti.expUnit (-Xᵀ) := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose, ← TauCeti.expUnit_neg, TauCeti.expUnit_coe,
    TauCeti.expUnit_coe]
  -- The entrywise topology in `Matrix.exp_transpose` agrees definitionally with the
  -- operator-norm topology used in `TauCeti.expUnit`.
  have h := (Matrix.exp_transpose (-X)).symm
  rw [Matrix.transpose_neg] at h
  convert h using 1 <;> rfl

end Matrix
