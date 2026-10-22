/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The exponential of a Hermitian complex matrix

Real multiples of a fixed complex matrix commute, so their exponential is multiplicative,
`Matrix.exp_add_smul`, and `exp (β • K)` is the inverse of `exp (-(β • K))`,
`Matrix.exp_smul_mul_exp_neg_smul`. These cancellation laws also hold against an arbitrary factor,
`Matrix.exp_smul_mul_exp_neg_smul_mul`, and conjugating by the two weights does not change the
trace, `Matrix.trace_exp_neg_smul_mul_exp_smul`.

For a Hermitian matrix `K` the exponential `exp (β • K)` of a real multiple is again Hermitian,
`Matrix.IsHermitian.exp_smul`, and has positive trace,
`Matrix.IsHermitian.trace_exp_smul_pos`. Hence `x ↦ Tr (exp (β • K) * x)` is a positive
functional, `Matrix.IsHermitian.trace_exp_smul_mul_nonneg`, the unnormalised Gibbs functional of
a matrix Hamiltonian at inverse temperature `β`.

## Main declarations

* `Matrix.exp_add_smul`: `exp ((s + t) • K) = exp (s • K) * exp (t • K)`.
* `Matrix.exp_smul_mul_exp_neg_smul`, `Matrix.exp_neg_smul_mul_exp_smul` and
  `Matrix.exp_smul_mul_exp_neg_smul_mul`: the cancellation laws for the exponential weights,
  both as plain products and against an arbitrary factor.
* `Matrix.trace_exp_neg_smul_mul_exp_smul`: conjugating by the exponential weights preserves the
  trace.
* `Matrix.IsHermitian.exp_smul`: `exp (β • K)` is Hermitian for Hermitian `K`.
* `Matrix.IsHermitian.trace_exp_smul_mul_nonneg` and `Matrix.IsHermitian.trace_exp_smul_pos`:
  positivity of the unnormalised Gibbs functional and of the Gibbs weight.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Section 5.3.1, for the exponential of a Hamiltonian as an unnormalised Gibbs weight.
-/

public section

noncomputable section

open Complex NormedSpace
open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The exponential of real multiples of a fixed matrix is multiplicative:
`exp ((s + t) • K) = exp (s • K) * exp (t • K)`. -/
theorem exp_add_smul (K : Matrix m m ℂ) (s t : ℝ) :
    exp ((s + t) • K) = exp (s • K) * exp (t • K) := by
  rw [add_smul, exp_add_of_commute _ _ (((Commute.refl K).smul_left _).smul_right _)]

/-- The exponential weight `exp (β • K)` cancels against `exp (-(β • K))`. -/
@[simp]
theorem exp_smul_mul_exp_neg_smul (K : Matrix m m ℂ) (β : ℝ) :
    exp (β • K) * exp (-(β • K)) = 1 := by
  rw [← neg_smul, ← exp_add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]

/-- The exponential weight `exp (-(β • K))` cancels against `exp (β • K)`. -/
@[simp]
theorem exp_neg_smul_mul_exp_smul (K : Matrix m m ℂ) (β : ℝ) :
    exp (-(β • K)) * exp (β • K) = 1 := by
  rw [← neg_smul, ← exp_add_smul, neg_add_cancel, zero_smul, NormedSpace.exp_zero]

/-- Cancellation of the exponential weights against an arbitrary factor. -/
@[simp]
theorem exp_smul_mul_exp_neg_smul_mul (K : Matrix m m ℂ) (β : ℝ) (x : Matrix m m ℂ) :
    exp (β • K) * (exp (-(β • K)) * x) = x := by
  rw [← Matrix.mul_assoc, exp_smul_mul_exp_neg_smul, Matrix.one_mul]

/-- Conjugating by the exponential weights preserves the trace. -/
@[simp]
theorem trace_exp_neg_smul_mul_exp_smul (K : Matrix m m ℂ) (β : ℝ) (x : Matrix m m ℂ) :
    (exp (-(β • K)) * x * exp (β • K)).trace = x.trace := by
  rw [Matrix.trace_mul_comm (exp (-(β • K)) * x) (exp (β • K)), exp_smul_mul_exp_neg_smul_mul]

namespace IsHermitian

variable {K : Matrix m m ℂ}

/-- For a Hermitian matrix `K` the exponential of a real multiple is Hermitian. -/
theorem exp_smul (hK : K.IsHermitian) (β : ℝ) : (NormedSpace.exp (β • K)).IsHermitian :=
  Matrix.IsHermitian.exp ((IsSelfAdjoint.all β).smul hK)

/-- For a Hermitian matrix `K`, the functional `x ↦ Tr (exp (β • K) * x)` is positive. -/
theorem trace_exp_smul_mul_nonneg (hK : K.IsHermitian) (β : ℝ) {x : Matrix m m ℂ}
    (hx : 0 ≤ x) : 0 ≤ (NormedSpace.exp (β • K) * x).trace := by
  have hF : star (NormedSpace.exp ((β / 2) • K)) = NormedSpace.exp ((β / 2) • K) :=
    (exp_smul hK _).eq
  rw [← add_halves β, Matrix.exp_add_smul, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc]
  refine Matrix.PosSemidef.trace_nonneg (Matrix.nonneg_iff_posSemidef.mp ?_)
  simpa [hF, Matrix.mul_assoc] using
    star_left_conjugate_nonneg hx (NormedSpace.exp ((β / 2) • K))

variable [Nonempty m]

/-- For a Hermitian matrix `K` the Gibbs weight `exp (β • K)` has positive trace. -/
theorem trace_exp_smul_pos (hK : K.IsHermitian) (β : ℝ) :
    0 < (NormedSpace.exp (β • K)).trace := by
  have h := Matrix.PosDef.conjTranspose_mul_self (NormedSpace.exp ((β / 2) • K))
    (Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_exp _))
  rw [(exp_smul hK _).eq, ← Matrix.exp_add_smul, add_halves] at h
  exact h.trace_pos

end IsHermitian

end Matrix
