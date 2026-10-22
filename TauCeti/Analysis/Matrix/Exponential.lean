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
# The exponential of a matrix

Over an `RCLike` field `𝕜`, scalar multiples of a fixed matrix commute, so their exponential is
multiplicative, `Matrix.exp_add_smul`, and `exp (β • K)` is the inverse of `exp (-(β • K))`,
`Matrix.exp_smul_mul_exp_neg_smul`, also against an arbitrary factor,
`Matrix.exp_smul_mul_exp_neg_smul_mul`. Conjugating by the two weights does not change the trace,
`Matrix.trace_exp_neg_smul_mul_exp_smul`.

For a Hermitian complex matrix `K`, the exponential `exp (β • K)` of a real multiple is again
Hermitian, `Matrix.IsHermitian.exp_smul`, and has positive trace,
`Matrix.IsHermitian.trace_exp_smul_pos`. Hence `x ↦ Tr (exp (β • K) * x)` is a positive
functional, `Matrix.IsHermitian.trace_exp_smul_mul_nonneg`, the unnormalised Gibbs functional of
a matrix Hamiltonian at inverse temperature `-β`.

## Main declarations

* `Matrix.exp_add_smul`: `exp ((s + t) • K) = exp (s • K) * exp (t • K)`.
* `Matrix.exp_smul_mul_exp_neg_smul`, `Matrix.exp_neg_smul_mul_exp_smul` and
  `Matrix.exp_smul_mul_exp_neg_smul_mul`: the cancellation laws for the exponential weights,
  both as plain products and against an arbitrary factor.
* `Matrix.trace_exp_neg_smul_mul_exp_smul`: conjugating by the exponential weights preserves the
  trace.
* `Matrix.IsHermitian.exp_smul`: `exp (β • K)` is Hermitian for Hermitian `K`.
* `Matrix.IsHermitian.trace_exp_smul_mul_nonneg` and `Matrix.IsHermitian.trace_exp_smul_pos`:
  positivity of the unnormalised Gibbs functional at inverse temperature `-β` and of its
  normalising constant.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Section 5.3.1, for the exponential of a Hamiltonian as an unnormalised Gibbs weight.
-/

public section

noncomputable section

open NormedSpace
open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The exponential of multiples of a fixed matrix is multiplicative:
`exp ((s + t) • K) = exp (s • K) * exp (t • K)`. -/
theorem exp_add_smul (K : Matrix m m 𝕜) (s t : 𝕜) :
    exp ((s + t) • K) = exp (s • K) * exp (t • K) := by
  rw [add_smul, exp_add_of_commute _ _ (((Commute.refl K).smul_left _).smul_right _)]

/-- The exponential weight `exp (β • K)` cancels against `exp (-(β • K))`. -/
@[simp]
theorem exp_smul_mul_exp_neg_smul (K : Matrix m m 𝕜) (β : 𝕜) :
    exp (β • K) * exp (-(β • K)) = 1 := by
  rw [← neg_smul, ← exp_add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]

/-- The exponential weight `exp (-(β • K))` cancels against `exp (β • K)`. -/
@[simp]
theorem exp_neg_smul_mul_exp_smul (K : Matrix m m 𝕜) (β : 𝕜) :
    exp (-(β • K)) * exp (β • K) = 1 := by
  rw [← neg_smul, ← exp_add_smul, neg_add_cancel, zero_smul, NormedSpace.exp_zero]

/-- Cancellation of the exponential weights against an arbitrary factor. -/
@[simp]
theorem exp_smul_mul_exp_neg_smul_mul (K : Matrix m m 𝕜) (β : 𝕜) (x : Matrix m m 𝕜) :
    exp (β • K) * (exp (-(β • K)) * x) = x := by
  rw [← Matrix.mul_assoc, exp_smul_mul_exp_neg_smul, Matrix.one_mul]

/-- Conjugating by the exponential weights preserves the trace. -/
@[simp]
theorem trace_exp_neg_smul_mul_exp_smul (K : Matrix m m 𝕜) (β : 𝕜) (x : Matrix m m 𝕜) :
    (exp (-(β • K)) * x * exp (β • K)).trace = x.trace := by
  rw [Matrix.trace_mul_comm (exp (-(β • K)) * x) (exp (β • K)), exp_smul_mul_exp_neg_smul_mul]

end RCLike

/-- The real-scalar form of `Matrix.exp_add_smul` for complex matrices, used by the Hermitian
lemmas below: `exp (β • K)` is the square of `exp ((β / 2) • K)`. -/
private theorem exp_smul_eq_mul_exp_half (K : Matrix m m ℂ) (β : ℝ) :
    NormedSpace.exp (β • K) =
      NormedSpace.exp ((β / 2) • K) * NormedSpace.exp ((β / 2) • K) := by
  conv_lhs => rw [← add_halves β, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl K).smul_left _).smul_right _)

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
  rw [exp_smul_eq_mul_exp_half K β, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  refine Matrix.PosSemidef.trace_nonneg (Matrix.nonneg_iff_posSemidef.mp ?_)
  simpa [hF, Matrix.mul_assoc] using
    star_left_conjugate_nonneg hx (NormedSpace.exp ((β / 2) • K))

variable [Nonempty m]

/-- For a Hermitian matrix `K` the exponential `exp (β • K)`, the Gibbs weight at inverse
temperature `-β`, has positive trace. -/
theorem trace_exp_smul_pos (hK : K.IsHermitian) (β : ℝ) :
    0 < (NormedSpace.exp (β • K)).trace := by
  have h := Matrix.PosDef.conjTranspose_mul_self (NormedSpace.exp ((β / 2) • K))
    (Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_exp _))
  rw [(exp_smul hK _).eq, ← exp_smul_eq_mul_exp_half K β] at h
  exact h.trace_pos

end IsHermitian

end Matrix
