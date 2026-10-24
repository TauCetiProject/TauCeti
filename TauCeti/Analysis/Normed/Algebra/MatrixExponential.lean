/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.Analysis.Calculus.FDeriv.Det

/-!
# The matrix exponential

For a square matrix `A` over `ℝ` or `ℂ` (any `RCLike` field),

`det (exp A) = exp (trace A)`.

The file also records the exponential identities that are specific to matrices: the reciprocal
laws `exp A * exp (-A) = 1` and `exp (-A) * exp A = 1` for an arbitrary matrix over commutative
entries, together with their forms against an arbitrary factor, invariance of the trace under
conjugation by the two exponential weights in either order, the half-split identity
`exp A = exp (A / 2) * exp (A / 2)`, and, for a Hermitian matrix `K`, the positivity of
`Tr (exp K)` and of `x ↦ Tr (exp K * x)`.

This is listed as a TODO in Mathlib's `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`.
No diagonalization is involved, so the identity holds for every matrix, including the real
matrices that are not diagonalizable over `ℂ` either.

## The argument

The function `f t = det (exp (t • A))` is a homomorphism from the additive group of the field to
its multiplicative monoid, because the exponentials of the commuting matrices `s • A` and `t • A`
multiply. Its derivative at `0` is `trace A`: the curve `t ↦ exp (t • A)` leaves the identity with
velocity `A`, and the derivative of the determinant at the identity is the trace
(`Matrix.hasFDerivAt_det_one`). The homomorphism property transports this to every point, so
`f' = trace A • f`, and then `t ↦ f t * exp (-t • trace A)` has vanishing derivative and is the
constant `1`. Evaluating at `t = 1` gives the identity.

## Main results

* `Matrix.det_exp`: `det (exp A) = exp (trace A)`.
* `Matrix.exp_mul_exp_neg`, `Matrix.exp_neg_mul_exp`, `Matrix.exp_mul_exp_neg_mul`,
  `Matrix.exp_neg_mul_exp_mul`: the reciprocal laws for the exponential of an arbitrary matrix,
  in both orientations.
* `Matrix.trace_exp_neg_mul_mul_exp`, `Matrix.trace_exp_mul_mul_exp_neg`: conjugating by the two
  exponential weights preserves the trace, in both orientations.
* `Matrix.exp_eq_mul_exp_half`: the exponential of a matrix is the square of its half.
* `Matrix.IsHermitian.trace_exp_mul_nonneg` and `Matrix.IsHermitian.trace_exp_pos`: positivity of
  the trace of the exponential of a Hermitian matrix and of the functional `x ↦ Tr (exp K * x)`.

## References

* Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
  Section 5.3.1, for the exponential of a Hamiltonian as an unnormalised Gibbs weight.
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Chapter 2, where the identity is proved by triangularizing `A`; the differential argument used
  here avoids any normal form.
-/

public section

open NormedSpace
open scoped ComplexOrder Matrix Matrix.Norms.Operator MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕂 : Type*} [RCLike 𝕂]

/-- **The determinant of the exponential of a matrix is the exponential of its trace.** -/
theorem det_exp (A : Matrix n n 𝕂) : det (exp A) = exp (trace A) := by
  set f : 𝕂 → 𝕂 := fun t => det (exp (t • A)) with hf_def
  have hmul (s t : 𝕂) : f (s + t) = f s * f t := by
    have h : exp ((s + t) • A) = exp (s • A) * exp (t • A) := by
      rw [add_smul]
      exact exp_add_of_commute _ _ (((Commute.refl A).smul_left s).smul_right t)
    simp only [hf_def, h, det_mul]
  have hf0 : HasDerivAt f (trace A) 0 := by
    have hexp := hasDerivAt_exp_smul_const (𝕂 := 𝕂) A 0
    simp only [zero_smul, exp_zero, one_mul] at hexp
    exact hasFDerivAt_det_one.comp_hasDerivAt_of_eq (0 : 𝕂) hexp (by simp)
  have hf (t : 𝕂) : HasDerivAt f (f t * trace A) t := by
    have hshift : f = fun s => f t * f (s - t) := by
      funext s
      rw [← hmul, add_sub_cancel]
    have hcomp := (hf0.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)).const_mul (f t)
    simp only [Function.comp_def, id, mul_one] at hcomp
    rwa [← hshift] at hcomp
  set g : 𝕂 → 𝕂 := fun t => f t * exp (t • -trace A) with hg_def
  have hg (t : 𝕂) : HasDerivAt g 0 t := by
    have h := (hf t).mul (hasDerivAt_exp_smul_const (𝕂 := 𝕂) (-trace A) t)
    convert h using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt)
    (fun t => (hg t).deriv) 1 0
  simp only [hg_def, hf_def, one_smul, zero_smul, exp_zero, det_one, mul_one] at hconst
  calc det (exp A) = det (exp A) * (exp (-trace A) * exp (trace A)) := by
        rw [← NormedSpace.exp_add_of_commute ((Commute.refl _).neg_left), neg_add_cancel,
          exp_zero, mul_one]
    _ = exp (trace A) := by rw [← mul_assoc, hconst, one_mul]

end Matrix

/-! ### Exponential identities for matrices

These are the matrix restatements used by the Gibbs-state development. The reciprocal laws hold
for an arbitrary matrix over a normed entry ring, not only for scalar multiples, and the trace
identities likewise over a commutative entry ring. Each law is stated in both orientations, so the
`@[simp]` set cancels the two exponential weights wherever `simp`'s normal form puts them. The half
split and the Hermitian results need an `RCLike` field, and the positivity statements use the order
on the entries.
-/

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The exponential of a matrix is the square of the exponential of its half,
`exp A = exp (A / 2) * exp (A / 2)`. -/
theorem exp_eq_mul_exp_half {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m m 𝕜) :
    NormedSpace.exp A =
      NormedSpace.exp ((1 / 2 : ℝ) • A) * NormedSpace.exp ((1 / 2 : ℝ) • A) := by
  conv_lhs => rw [← one_smul ℝ A, ← add_halves (1 : ℝ), add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left _).smul_right _)

section Ring

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- The exponential weights of an arbitrary matrix are mutually inverse. -/
@[simp]
theorem exp_mul_exp_neg (A : Matrix m m 𝔸) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  simpa using (Matrix.exp_add_of_commute (A := A) (B := -A) (Commute.refl A).neg_right).symm

/-- The exponential weights of an arbitrary matrix are mutually inverse. -/
@[simp]
theorem exp_neg_mul_exp (A : Matrix m m 𝔸) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  simpa using (Matrix.exp_add_of_commute (A := -A) (B := A) (Commute.refl A).neg_left).symm

/-- The exponential of a negative matrix cancels against an arbitrary factor. -/
@[simp]
theorem exp_mul_exp_neg_mul (A x : Matrix m m 𝔸) :
    NormedSpace.exp A * (NormedSpace.exp (-A) * x) = x := by
  rw [← Matrix.mul_assoc, exp_mul_exp_neg, Matrix.one_mul]

/-- The exponential of a matrix cancels against an arbitrary factor on the other side. -/
@[simp]
theorem exp_neg_mul_exp_mul (A x : Matrix m m 𝔸) :
    NormedSpace.exp (-A) * (NormedSpace.exp A * x) = x := by
  rw [← Matrix.mul_assoc, exp_neg_mul_exp, Matrix.one_mul]

end Ring

section CommutativeEntries

variable {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- Conjugating by the two exponential weights preserves the trace. -/
@[simp]
theorem trace_exp_neg_mul_mul_exp (A x : Matrix m m 𝔸) :
    (NormedSpace.exp (-A) * x * NormedSpace.exp A).trace = x.trace := by
  rw [Matrix.trace_mul_comm (NormedSpace.exp (-A) * x) (NormedSpace.exp A),
    exp_mul_exp_neg_mul]

/-- Conjugating by the two exponential weights, in the other order, preserves the trace. -/
@[simp]
theorem trace_exp_mul_mul_exp_neg (A x : Matrix m m 𝔸) :
    (NormedSpace.exp A * x * NormedSpace.exp (-A)).trace = x.trace := by
  rw [Matrix.trace_mul_comm (NormedSpace.exp A * x) (NormedSpace.exp (-A)), exp_neg_mul_exp_mul]

end CommutativeEntries

namespace IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {K : Matrix m m 𝕜}

/-- For a Hermitian matrix `K`, the functional `x ↦ Tr (exp K * x)` is positive. -/
theorem trace_exp_mul_nonneg (hK : K.IsHermitian) {x : Matrix m m 𝕜}
    (hx : 0 ≤ x) : 0 ≤ (NormedSpace.exp K * x).trace := by
  have hP : (NormedSpace.exp ((1 / 2 : ℝ) • K)).IsHermitian :=
    (hK.smul (IsSelfAdjoint.all (1 / 2 : ℝ))).exp
  have hF : star (NormedSpace.exp ((1 / 2 : ℝ) • K)) = NormedSpace.exp ((1 / 2 : ℝ) • K) :=
    hP.eq
  rw [exp_eq_mul_exp_half K, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  refine Matrix.PosSemidef.trace_nonneg (Matrix.nonneg_iff_posSemidef.mp ?_)
  simpa only [hF, Matrix.mul_assoc] using
    star_left_conjugate_nonneg hx (NormedSpace.exp ((1 / 2 : ℝ) • K))

variable [Nonempty m]

/-- For a Hermitian matrix `K` the exponential `exp K` has positive trace. -/
theorem trace_exp_pos (hK : K.IsHermitian) :
    0 < (NormedSpace.exp K).trace := by
  have h := Matrix.PosDef.conjTranspose_mul_self (NormedSpace.exp ((1 / 2 : ℝ) • K))
    (Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_exp _))
  rw [(hK.smul (IsSelfAdjoint.all (1 / 2 : ℝ))).exp.eq, ← exp_eq_mul_exp_half K] at h
  exact h.trace_pos

end IsHermitian

end Matrix
