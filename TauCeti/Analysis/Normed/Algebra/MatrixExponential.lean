/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.Analysis.Calculus.FDeriv.Det

/-!
# The determinant of a matrix exponential

For a square matrix `A` over `ℝ` or `ℂ` (any `RCLike` field),

`det (exp A) = exp (trace A)`.

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

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Chapter 2, where the identity is proved by triangularizing `A`; the differential argument used
  here avoids any normal form.
-/

public section

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

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
