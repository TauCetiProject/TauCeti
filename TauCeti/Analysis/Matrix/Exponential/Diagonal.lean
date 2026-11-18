/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Diagonal
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Real diagonal matrices in the image of the exponential

A real diagonal matrix with pairwise distinct entries can be an exponential only if every
entry is positive.
The distinctness assumption matters: repeated negative entries can have real matrix logarithms.

## Main results

* `Matrix.diag_pos_of_exp_eq_diagonal`: positivity of a diagonal exponential with distinct entries.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, GTM 222
  (2015), Section 2.1, Propositions 2.1 and 2.3, for the matrix exponential.
* Mathlib, `Analysis/Normed/Algebra/MatrixExponential.lean`, for the diagonal exponential.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real diagonal exponential with pairwise distinct entries has strictly positive entries. -/
theorem diag_pos_of_exp_eq_diagonal (A : Matrix n n ℝ) {d : n → ℝ}
    (hd : Function.Injective d) (hA : NormedSpace.exp A = diagonal d) (i : n) : 0 < d i := by
  have hc : Commute (NormedSpace.exp A) A := (Commute.refl A).exp_left
  rw [hA] at hc
  have hdiag := TauCeti.isDiag_of_commute_diagonal hd hc
  have he : NormedSpace.exp (diagonal (diag A)) = diagonal d := by
    rw [hdiag.diagonal_diag]
    exact hA
  rw [exp_diagonal] at he
  have hi := congrArg (fun M : Matrix n n ℝ => M i i) he
  simp only [diagonal_apply_eq, Pi.coe_exp, diag_apply] at hi
  rw [← hi, ← Real.exp_eq_exp_ℝ]
  exact Real.exp_pos (A i i)

end Matrix
