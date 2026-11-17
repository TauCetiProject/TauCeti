/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Norm bounds for Pochhammer polynomials

This module records elementary norm estimates for ascending Pochhammer polynomial evaluations
`(ascPochhammer R n).eval w` in seminormed rings with `‖1‖ = 1`, independent of the Gamma function.

## Main results

* `TauCeti.norm_ascPochhammer_eval_le_factorial`: `‖(w)ₙ‖ ≤ (M + n)!` whenever `‖w‖ ≤ M`.
-/

public section

open scoped Nat

namespace TauCeti

/-- The ascending Pochhammer polynomial evaluation `(w)ₙ` satisfies `‖(w)ₙ‖ ≤ (M + n)!` whenever
`‖w‖ ≤ M` in a seminormed ring with `‖1‖ = 1`. -/
theorem norm_ascPochhammer_eval_le_factorial {R : Type*} [SeminormedRing R] [NormOneClass R]
    {w : R} {M : ℕ} (hw : ‖w‖ ≤ M) (n : ℕ) :
    ‖(ascPochhammer R n).eval w‖ ≤ ((M + n)! : ℝ) := by
  induction n with
  | zero => simp [Nat.one_le_iff_ne_zero, Nat.factorial_ne_zero]
  | succ n ih =>
    have hwn : ‖w + n‖ ≤ (M + n + 1 : ℝ) :=
      (norm_add_le w n).trans <| by
        have hn : ‖(n : R)‖ ≤ n := by simpa using Nat.norm_cast_le (α := R) n
        linarith
    rw [ascPochhammer_succ_eval]
    refine (norm_mul_le _ _).trans ?_
    refine (mul_le_mul ih hwn (norm_nonneg _) (by positivity)).trans_eq ?_
    rw [← add_assoc, Nat.factorial_succ]
    push_cast
    ring

end TauCeti
