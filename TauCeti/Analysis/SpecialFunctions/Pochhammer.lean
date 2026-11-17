/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Norm bounds for Pochhammer polynomials

This file complements `Mathlib.Analysis.SpecialFunctions.Pochhammer` with norm bounds for the
evaluated ascending Pochhammer polynomial `(ascPochhammer R n).eval x = x (x + 1) ⋯ (x + n - 1)`
in a seminormed ring satisfying `‖(1 : R)‖ = 1`.

## Main results

* `TauCeti.norm_ascPochhammer_eval_le_of_norm_le`: if `‖x‖ ≤ r`, then
  `‖(ascPochhammer R n).eval x‖ ≤ (ascPochhammer ℝ n).eval r`.
* `TauCeti.norm_ascPochhammer_eval_le`:
  `‖(ascPochhammer R n).eval x‖ ≤ (ascPochhammer ℝ n).eval ‖x‖`.
* `TauCeti.norm_ascPochhammer_eval_le_ascFactorial`: if `‖x‖ ≤ M` for `M : ℕ`, then
  `‖(ascPochhammer R n).eval x‖ ≤ M.ascFactorial n`.
-/

public section

namespace TauCeti

/-- If `‖x‖ ≤ r` in a seminormed ring with `‖1‖ = 1`, then the evaluated ascending Pochhammer
polynomial `(x)ₙ = x (x + 1) ⋯ (x + n - 1)` has norm at most `(r)ₙ`. -/
theorem norm_ascPochhammer_eval_le_of_norm_le {R : Type*} [SeminormedRing R] [NormOneClass R]
    (n : ℕ) {x : R} {r : ℝ} (hx : ‖x‖ ≤ r) :
    ‖(ascPochhammer R n).eval x‖ ≤ (ascPochhammer ℝ n).eval r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    exact (norm_mul_le _ _).trans <|
      mul_le_mul ih
        ((norm_add_le x (n : R)).trans
          (add_le_add hx (by simpa using Nat.norm_cast_le (α := R) n)))
        (norm_nonneg _) ((norm_nonneg _).trans ih)

/-- In a seminormed ring with `‖1‖ = 1`, the norm of the evaluated ascending Pochhammer
polynomial `(x)ₙ = x (x + 1) ⋯ (x + n - 1)` is bounded by `(‖x‖)ₙ`. -/
theorem norm_ascPochhammer_eval_le {R : Type*} [SeminormedRing R] [NormOneClass R]
    (n : ℕ) (x : R) :
    ‖(ascPochhammer R n).eval x‖ ≤ (ascPochhammer ℝ n).eval ‖x‖ :=
  norm_ascPochhammer_eval_le_of_norm_le n le_rfl

/-- If `‖x‖ ≤ M` for a natural number `M` in a seminormed ring with `‖1‖ = 1`, then the evaluated
ascending Pochhammer polynomial `(x)ₙ` has norm at most the rising factorial `M.ascFactorial n`. -/
theorem norm_ascPochhammer_eval_le_ascFactorial {R : Type*} [SeminormedRing R] [NormOneClass R]
    (n : ℕ) {x : R} {M : ℕ} (hx : ‖x‖ ≤ M) :
    ‖(ascPochhammer R n).eval x‖ ≤ M.ascFactorial n :=
  (norm_ascPochhammer_eval_le_of_norm_le n hx).trans_eq
    (ascPochhammer_nat_eq_natCast_ascFactorial ℝ M n)

end TauCeti
