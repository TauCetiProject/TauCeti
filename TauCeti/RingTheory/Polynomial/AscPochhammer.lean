/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Shifted ascending Pochhammer polynomials

Evaluating the Taylor shift `Polynomial.taylor (m + 1) (ascPochhammer R d)` at `n` and multiplying
by `(n + m)!` yields `(n + m + d)!` over any semiring `R`.

## Main results

* `TauCeti.factorial_mul_eval_taylor_ascPochhammer`: the shifted rising-factorial identity.
-/

public section

namespace TauCeti

/-- Evaluating `Polynomial.taylor (m + 1) (ascPochhammer R d)` at `n` and multiplying by `(n + m)!`
yields `(n + m + d)!` over any semiring `R`. -/
theorem factorial_mul_eval_taylor_ascPochhammer (R : Type*) [Semiring R] (n m d : ℕ) :
    ((n + m).factorial : R) *
      (Polynomial.taylor ((m + 1 : ℕ) : R) (ascPochhammer R d)).eval (n : R) =
      ((n + m + d).factorial : R) := by
  have hnat : (n + m).factorial *
      (Polynomial.taylor (m + 1) (ascPochhammer ℕ d)).eval n = (n + m + d).factorial := by
    rw [Polynomial.taylor_eval]
    simpa only [Nat.cast_id, add_assoc] using factorial_mul_ascPochhammer ℕ (n + m) d
  have hcast := congrArg (Nat.castRingHom R) hnat
  have hmap : Polynomial.map (Nat.castRingHom R) (Polynomial.taylor (m + 1) (ascPochhammer ℕ d)) =
      Polynomial.taylor ((m + 1 : ℕ) : R) (ascPochhammer R d) := by
    rw [Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.map_comp, ascPochhammer_map,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
    rfl
  rw [map_mul, ← Polynomial.eval_map_apply, hmap] at hcast
  simpa only [map_natCast, eq_natCast] using hcast

end TauCeti
