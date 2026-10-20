/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Finite evaluation of power series at nilpotent elements

Substitution at a nilpotent series depends on only finitely many coefficients. In particular,
substitution at a nilpotent constant is the constant series given by finite polynomial
evaluation. This connects formal identities with polynomial maps on nilpotent elements.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Substituting a series whose `n`th power vanishes uses only the coefficients below `n`. -/
theorem subst_eq_aeval_trunc_of_pow_eq_zero {a : R⟦X⟧} {n : ℕ}
    (hn : a ^ n = 0) (f : R⟦X⟧) :
    f.subst a = Polynomial.aeval a (trunc n f) := by
  have ha : HasSubst a := ⟨n, by rw [← map_pow, hn, map_zero]⟩
  conv_lhs => rw [eq_X_pow_mul_shift_add_trunc n f]
  rw [subst_add ha, subst_mul ha, subst_pow ha, subst_X ha, hn, zero_mul, zero_add,
    subst_coe ha]

/-- A nilpotent constant substitutes by evaluating a finite truncation. -/
theorem subst_C_eq_C_eval_trunc {x : R} {n : ℕ} (hn : x ^ n = 0) (f : R⟦X⟧) :
    f.subst (C x) = C ((trunc n f).eval x) := by
  rw [subst_eq_aeval_trunc_of_pow_eq_zero (n := n) (by rw [← map_pow, hn, map_zero])]
  simp [Polynomial.aeval_def]

end PowerSeries
