/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The substitutions `t ↦ t / (1 - t)` and `t ↦ t / (1 + t)`

The power series `t / (1 - t) = t + t² + ⋯` and `t / (1 + t) = t - t² + ⋯` are written
`X * mk 1` and `X * mk fun n => (-1) ^ n`. Both have zero constant coefficient, so they can be
substituted into any power series, and the two substitutions are mutually inverse. The powers of
`t / (1 - t)` have binomial coefficients: `[tⁿ⁺¹] (t / (1 - t)) ^ (j + 1) = (n choose j)`.

These substitutions relate the λ-operations and the γ-operations of a pre-λ structure.

## Main results

* `PowerSeries.coeff_succ_X_mul_mk_one_pow_succ`: the coefficients of the powers of `t / (1 - t)`.
* `PowerSeries.X_mul_mk_one_subst_X_mul_mk_neg_one_pow`: `(t / (1 - t)) ∘ (t / (1 + t)) = t`.
* `PowerSeries.X_mul_mk_neg_one_pow_subst_X_mul_mk_one`: `(t / (1 + t)) ∘ (t / (1 - t)) = t`.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The series `t / (1 - t) = X * mk 1` can be substituted into any power series. -/
theorem hasSubst_X_mul_mk_one : HasSubst (X * mk 1 : R⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (by simp)

/-- The series `t / (1 + t) = X * mk fun n => (-1) ^ n` can be substituted into any power
series. -/
theorem hasSubst_X_mul_mk_neg_one_pow : HasSubst (X * mk fun n => (-1 : R) ^ n : R⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (by simp)

/-- The coefficients of the powers of `t / (1 - t) = t + t² + ⋯`:
`[tⁿ⁺¹] (t / (1 - t)) ^ (j + 1) = (n choose j)`. -/
theorem coeff_succ_X_mul_mk_one_pow_succ (n j : ℕ) :
    coeff (n + 1) ((X * mk 1 : R⟦X⟧) ^ (j + 1)) = n.choose j := by
  rw [mul_pow, mk_one_pow_eq_mk_choose_add, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_mk, show j + (n + 1 - (j + 1)) = n by omega]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

/-- The substitution `t ↦ t / (1 + t)` undoes `t ↦ t / (1 - t)`:
`(t / (1 - t)) ∘ (t / (1 + t)) = t`. -/
theorem X_mul_mk_one_subst_X_mul_mk_neg_one_pow :
    (X * mk 1 : R⟦X⟧).subst (X * mk fun n => (-1 : R) ^ n : R⟦X⟧) = X := by
  set a : R⟦X⟧ := X * mk fun n => (-1 : R) ^ n
  have ha : HasSubst a := hasSubst_X_mul_mk_neg_one_pow
  -- the image `u` of `1 / (1 - t)` satisfies `u (1 - a) = 1`, where `1 - a = 1 / (1 + t)`
  have hu := congrArg (fun f : R⟦X⟧ => f.subst a) (mk_one_mul_one_sub_eq_one R)
  rw [subst_mul ha, subst_sub ha, subst_X ha, subst_one] at hu
  have hm := mk_neg_one_pow_mul_one_add_eq_one R
  rw [subst_mul ha, subst_X ha]
  -- with `m = mk fun n => (-1) ^ n`, so that `a = t m`:
  -- `a u - t = t u (m (1 + t) - 1) + t (u (1 - a) - 1)`
  linear_combination (X : R⟦X⟧) * (mk 1 : R⟦X⟧).subst a * hm + X * hu

/-- The substitution `t ↦ t / (1 - t)` undoes `t ↦ t / (1 + t)`:
`(t / (1 + t)) ∘ (t / (1 - t)) = t`. -/
theorem X_mul_mk_neg_one_pow_subst_X_mul_mk_one :
    (X * mk fun n => (-1 : R) ^ n : R⟦X⟧).subst (X * mk 1 : R⟦X⟧) = X := by
  set a : R⟦X⟧ := X * mk 1
  have ha : HasSubst a := hasSubst_X_mul_mk_one
  -- the image `v` of `1 / (1 + t)` satisfies `v (1 + a) = 1`, where `1 + a = 1 / (1 - t)`
  have hv := congrArg (fun f : R⟦X⟧ => f.subst a) (mk_neg_one_pow_mul_one_add_eq_one R)
  rw [subst_mul ha, subst_add ha, subst_X ha, subst_one] at hv
  have hm := mk_one_mul_one_sub_eq_one R
  rw [subst_mul ha, subst_X ha]
  -- with `g = mk 1`, so that `a = t g`:
  -- `a v - t = t v (g (1 - t) - 1) + t (v (1 + a) - 1)`
  linear_combination (X : R⟦X⟧) * (mk fun n => (-1 : R) ^ n : R⟦X⟧).subst a * hm + X * hv

end PowerSeries
