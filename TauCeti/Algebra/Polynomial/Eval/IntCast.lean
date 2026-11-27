/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Polynomial evaluation at integer casts and finite differences

This file records general facts about evaluating univariate polynomials at integer casts over an
arbitrary (possibly noncommutative) ring `R`:

* Because integer casts are central, evaluating a composition `p.comp q` at `(d : R)` equals
  `p.eval (q.eval (d : R))` (`Polynomial.eval_comp_intCast`).
* Over any semiring `R`, the `k`-th coefficient of the forward shift `p.comp (X + 1)` expands as
  `∑ i < m, p.coeff i * (i.choose k : R)` whenever `p.natDegree < m`
  (`Polynomial.coeff_comp_X_add_one`).
* Over any ring `R` with unique additive division (`HasUniqueDiv R`), two polynomials agreeing at
  all integers from some bound `N` onward are equal (`Polynomial.eq_of_forall_ge_intCast_eval_eq`).
  The proof takes repeated forward differences `D(X + 1) - D(X)`, whose top coefficient is
  `(n + 1) • D.coeff (n + 1)`.

## Main results

* `Polynomial.eval_comp_intCast`: `(p.comp q).eval (d : R) = p.eval (q.eval (d : R))` over any
  ring `R`.
* `Polynomial.coeff_comp_X_add_one`: coefficient formula for `p.comp (X + 1)` over any semiring
  `R`.
* `Polynomial.eq_of_forall_ge_intCast_eval_eq`: polynomials over a `HasUniqueDiv` ring agreeing on
  all sufficiently large integers are equal.
-/

public section

namespace Polynomial

/-- Evaluating `p.comp q` at an integer cast `(d : R)` equals `p.eval (q.eval (d : R))` over any
ring `R` (not necessarily commutative), because integer casts are central. -/
theorem eval_comp_intCast {R : Type*} [Ring R] (p q : R[X]) (d : ℤ) :
    (p.comp q).eval (d : R) = p.eval (q.eval (d : R)) := by
  have hmul (u v : R[X]) : (u * v).eval (d : R) = u.eval (d : R) * v.eval (d : R) :=
    eval₂_mul_noncomm (RingHom.id R) (d : R) fun _ ↦ (Int.cast_commute d _).symm
  have hpow (m : ℕ) : (q ^ m).eval (d : R) = (q.eval (d : R)) ^ m := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, hmul, ih, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ => simp [add_comp, h₁, h₂]
  | monomial k r => rw [monomial_comp, eval_C_mul, hpow, eval_monomial]

/-- Coefficient formula for `p.comp (X + 1)` over any semiring `R`. -/
theorem coeff_comp_X_add_one {R : Type*} [Semiring R] (p : R[X]) (m k : ℕ)
    (hm : p.natDegree < m) :
    (p.comp (X + 1)).coeff k = ∑ i ∈ Finset.range m, p.coeff i * (i.choose k : R) := by
  conv_lhs => rw [as_sum_range' p m hm]
  rw [sum_comp, finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [monomial_comp, coeff_C_mul, coeff_X_add_one_pow]

/-- Two polynomials over a ring with unique additive division (`HasUniqueDiv`) that agree on every
integer greater than or equal to some bound `N` are equal. -/
theorem eq_of_forall_ge_intCast_eval_eq {R : Type*} [Ring R] [HasUniqueDiv R]
    {P Q : R[X]} {N : ℤ} (h : ∀ d : ℤ, N ≤ d → P.eval (d : R) = Q.eval (d : R)) : P = Q := by
  suffices hzero : ∀ (n : ℕ) (D : R[X]), D.natDegree ≤ n →
      (∀ d : ℤ, N ≤ d → D.eval (d : R) = 0) → D = 0 from
    sub_eq_zero.mp (hzero (P - Q).natDegree (P - Q) le_rfl fun d hd ↦ by
      rw [eval_sub, h d hd, sub_self])
  intro n
  induction n with
  | zero =>
    intro D hdeg hD
    rw [eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hdeg)] at hD ⊢
    simpa using hD N le_rfl
  | succ n ih =>
    intro D hdeg hD
    let Δ : R[X] := D.comp (X + 1) - D
    have hΔ_eval (d : ℤ) (hd : N ≤ d) : Δ.eval (d : R) = 0 := by
      rw [eval_sub, eval_comp_intCast, eval_add, eval_X, eval_one, ← Int.cast_one,
        ← Int.cast_add, hD (d + 1) (by omega), hD d hd, sub_self]
    have hΔ_deg : Δ.natDegree ≤ n := natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ by
      rw [coeff_sub, coeff_comp_X_add_one D (n + 2) k (by omega)]
      by_cases hkn : k = n + 1
      · subst hkn
        rw [Finset.sum_eq_single (n + 1)
          (fun i hi hne ↦ by
            rw [Nat.choose_eq_zero_of_lt (by have := Finset.mem_range.mp hi; omega),
              Nat.cast_zero, mul_zero])
          (fun hnot ↦ absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) hnot)]
        simp
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
        exact Finset.sum_eq_zero fun i hi ↦ by
          rw [Nat.choose_eq_zero_of_lt (by have := Finset.mem_range.mp hi; omega),
            Nat.cast_zero, mul_zero]
    have hΔ_zero : Δ = 0 := ih Δ hΔ_deg hΔ_eval
    have hlead : D.coeff (n + 1) = 0 := by
      have hcomp : (D.comp (X + 1)).coeff n = D.coeff n + (n + 1) • D.coeff (n + 1) := by
        rw [coeff_comp_X_add_one D (n + 2) n (by omega), Finset.sum_range_succ,
          Finset.sum_range_succ]
        have hlt : ∑ i ∈ Finset.range n, D.coeff i * (i.choose n : R) = 0 :=
          Finset.sum_eq_zero fun i hi ↦ by
            simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]
        rw [hlt, zero_add, Nat.choose_self, Nat.cast_one, mul_one,
          Nat.choose_succ_self_right, nsmul_eq_mul']
      have h0 : Δ.coeff n = (n + 1) • D.coeff (n + 1) := by
        rw [coeff_sub, hcomp, add_sub_cancel_left]
      exact HasUniqueDiv.nsmul_right_injective (Nat.succ_ne_zero n)
        (by dsimp only; rw [nsmul_zero, ← h0, hΔ_zero, coeff_zero])
    exact ih D (natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ by
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hk) with rfl | hgt
      · exact hlead
      · exact coeff_eq_zero_of_natDegree_lt (by omega)) hD

end Polynomial
