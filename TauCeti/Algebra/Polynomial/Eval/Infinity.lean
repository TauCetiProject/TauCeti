/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Basic.Sign.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith

/-! # Polynomial signs at infinity over an ordered field

A coefficient bound makes the leading term dominate all lower terms.
The bound belongs to the field itself; no Archimedean assumption is used.
-/

public section

namespace Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Beyond a field-valued coefficient bound, a polynomial has the sign
of its leading coefficient. -/
theorem exists_sign_atTop (p : R[X]) : ∃ B : R, ∀ x, B < x →
    SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  classical
  by_cases hn : p.natDegree = 0
  · refine ⟨0, fun x _ => ?_⟩
    rw [eq_C_of_natDegree_eq_zero hn]
    simp
  have hdegree : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hn
  have hp : p ≠ 0 := fun h => hn (by simp [h])
  have hlc : 0 < |p.leadingCoeff| := abs_pos.mpr (leadingCoeff_ne_zero.mpr hp)
  let S := ∑ i ∈ Finset.range p.natDegree, |p.coeff i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg (p.coeff i)
  refine ⟨1 + S / |p.leadingCoeff|, fun x hx => ?_⟩
  have hx1 : 1 < x := lt_of_le_of_lt
    (le_add_of_nonneg_right (div_nonneg hS hlc.le)) hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hdom : S < |p.leadingCoeff| * x := by
    rw [mul_comm]
    apply (div_lt_iff₀ hlc).mp
    linarith
  let t := ∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i
  have ht : |t| ≤ S * x ^ (p.natDegree - 1) := by
    calc
      |t| ≤ ∑ i ∈ Finset.range p.natDegree, |p.coeff i * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range p.natDegree, |p.coeff i| * x ^ (p.natDegree - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_pow, abs_of_pos hx0]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hx1.le (by simpa using Nat.le_pred_of_lt (Finset.mem_range.mp hi)))
          (abs_nonneg _)
      _ = S * x ^ (p.natDegree - 1) := (Finset.sum_mul _ _ _).symm
  have hsmall : |t| < |p.leadingCoeff| * x ^ p.natDegree := by
    have h := mul_lt_mul_of_pos_right hdom (pow_pos hx0 (p.natDegree - 1))
    rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hdegree] at h
    exact ht.trans_lt h
  have heval : p.eval x = t + p.leadingCoeff * x ^ p.natDegree := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, coeff_natDegree]
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp) with hneg | hpos
  · rw [abs_of_neg hneg] at hsmall
    rw [sign_neg hneg, heval]
    apply sign_neg
    have := le_abs_self t
    nlinarith
  · rw [abs_of_pos hpos] at hsmall
    rw [sign_pos hpos, heval]
    apply sign_pos
    have := neg_abs_le t
    nlinarith

/-- Below some field-valued bound, the sign gains the degree-parity factor. -/
theorem exists_sign_atBot (p : R[X]) : ∃ B : R, ∀ x, x < B →
    SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree) := by
  obtain ⟨B, hB⟩ := exists_sign_atTop (p.comp (-X))
  refine ⟨-B, fun x hx => ?_⟩
  have hs := hB (-x) (by linarith)
  simpa only [eval_comp, eval_neg, eval_X, neg_neg,
    leadingCoeff_comp (by simp : (-X : R[X]).natDegree ≠ 0),
    leadingCoeff_neg, leadingCoeff_X] using hs

end Polynomial

namespace List

open Polynomial Filter

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A uniform right bound for the leading-coefficient signs of a polynomial list. -/
theorem exists_signs_atTop (cs : List (Polynomial R)) : ∃ B : R,
    ∀ p ∈ cs, ∀ x, B < x → SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  have he : ∀ᶠ x in atTop, ∀ p ∈ cs,
      SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
    apply cs.finite_toSet.eventually_all.mpr
    intro p _
    obtain ⟨B, hB⟩ := exists_sign_atTop p
    exact (eventually_gt_atTop B).mono fun x hx => hB x hx
  obtain ⟨B, hB⟩ := eventually_atTop.mp he
  exact ⟨B, fun p hp x hx => hB x hx.le p hp⟩

/-- A uniform left bound for the degree-parity signs of a polynomial list. -/
theorem exists_signs_atBot (cs : List (Polynomial R)) : ∃ B : R,
    ∀ p ∈ cs, ∀ x, x < B →
      SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree) := by
  have he : ∀ᶠ x in atBot, ∀ p ∈ cs,
      SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree) := by
    apply cs.finite_toSet.eventually_all.mpr
    intro p _
    obtain ⟨B, hB⟩ := exists_sign_atBot p
    exact (eventually_lt_atBot B).mono fun x hx => hB x hx
  obtain ⟨B, hB⟩ := eventually_atBot.mp he
  exact ⟨B, fun p hp x hx => hB x hx.le p hp⟩

end List
