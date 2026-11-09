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

Over a linearly ordered field, a polynomial eventually has the sign of its leading coefficient
to the right, and the sign of `leadingCoeff * (-1) ^ natDegree` to the left. The bounds are
elements of the field itself, so no Archimedean or topological assumption is needed. The `List`
versions give a single bound working for every polynomial in a list, as needed for sign
variations of Sturm chains at infinity.
-/

public section

namespace Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Beyond some bound in the field, a polynomial has the sign of its leading coefficient. -/
theorem exists_sign_atTop (p : R[X]) : ∃ B : R, ∀ x, B < x →
    SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  rcases eq_or_ne p.natDegree 0 with hn | hn
  · exact ⟨0, fun x _ => by rw [eq_C_of_natDegree_eq_zero hn]; simp⟩
  have hlc : p.leadingCoeff ≠ 0 := by simpa using ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero hn)
  let S := ∑ i ∈ Finset.range p.natDegree, |p.coeff i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg (p.coeff i)
  refine ⟨1 + S / |p.leadingCoeff|, fun x hx => ?_⟩
  have hx1 : 1 < x := by have := div_nonneg hS (abs_nonneg p.leadingCoeff); linarith
  have hdom : S < |p.leadingCoeff| * x := by
    rw [mul_comm, ← div_lt_iff₀ (abs_pos.mpr hlc)]
    linarith
  -- The lower-order terms are dominated by the leading term.
  have ht : |∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i| <
      |p.leadingCoeff| * x ^ p.natDegree :=
    calc _ ≤ ∑ i ∈ Finset.range p.natDegree, |p.coeff i| * x ^ (p.natDegree - 1) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
          rw [abs_mul, abs_pow, abs_of_pos (zero_lt_one.trans hx1)]
          gcongr
          · exact hx1.le
          · exact Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)
      _ = S * x ^ (p.natDegree - 1) := (Finset.sum_mul _ _ _).symm
      _ < |p.leadingCoeff| * x * x ^ (p.natDegree - 1) := by gcongr
      _ = |p.leadingCoeff| * x ^ p.natDegree := by
          rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
  rw [eval_eq_sum_range, Finset.sum_range_succ, coeff_natDegree]
  have := abs_lt.mp ht
  rcases hlc.lt_or_gt with hneg | hpos
  · rw [abs_of_neg hneg] at this
    rw [sign_neg hneg, sign_neg (by linarith)]
  · rw [abs_of_pos hpos] at this
    rw [sign_pos hpos, sign_pos (by linarith)]

/-- Below some bound in the field, a polynomial has the sign of
`leadingCoeff * (-1) ^ natDegree`. -/
theorem exists_sign_atBot (p : R[X]) : ∃ B : R, ∀ x, x < B →
    SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree) := by
  obtain ⟨B, hB⟩ := exists_sign_atTop (p.comp (-X))
  refine ⟨-B, fun x hx => ?_⟩
  simpa [leadingCoeff_comp (by simp : (-X : R[X]).natDegree ≠ 0)] using hB (-x) (by linarith)

end Polynomial

namespace List

open Polynomial Filter

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A single bound beyond which every polynomial in a list has the sign of its leading
coefficient. -/
theorem exists_signs_atTop (cs : List R[X]) : ∃ B : R,
    ∀ p ∈ cs, ∀ x, B < x → SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp <| cs.finite_toSet.eventually_all.mpr fun p _ =>
    (eventually_gt_atTop _).mono (exists_sign_atTop p).choose_spec
  exact ⟨B, fun p hp x hx => hB x hx.le p hp⟩

/-- A single bound below which every polynomial `p` in a list has the sign of
`p.leadingCoeff * (-1) ^ p.natDegree`. -/
theorem exists_signs_atBot (cs : List R[X]) : ∃ B : R,
    ∀ p ∈ cs, ∀ x, x < B →
      SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree) := by
  obtain ⟨B, hB⟩ := eventually_atBot.mp <| cs.finite_toSet.eventually_all.mpr fun p _ =>
    (eventually_lt_atBot _).mono (exists_sign_atBot p).choose_spec
  exact ⟨B, fun p hp x hx => hB x hx.le p hp⟩

end List
