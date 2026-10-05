/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence

/-! # Entries of a Sturm sequence

Reading a missing second entry as zero recovers the second input uniformly,
including the singleton sequence with zero second input. Each entry after the second is the
negated remainder of its two predecessors, and from the second entry on the degrees strictly
decrease. These facts let results about one Euclidean step be propagated along the whole
sequence.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- A nonzero-headed Sturm sequence has its second input as its second entry,
with zero representing the missing entry of a singleton sequence. -/
@[simp, grind =]
theorem getD_getElem?_sturmSeq {p : K[X]} (hp : p ≠ 0) (q : K[X]) :
    (sturmSeq p q)[1]?.getD 0 = q := by
  rw [← List.head?_tail]
  rw [sturmSeq_cons hp, List.tail_cons]
  by_cases hq : q = 0
  · simp only [hq, sturmSeq_zero_left, List.head?_nil, Option.getD_none]
  · simp only [head?_sturmSeq hq, Option.getD_some]

/-- Every entry of a Sturm sequence after the second is the negated remainder of its two
predecessors. -/
theorem eq_neg_mod_of_getElem?_sturmSeq {p q a b c : K[X]} {i : ℕ}
    (ha : (sturmSeq p q)[i]? = some a) (hb : (sturmSeq p q)[i + 1]? = some b)
    (hc : (sturmSeq p q)[i + 2]? = some c) : c = -a % b := by
  induction p, q using sturmSeq.induct generalizing i with
  | case1 q => simp at ha
  | case2 p q hp ih =>
    rw [sturmSeq_cons hp] at ha hb hc
    rcases i with _ | i
    · have hq : q ≠ 0 := by
        rintro rfl
        simp at hb
      have hr : -p % q ≠ 0 := by
        rintro hr
        simp [sturmSeq_cons hq, hr] at hc
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      simp only [List.getElem?_cons_succ, sturmSeq_cons hq, List.getElem?_cons_zero,
        Option.some.injEq] at hb
      simp only [List.getElem?_cons_succ, sturmSeq_cons hq, sturmSeq_cons hr,
        List.getElem?_cons_zero, Option.some.injEq] at hc
      rw [← ha, ← hb, ← hc]
    · exact ih ha hb hc

/-- From the second entry on, the degrees of the entries of a Sturm sequence strictly
decrease. The first two entries are unconstrained. -/
theorem natDegree_lt_of_getElem?_sturmSeq {p q s t : K[X]} {i : ℕ}
    (hs : (sturmSeq p q)[i + 1]? = some s) (ht : (sturmSeq p q)[i + 2]? = some t) :
    t.natDegree < s.natDegree := by
  induction p, q using sturmSeq.induct generalizing i with
  | case1 q => simp at hs
  | case2 p q hp ih =>
    rw [sturmSeq_cons hp] at hs ht
    rcases i with _ | i
    · have hq : q ≠ 0 := by
        rintro rfl
        simp at hs
      have hr : -p % q ≠ 0 := by
        rintro hr
        simp [sturmSeq_cons hq, hr] at ht
      simp only [List.getElem?_cons_succ, sturmSeq_cons hq, List.getElem?_cons_zero,
        Option.some.injEq] at hs
      simp only [List.getElem?_cons_succ, sturmSeq_cons hq, sturmSeq_cons hr,
        List.getElem?_cons_zero, Option.some.injEq] at ht
      rw [← hs, ← ht]
      exact natDegree_lt_natDegree hr (degree_mod_lt _ hq)
    · exact ih hs ht

/-- If the second input has degree at most that of the first, then so does every entry of the
Sturm sequence. -/
theorem natDegree_le_of_mem_sturmSeq {p q s : K[X]} (hs : s ∈ sturmSeq p q)
    (hq : q.natDegree ≤ p.natDegree) : s.natDegree ≤ p.natDegree := by
  induction p, q using sturmSeq.induct with
  | case1 q => simp at hs
  | case2 p q hp ih =>
    rw [sturmSeq_cons hp, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact le_rfl
    · by_cases hq0 : q = 0
      · simp [hq0] at hs
      · exact (ih hs (natDegree_le_natDegree (degree_mod_lt _ hq0).le)).trans hq

end Polynomial
