/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence

/-! # The second entry of a Sturm sequence

Reading a missing second entry as zero recovers the second input uniformly,
including the singleton sequence with zero second input.
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

end Polynomial
