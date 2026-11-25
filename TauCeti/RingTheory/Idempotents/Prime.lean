/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.RingTheory.Ideal.Prime

/-!
# Idempotents and prime ideals

An idempotent `e` and its complement `1 - e` multiply to `0` and add up to `1`, so a prime ideal
contains exactly one of them. On the prime spectrum of a commutative ring this says that the basic
open sets of `e` and `1 - e` are complementary.

## Main results

* `IsIdempotentElem.one_sub_mem_iff_notMem`: a prime ideal contains exactly one of `e` and
  `1 - e`.
-/

public section

/-- A prime ideal contains exactly one of an idempotent `e` and its complement `1 - e`. -/
theorem IsIdempotentElem.one_sub_mem_iff_notMem {R : Type*} [Ring R] {e : R}
    (he : IsIdempotentElem e) {P : Ideal R} [hP : P.IsPrime] : 1 - e ∈ P ↔ e ∉ P := by
  refine ⟨fun h he' ↦ hP.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.add_mem he' h)),
    fun h ↦ (hP.mem_or_mem ?_).resolve_left h⟩
  rw [he.mul_one_sub_self]
  exact P.zero_mem
