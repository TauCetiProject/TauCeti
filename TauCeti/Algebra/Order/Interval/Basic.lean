/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Halves and rational casts of nonempty intervals

This file splits a nonempty closed interval `[a, b]` of an ordered field at its midpoint, into
the lower half `[a, (a + b) / 2]` and the upper half `[(a + b) / 2, b]`. Each half lies in the
interval and has half its length. Repeated halving is the basic step of interval bisection.

It also shows that nested rational intervals span nested intervals of every ordered field.

## Main definitions

* `NonemptyInterval.lowerHalf`, `NonemptyInterval.upperHalf`: the halves `[a, (a + b) / 2]` and
  `[(a + b) / 2, b]` of an interval `[a, b]`.

## Main results

* `NonemptyInterval.lowerHalf_le`, `NonemptyInterval.upperHalf_le`: each half lies in the
  interval.
* `NonemptyInterval.length_lowerHalf`, `NonemptyInterval.length_upperHalf`: each half has half
  the length of the interval.
* `NonemptyInterval.Icc_ratCast_subset_Icc_ratCast`: nested rational intervals span nested
  intervals of every ordered field.
-/

public section

/-- Nested rational intervals span nested intervals of every ordered field. -/
theorem NonemptyInterval.Icc_ratCast_subset_Icc_ratCast {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {I J : NonemptyInterval ℚ} (h : I ≤ J) :
    Set.Icc (I.fst : K) I.snd ⊆ Set.Icc (J.fst : K) J.snd :=
  Set.Icc_subset_Icc (Rat.cast_le.mpr (NonemptyInterval.le_def.mp h).1)
    (Rat.cast_le.mpr (NonemptyInterval.le_def.mp h).2)

namespace NonemptyInterval

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (I : NonemptyInterval K)

/-- The lower half `[a, (a + b) / 2]` of an interval `[a, b]`. -/
def lowerHalf : NonemptyInterval K :=
  ⟨(I.fst, (I.fst + I.snd) / 2), by dsimp only; linarith [I.fst_le_snd]⟩

/-- The upper half `[(a + b) / 2, b]` of an interval `[a, b]`. -/
def upperHalf : NonemptyInterval K :=
  ⟨((I.fst + I.snd) / 2, I.snd), by dsimp only; linarith [I.fst_le_snd]⟩

@[simp]
theorem lowerHalf_fst : I.lowerHalf.fst = I.fst :=
  (rfl)

@[simp]
theorem lowerHalf_snd : I.lowerHalf.snd = (I.fst + I.snd) / 2 :=
  (rfl)

@[simp]
theorem upperHalf_fst : I.upperHalf.fst = (I.fst + I.snd) / 2 :=
  (rfl)

@[simp]
theorem upperHalf_snd : I.upperHalf.snd = I.snd :=
  (rfl)

/-- The lower half of an interval lies in the interval. -/
theorem lowerHalf_le : I.lowerHalf ≤ I :=
  NonemptyInterval.le_def.mpr ⟨le_rfl, by simp only [lowerHalf_snd]; linarith [I.fst_le_snd]⟩

/-- The upper half of an interval lies in the interval. -/
theorem upperHalf_le : I.upperHalf ≤ I :=
  NonemptyInterval.le_def.mpr ⟨by simp only [upperHalf_fst]; linarith [I.fst_le_snd], le_rfl⟩

/-- The lower half of an interval has half its length. -/
@[simp]
theorem length_lowerHalf : I.lowerHalf.length = I.length / 2 := by
  simp only [length, lowerHalf_fst, lowerHalf_snd]
  ring

/-- The upper half of an interval has half its length. -/
@[simp]
theorem length_upperHalf : I.upperHalf.length = I.length / 2 := by
  simp only [length, upperHalf_fst, upperHalf_snd]
  ring

end NonemptyInterval
