/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Basic

/-!
# Nonnegative real intervals

Reflection about an upper bound turns left-closed, right-open intervals into
left-open, right-closed intervals. The explicit upper bound prevents truncated
subtraction from introducing extra points at zero. Pulling a left-open, right-closed
`ℝ≥0` interval `Ioc u v` (`(u, v]`) back along `Real.toNNReal` yields the corresponding
real interval `Ioc (u : ℝ) (v : ℝ)`.
-/

public section

open Set
open scoped NNReal

/-- The preimage of a left-open, right-closed `ℝ≥0` interval `Ioc u v` (`(u, v]`) under
`Real.toNNReal` is the corresponding real interval `Ioc (u : ℝ) (v : ℝ)`. Nonpositive reals
are excluded on both sides because `u ≥ 0` is a strict (open) lower bound (`0 ∉ Ioc u v`). -/
@[simp]
theorem Real.preimage_toNNReal_Ioc (u v : ℝ≥0) :
    Real.toNNReal ⁻¹' Ioc u v = Ioc (u : ℝ) (v : ℝ) := by
  ext x
  simp only [mem_preimage, mem_Ioc, Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_le_iff_le_coe]

namespace NNReal

/-- Membership in a reflected half-open interval, retaining both endpoint conventions. -/
theorem mem_Ioc_tsub_iff {t a b : ℝ≥0} (s : ℝ≥0) (hab : a ≤ b) (hbt : b ≤ t) :
    s ∈ Ioc (t - b) (t - a) ↔ s ≤ t ∧ t - s ∈ Ico a b := by
  simp only [mem_Ioc, mem_Ico]
  constructor
  · rintro ⟨hb, ha⟩
    have hst : s ≤ t := ha.trans tsub_le_self
    exact ⟨hst, (le_tsub_iff_left hst).2 ((le_tsub_iff_right (hab.trans hbt)).1 ha),
      (tsub_lt_iff_left hst).2 ((tsub_lt_iff_right hbt).1 hb)⟩
  · rintro ⟨hst, ha, hb⟩
    constructor
    · exact (tsub_lt_iff_right hbt).2 ((tsub_lt_iff_left hst).1 hb)
    · exact (le_tsub_iff_right (hab.trans hbt)).2 ((le_tsub_iff_left hst).1 ha)

end NNReal
