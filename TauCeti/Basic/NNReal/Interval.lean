/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Basic

/-!
# Reflection of nonnegative real intervals

Reflection about an upper bound turns left-closed, right-open intervals into
left-open, right-closed intervals. The explicit upper bound prevents truncated
subtraction from introducing extra points at zero.
-/

public section

open Set

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
