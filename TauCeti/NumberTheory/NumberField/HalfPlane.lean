/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Right half-planes associated with a number field

Elementary set inclusions between the closed half-plane `Re s ≥ 1` and the open half-plane
`Re s > 1 - 1 / [K : ℚ]` for a number field `K`.

## Main results

* `TauCeti.setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re`: the closed half-plane
  `Re s ≥ 1` lies in `{s : ℂ | 1 - 1 / [K : ℚ] < s.re}`.
-/

public section

namespace TauCeti

/-- The closed half-plane `Re s ≥ 1` lies in the half-plane of the Dedekind zeta continuation. -/
theorem setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re
    (K : Type*) [Field K] [NumberField K] :
    {s : ℂ | 1 ≤ s.re} ⊆ {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} :=
  fun _ hs ↦
    (sub_lt_self (1 : ℝ) (one_div_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos))).trans_le hs

end TauCeti
