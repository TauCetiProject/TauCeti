/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Powers in the unit group of a valuation subring

A nonzero power of a field unit lies in the unit group of a valuation subring exactly when
that unit does. Consequently a root in the field of a unit of the valuation subring is itself
a unit of the valuation subring. This permits local power equations to be read in the unit
group.
-/

public section

namespace ValuationSubring

variable {K : Type*} [Field K]

/-- A field unit belongs to the unit group of a valuation subring if and only if
one of its nonzero powers does. -/
theorem pow_mem_unitGroup_iff (A : ValuationSubring K) {n : ℕ} (hn : n ≠ 0) {x : Kˣ} :
    x ^ n ∈ A.unitGroup ↔ x ∈ A.unitGroup := by
  simp only [mem_unitGroup_iff, Units.val_pow_eq_pow_val, map_pow, pow_eq_one_iff_left hn]

end ValuationSubring
