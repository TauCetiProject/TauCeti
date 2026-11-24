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

The file also records that `-1` lies in the unit group of every valuation subring, with residue
`-1` (`ValuationSubring.unitGroupToResidueFieldUnits_neg_one`); signs `(-1) ^ n` such as the one in
the tame symbol `Valuation.tameSymbol` are reduced to the residue field this way.
-/

public section

namespace ValuationSubring

variable {K : Type*} [Field K]

/-- A field unit belongs to the unit group of a valuation subring if and only if
one of its nonzero powers does. -/
theorem pow_mem_unitGroup_iff (A : ValuationSubring K) {n : ℕ} (hn : n ≠ 0) {x : Kˣ} :
    x ^ n ∈ A.unitGroup ↔ x ∈ A.unitGroup := by
  simp only [mem_unitGroup_iff, Units.val_pow_eq_pow_val, map_pow, pow_eq_one_iff_left hn]

/-- `-1` is a unit of every valuation subring. -/
theorem neg_one_mem_unitGroup (A : ValuationSubring K) : (-1 : Kˣ) ∈ A.unitGroup := by
  simp [mem_unitGroup_iff]

/-- The residue of the unit `-1` of a valuation subring is `-1`. -/
@[simp]
theorem unitGroupToResidueFieldUnits_neg_one (A : ValuationSubring K) :
    A.unitGroupToResidueFieldUnits ⟨-1, A.neg_one_mem_unitGroup⟩ = -1 := by
  have h : ((A.unitGroupMulEquiv ⟨-1, A.neg_one_mem_unitGroup⟩ : Aˣ) : A) = -1 :=
    Subtype.ext (by simp)
  ext
  rw [coe_unitGroupToResidueFieldUnits_apply, h, Units.val_neg, Units.val_one, map_neg, map_one]
  -- The two sides differ only in the `Neg` and `One` instances of `A ⧸ maximalIdeal A` and of
  -- `IsLocalRing.ResidueField A`, which is defined as that quotient.
  rfl

end ValuationSubring
