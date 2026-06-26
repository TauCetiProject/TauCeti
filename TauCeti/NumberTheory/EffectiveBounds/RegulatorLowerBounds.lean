/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EffectiveBounds.Regulator

/-!
# Rank-zero lower bounds for the regulator

The effective-bounds roadmap asks for explicit lower bounds on regulators. The file
`TauCeti.NumberTheory.EffectiveBounds.Regulator` proves the rank-zero exact evaluation
`R_F = 1`, covering fields whose unit lattice has dimension zero. This file records the
corresponding lower-bound API in the forms later estimates tend to use: from a single infinite
place, from degree one, for `ℚ`, and for totally complex quadratic fields.

These are intentionally only corollaries of the existing rank-zero computation; positive-rank
regulator estimates are separate Layer 3 work.

## Main results

* `TauCeti.NumberField.Units.regulator_eq_one_of_card_infinitePlace_eq_one`: exact evaluation
  from a single infinite place.
* `TauCeti.NumberField.Units.one_le_regulator_of_card_infinitePlace_eq_one`: lower bound from a
  single infinite place.
* `TauCeti.NumberField.Units.one_le_regulator_of_card_infinitePlace_le_one`: lower bound from an
  upper bound of one infinite place.
* `TauCeti.NumberField.Units.one_le_regulator_of_finrank_eq_one`: degree-one lower bound.
* `TauCeti.NumberField.Units.one_le_regulator_of_finrank_le_one`: degree-at-most-one lower bound.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.Units
open scoped NumberField

namespace TauCeti.NumberField.Units

variable (K : Type*) [Field K] [NumberField K]

/-- If a number field has a single infinite place, then its regulator is `1`.

This is the exact rank-zero evaluation restated in terms of the infinite-place count, the
condition that identifies `ℚ` and imaginary quadratic fields among number fields. -/
theorem regulator_eq_one_of_card_infinitePlace_eq_one
    (h : Fintype.card (InfinitePlace K) = 1) : regulator K = 1 :=
  regulator_eq_one_of_rank_eq_zero K (rank_eq_zero_of_card_infinitePlace_eq_one K h)

/-- If a number field has a single infinite place, then `1 ≤ R_F`. This is the rank-zero
base case of explicit regulator lower bounds, stated in the form supplied by the infinite-place
classification. -/
theorem one_le_regulator_of_card_infinitePlace_eq_one
    (h : Fintype.card (InfinitePlace K) = 1) : 1 ≤ regulator K :=
  (regulator_eq_one_of_card_infinitePlace_eq_one K h).ge

/-- If a number field has at most one infinite place, then it has exactly one infinite place, so
its regulator is `1`. The nonemptiness of infinite places supplies the missing lower bound on the
cardinality. -/
theorem regulator_eq_one_of_card_infinitePlace_le_one
    (h : Fintype.card (InfinitePlace K) ≤ 1) : regulator K = 1 := by
  refine regulator_eq_one_of_card_infinitePlace_eq_one K ?_
  have hpos : 0 < Fintype.card (InfinitePlace K) :=
    Fintype.card_pos_iff.mpr ⟨Classical.arbitrary _⟩
  omega

/-- If a number field has at most one infinite place, then `1 ≤ R_F`. -/
theorem one_le_regulator_of_card_infinitePlace_le_one
    (h : Fintype.card (InfinitePlace K) ≤ 1) : 1 ≤ regulator K :=
  (regulator_eq_one_of_card_infinitePlace_le_one K h).ge

/-- If a number field has degree one over `ℚ`, then its regulator is `1`. -/
theorem regulator_eq_one_of_finrank_eq_one (h : finrank ℚ K = 1) : regulator K = 1 :=
  regulator_eq_one_of_rank_eq_zero K (rank_eq_zero_of_finrank_eq_one K h)

/-- If a number field has degree one over `ℚ`, then `1 ≤ R_F`. -/
theorem one_le_regulator_of_finrank_eq_one (h : finrank ℚ K = 1) : 1 ≤ regulator K :=
  (regulator_eq_one_of_finrank_eq_one K h).ge

/-- If a number field has degree at most one over `ℚ`, then its regulator is `1`. This is a
consumer form for arguments that produce only an upper bound on the degree. -/
theorem regulator_eq_one_of_finrank_le_one (h : finrank ℚ K ≤ 1) : regulator K = 1 := by
  refine regulator_eq_one_of_finrank_eq_one K ?_
  have hpos : 0 < finrank ℚ K := finrank_pos
  omega

/-- If a number field has degree at most one over `ℚ`, then `1 ≤ R_F`. -/
theorem one_le_regulator_of_finrank_le_one (h : finrank ℚ K ≤ 1) : 1 ≤ regulator K :=
  (regulator_eq_one_of_finrank_le_one K h).ge

/-- If a number field has degree strictly less than two over `ℚ`, then its regulator is `1`.
This is the same rank-zero base case expressed with the common `n < 2` degree bound. -/
theorem regulator_eq_one_of_finrank_lt_two (h : finrank ℚ K < 2) : regulator K = 1 :=
  regulator_eq_one_of_finrank_le_one K (Nat.lt_succ_iff.mp h)

/-- If a number field has degree strictly less than two over `ℚ`, then `1 ≤ R_F`. -/
theorem one_le_regulator_of_finrank_lt_two (h : finrank ℚ K < 2) : 1 ≤ regulator K :=
  (regulator_eq_one_of_finrank_lt_two K h).ge

end TauCeti.NumberField.Units
