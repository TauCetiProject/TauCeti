/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# The regulator of a number field of unit rank zero

The regulator `R_F` of a number field `F` is the covolume of its unit lattice
(`NumberField.Units.regulator`). When the unit rank is zero — equivalently, `F` has a single
infinite place, so `F = ℚ` or `F` is imaginary quadratic — the unit lattice lives in the
zero-dimensional log space, and its covolume is the empty determinant `1`.

This is the base case of the effective-bounds roadmap's Layer 3 (regulators and unit-lattice
volume): the exact value `R_F = 1`, and the corresponding lower-bound forms `1 ≤ R_F`, on the
fields where the regulator carries no information. Mathlib defines the regulator and proves it
positive (`NumberField.Units.regulator_pos`) but does not evaluate it in the rank-zero case.

## Main results

* `TauCeti.NumberField.Units.regulator_eq_one_of_rank_eq_zero`: `R_F = 1` when the unit rank
  of `F` is zero.
* `TauCeti.NumberField.Units.one_le_regulator_of_rank_eq_zero`: `1 ≤ R_F` when the unit rank
  of `F` is zero.
* `TauCeti.NumberField.Units.regulator_rat_eq_one`: `R_ℚ = 1`.
* `TauCeti.NumberField.Units.one_le_regulator_rat`: `1 ≤ R_ℚ`.
* `TauCeti.NumberField.Units.regulator_eq_one_of_isTotallyComplex_of_finrank_eq_two`:
  `R_F = 1` for an imaginary quadratic field `F`.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped NumberField

namespace TauCeti.NumberField.Units

variable (K : Type*) [Field K] [NumberField K]

/-- **The regulator of a number field of unit rank zero is `1`.** When the unit rank is zero,
the unit lattice sits inside the zero-dimensional log space, and the regulator — its covolume,
computed by `NumberField.Units.regulator_eq_det'` as a determinant indexed by the infinite
places other than the distinguished one — is the determinant of the empty matrix, `1`. -/
theorem regulator_eq_one_of_rank_eq_zero (h : rank K = 0) : regulator K = 1 := by
  classical
  -- A rank-zero field has no infinite place other than the distinguished `w₀`, so the matrix
  -- whose determinant is the regulator is the empty matrix.
  haveI : IsEmpty {w : InfinitePlace K // w ≠ w₀} := by
    rw [← Fintype.card_eq_zero_iff, ← Fintype.card_congr (equivFinRank K), Fintype.card_fin, h]
  rw [regulator_eq_det', Matrix.det_isEmpty, abs_one]

/-- The regulator lower bound in the rank-zero case: `1 ≤ R_F`. -/
theorem one_le_regulator_of_rank_eq_zero (h : rank K = 0) : 1 ≤ regulator K :=
  (regulator_eq_one_of_rank_eq_zero K h).ge

/-- A number field with a single infinite place has unit rank zero. This covers `ℚ` (one real
place) and the imaginary quadratic fields (one complex place). -/
theorem rank_eq_zero_of_card_infinitePlace_eq_one
    (h : Fintype.card (InfinitePlace K) = 1) : rank K = 0 := by
  rw [NumberField.Units.rank, h]

/-- If a number field has a single infinite place, then `1 ≤ R_F`.

This is the rank-zero lower bound restated in terms of the infinite-place count, the condition
that identifies `ℚ` and imaginary quadratic fields among number fields. -/
theorem one_le_regulator_of_card_infinitePlace_eq_one
    (h : Fintype.card (InfinitePlace K) = 1) : 1 ≤ regulator K :=
  one_le_regulator_of_rank_eq_zero K (rank_eq_zero_of_card_infinitePlace_eq_one K h)

/-- If a number field has at most one infinite place, then it has exactly one infinite place, so
`1 ≤ R_F`. The nonemptiness of infinite places supplies the missing lower bound on the
cardinality. -/
theorem one_le_regulator_of_card_infinitePlace_le_one
    (h : Fintype.card (InfinitePlace K) ≤ 1) : 1 ≤ regulator K := by
  refine one_le_regulator_of_card_infinitePlace_eq_one K ?_
  have hpos : 0 < Fintype.card (InfinitePlace K) :=
    Fintype.card_pos_iff.mpr ⟨Classical.arbitrary _⟩
  omega

/-- A number field of degree one over `ℚ` (namely `ℚ` itself) has unit rank zero. -/
theorem rank_eq_zero_of_finrank_eq_one (h : finrank ℚ K = 1) : rank K = 0 := by
  refine rank_eq_zero_of_card_infinitePlace_eq_one K ?_
  have h₁ := card_add_two_mul_card_eq_rank K
  have h₂ := card_eq_nrRealPlaces_add_nrComplexPlaces K
  omega

/-- If a number field has degree one over `ℚ`, then `1 ≤ R_F`. -/
theorem one_le_regulator_of_finrank_eq_one (h : finrank ℚ K = 1) : 1 ≤ regulator K :=
  one_le_regulator_of_rank_eq_zero K (rank_eq_zero_of_finrank_eq_one K h)

/-- If a number field has degree at most one over `ℚ`, then `1 ≤ R_F`. This is a
consumer form for arguments that produce only an upper bound on the degree. -/
theorem one_le_regulator_of_finrank_le_one (h : finrank ℚ K ≤ 1) : 1 ≤ regulator K := by
  refine one_le_regulator_of_finrank_eq_one K ?_
  have hpos : 0 < finrank ℚ K := finrank_pos
  omega

/-- If a number field has degree strictly less than two over `ℚ`, then `1 ≤ R_F`.
This is the same rank-zero base case expressed with the common `n < 2` degree bound. -/
theorem one_le_regulator_of_finrank_lt_two (h : finrank ℚ K < 2) : 1 ≤ regulator K :=
  one_le_regulator_of_finrank_le_one K (Nat.lt_succ_iff.mp h)

/-- An imaginary quadratic field — totally complex of degree two — has unit rank zero. -/
theorem rank_eq_zero_of_isTotallyComplex_of_finrank_eq_two
    [IsTotallyComplex K] (h : finrank ℚ K = 2) : rank K = 0 := by
  refine rank_eq_zero_of_card_infinitePlace_eq_one K ?_
  have h₁ := card_add_two_mul_card_eq_rank K
  have h₂ := card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h₃ := IsTotallyComplex.nrRealPlaces_eq_zero (K := K)
  omega

/-- **The regulator of `ℚ` is `1`.** The rational field has rank zero, so its regulator is the
empty determinant. -/
@[simp]
theorem regulator_rat_eq_one : regulator ℚ = 1 :=
  regulator_eq_one_of_rank_eq_zero ℚ (rank_eq_zero_of_finrank_eq_one ℚ (finrank_self ℚ))

/-- The regulator lower bound for `ℚ`: `1 ≤ R_ℚ`. -/
theorem one_le_regulator_rat : 1 ≤ regulator ℚ :=
  regulator_rat_eq_one.ge

/-- **The regulator of an imaginary quadratic field is `1`**, the rank-zero base case on a
degree-two totally complex field. -/
theorem regulator_eq_one_of_isTotallyComplex_of_finrank_eq_two
    [IsTotallyComplex K] (h : finrank ℚ K = 2) : regulator K = 1 :=
  regulator_eq_one_of_rank_eq_zero K (rank_eq_zero_of_isTotallyComplex_of_finrank_eq_two K h)

/-- The regulator lower bound for an imaginary quadratic field: `1 ≤ R_F`. -/
theorem one_le_regulator_of_isTotallyComplex_of_finrank_eq_two
    [IsTotallyComplex K] (h : finrank ℚ K = 2) : 1 ≤ regulator K :=
  (regulator_eq_one_of_isTotallyComplex_of_finrank_eq_two K h).ge

end TauCeti.NumberField.Units
