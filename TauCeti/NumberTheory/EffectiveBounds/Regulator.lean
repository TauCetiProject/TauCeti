/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.NumberTheory.EffectiveBounds.UnitHeight
public import TauCeti.NumberTheory.NumberField.Units.FundamentalSystem

/-!
# Explicit lower bounds for number-field regulators

In degree `d` and unit rank `r`, the regulator is at least
`(log 2 / (unitPowerCountBound d + 1)) ^ r / r!`. This is a positive, explicit expression
depending only on `d` and `r`, including positive unit ranks. The estimate combines the
explicit nontorsion-unit height gap with Minkowski's second theorem for the unit logarithmic
lattice. It is intentionally coarse; it does not use a minimum obtained from finiteness.

The rank-zero case also admits an exact evaluation:

The regulator `R_F` of a number field `F` is the covolume of its unit lattice
(`NumberField.Units.regulator`). When the unit rank is zero — equivalently, `F` has a single
infinite place, so `F = ℚ` or `F` is imaginary quadratic — the unit lattice lives in the
zero-dimensional log space, and its covolume is the empty determinant `1`.

This is the base case of the effective-bounds roadmap's Layer 3 (regulators and unit-lattice
volume): the exact value `R_F = 1`, which is in particular the trivial lower bound `1 ≤ R_F`,
on the fields where the regulator carries no information. Mathlib defines the regulator and
proves it positive (`NumberField.Units.regulator_pos`) but does not evaluate it in the
rank-zero case.

## Main results

* `TauCeti.NumberField.Units.regulatorLowerBound_le_regulator`: an explicit positive
  degree-and-rank bound for every number field.
* `NumberField.Units.regulator_eq_one_of_rank_eq_zero`: `R_F = 1` when the unit rank
  of `F` is zero.
* `NumberField.Units.one_le_regulator_of_rank_eq_zero`: the corresponding lower bound
  `1 ≤ R_F`.
* `NumberField.Units.regulator_rat_eq_one`: `R_ℚ = 1`.
* `NumberField.Units.regulator_eq_one_of_isTotallyComplex_of_finrank_eq_two`:
  `R_F = 1` for an imaginary quadratic field `F`.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem (w₀)
open scoped NumberField

namespace NumberField.Units

variable (K : Type*) [Field K] [NumberField K]

/-- **The regulator of a number field of unit rank zero is `1`.** When the unit rank is zero,
the unit lattice sits inside the zero-dimensional log space, and the regulator — its covolume,
computed by `NumberField.Units.regulator_eq_det'` as a determinant indexed by the infinite
places other than the distinguished one — is the determinant of the empty matrix, `1`. -/
@[simp]
theorem regulator_eq_one_of_rank_eq_zero (h : rank K = 0) : regulator K = 1 := by
  classical
  -- A rank-zero field has no infinite place other than the distinguished `w₀`, so the matrix
  -- whose determinant is the regulator is the empty matrix.
  have : IsEmpty {w : InfinitePlace K // w ≠ w₀} := by
    rw [← Fintype.card_eq_zero_iff, ← Fintype.card_congr (equivFinRank K), Fintype.card_fin, h]
  rw [regulator_eq_det', Matrix.det_isEmpty, abs_one]

/-- A number field with at most one infinite place has unit rank zero. This covers `ℚ` (one real
place) and the imaginary quadratic fields (one complex place), and is stated in the monotone
form consumed by effective lower-bound arguments. -/
theorem rank_eq_zero_of_card_infinitePlace_le_one
    (h : Fintype.card (InfinitePlace K) ≤ 1) : rank K = 0 := by
  rw [NumberField.Units.rank]
  omega

/-- A number field with a single infinite place has unit rank zero. -/
theorem rank_eq_zero_of_card_infinitePlace_eq_one
    (h : Fintype.card (InfinitePlace K) = 1) : rank K = 0 :=
  rank_eq_zero_of_card_infinitePlace_le_one K h.le

/-- A number field of degree at most one over `ℚ` has unit rank zero. -/
theorem rank_eq_zero_of_finrank_le_one (h : finrank ℚ K ≤ 1) : rank K = 0 := by
  refine rank_eq_zero_of_card_infinitePlace_eq_one K ?_
  have hpos : 0 < finrank ℚ K := Module.finrank_pos
  have h₁ := card_add_two_mul_card_eq_rank K
  have h₂ := card_eq_nrRealPlaces_add_nrComplexPlaces K
  omega

/-- A number field of degree less than two over `ℚ` has unit rank zero. -/
theorem rank_eq_zero_of_finrank_lt_two (h : finrank ℚ K < 2) : rank K = 0 :=
  rank_eq_zero_of_finrank_le_one K (by omega)

/-- A number field of degree one over `ℚ` (namely `ℚ` itself) has unit rank zero. -/
theorem rank_eq_zero_of_finrank_eq_one (h : finrank ℚ K = 1) : rank K = 0 :=
  rank_eq_zero_of_finrank_le_one K h.le

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

/-- **The regulator of an imaginary quadratic field is `1`**, the rank-zero base case on a
degree-two totally complex field. -/
theorem regulator_eq_one_of_isTotallyComplex_of_finrank_eq_two
    [IsTotallyComplex K] (h : finrank ℚ K = 2) : regulator K = 1 :=
  regulator_eq_one_of_rank_eq_zero K (rank_eq_zero_of_isTotallyComplex_of_finrank_eq_two K h)

/-- **Rank-zero regulator lower bound.** If the unit rank of `K` is zero, then `1 ≤ R_K`. -/
theorem one_le_regulator_of_rank_eq_zero (h : rank K = 0) : 1 ≤ regulator K := by
  rw [regulator_eq_one_of_rank_eq_zero K h]

/-- **One-infinite-place regulator lower bound.** If `K` has at most one infinite place, then
`1 ≤ R_K`. -/
theorem one_le_regulator_of_card_infinitePlace_le_one
    (h : Fintype.card (InfinitePlace K) ≤ 1) : 1 ≤ regulator K :=
  one_le_regulator_of_rank_eq_zero K (rank_eq_zero_of_card_infinitePlace_le_one K h)

/-- **One-infinite-place regulator lower bound.** If `K` has one infinite place, then
`1 ≤ R_K`. -/
theorem one_le_regulator_of_card_infinitePlace_eq_one
    (h : Fintype.card (InfinitePlace K) = 1) : 1 ≤ regulator K :=
  one_le_regulator_of_card_infinitePlace_le_one K h.le

/-- **Degree-at-most-one regulator lower bound.** If `[K : ℚ] ≤ 1`, then `1 ≤ R_K`. -/
theorem one_le_regulator_of_finrank_le_one (h : finrank ℚ K ≤ 1) : 1 ≤ regulator K :=
  one_le_regulator_of_rank_eq_zero K (rank_eq_zero_of_finrank_le_one K h)

/-- **Degree-less-than-two regulator lower bound.** If `[K : ℚ] < 2`, then `1 ≤ R_K`. -/
theorem one_le_regulator_of_finrank_lt_two (h : finrank ℚ K < 2) : 1 ≤ regulator K :=
  one_le_regulator_of_finrank_le_one K (by omega)

/-- **Degree-one regulator lower bound.** If `[K : ℚ] = 1`, then `1 ≤ R_K`. -/
theorem one_le_regulator_of_finrank_eq_one (h : finrank ℚ K = 1) : 1 ≤ regulator K :=
  one_le_regulator_of_finrank_le_one K h.le

/-- **The rational regulator lower bound.** For `ℚ`, `1 ≤ R_ℚ`. -/
theorem one_le_regulator_rat : 1 ≤ regulator ℚ := by
  rw [regulator_rat_eq_one]

/-- **Imaginary-quadratic regulator lower bound.** If `K` is totally complex of degree two, then
`1 ≤ R_K`. -/
theorem one_le_regulator_of_isTotallyComplex_of_finrank_eq_two
    [IsTotallyComplex K] (h : finrank ℚ K = 2) : 1 ≤ regulator K :=
  one_le_regulator_of_rank_eq_zero K (rank_eq_zero_of_isTotallyComplex_of_finrank_eq_two K h)

end NumberField.Units

namespace TauCeti.NumberField.Units

/-- The explicit lower bound for the regulator in degree `d` and unit rank `r`. -/
noncomputable def regulatorLowerBound (d r : ℕ) : ℝ :=
  unitHeightLowerBound d ^ r / r.factorial

/-- The explicit regulator bound is positive, including every positive unit rank. -/
theorem regulatorLowerBound_pos (d r : ℕ) : 0 < regulatorLowerBound d r :=
  div_pos (pow_pos (unitHeightLowerBound_pos d) r) (by positivity)

/-- The explicit regulator lower bound has the standard value one in rank zero. -/
@[simp]
theorem regulatorLowerBound_rank_zero (d : ℕ) : regulatorLowerBound d 0 = 1 := by
  simp [regulatorLowerBound]

/-- **An explicit regulator lower bound in every unit rank.** If `d = [K : ℚ]` and
`r = rank K`, then `R_K ≥ (log 2 / (unitPowerCountBound d + 1)) ^ r / r!`.
The constant depends only on the degree and unit rank and is strictly positive. -/
theorem regulatorLowerBound_le_regulator (K : Type*) [Field K] [NumberField K] :
    regulatorLowerBound (finrank ℚ K) (rank K) ≤ regulator K := by
  classical
  obtain ⟨u, hu, hprod⟩ := exists_isMaxRank_prod_sum_abs_logEmbedding_le (K := K)
  have hheight (i : Fin (rank K)) :
      unitHeightLowerBound (finrank ℚ K) ≤
        ∑ w, |logEmbedding K (Additive.ofMul (u i)) w| := by
    have hut : u i ∉ torsion K := fun h ↦ hu.ne_zero i
      (dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr h)
    exact (unitHeightLowerBound_le_logHeight₁ hut).trans
      (le_of_mul_le_mul_left (two_mul_logHeight₁_le_two_mul_sum_abs_logEmbedding (u i)) two_pos)
  rw [regulatorLowerBound, div_le_iff₀ (by positivity)]
  calc unitHeightLowerBound (finrank ℚ K) ^ rank K
      = ∏ _ : Fin (rank K), unitHeightLowerBound (finrank ℚ K) := by simp
    _ ≤ ∏ i, ∑ w, |logEmbedding K (Additive.ofMul (u i)) w| :=
      Finset.prod_le_prod₀ (fun _ _ ↦ (unitHeightLowerBound_pos _).le) (fun i _ ↦ hheight i)
    _ ≤ _ := by simpa only [mul_comm] using hprod

end TauCeti.NumberField.Units
