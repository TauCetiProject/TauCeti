/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Quantile

/-!
# Quantiles of discrete laws

For a probability measure on `ℕ` or `ℤ`, every interior quantile of its real cast is itself
an integer. It is the least integer whose native cumulative mass reaches the given level.
These characterizations apply without any assumption on the support: gaps, finite support,
and point masses are allowed.

The natural-valued case also gives an explicit `Nat.find` formula. Thus cumulative mass formulas
for individual distributions can be used directly, without computing an infimum in `ℝ`.

## Main results

* `MeasureTheory.Measure.isLeast_quantile_map_natCast` and
  `MeasureTheory.Measure.isLeast_quantile_map_intCast` identify the least cumulative crossings;
* `MeasureTheory.Measure.quantile_map_natCast_eq_iff` and
  `MeasureTheory.Measure.quantile_map_intCast_eq_iff` characterize an individual crossing;
* `MeasureTheory.Measure.quantile_map_natCast_eq_succ_iff` characterizes a positive natural
  quantile by its two adjacent cumulative masses;
* `MeasureTheory.Measure.quantile_map_natCast_eq_find` gives the natural least-search formula.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace MeasureTheory.Measure

section Nat

variable (μ : Measure ℕ) [IsProbabilityMeasure μ] {u : ℝ}

/-- An interior quantile of a natural-valued law is nonnegative. -/
theorem quantile_map_natCast_nonneg (hu : u ∈ Ioo 0 1) :
    0 ≤ (μ.map (Nat.cast : ℕ → ℝ)).quantile u := by
  by_contra h
  have hcdf := le_cdf_quantile (μ.map (Nat.cast : ℕ → ℝ)) hu.2
  rw [cdf_map_natCast_of_neg μ (not_le.mp h)] at hcdf
  exact hu.1.not_ge hcdf

/-- An interior quantile of a natural-valued law is a natural number, so taking its natural
floor and casting back leaves it unchanged. -/
theorem quantile_map_natCast_eq_floor (hu : u ∈ Ioo 0 1) :
    (μ.map (Nat.cast : ℕ → ℝ)).quantile u =
      (⌊(μ.map (Nat.cast : ℕ → ℝ)).quantile u⌋₊ : ℝ) := by
  have hq := quantile_map_natCast_nonneg μ hu
  refine le_antisymm ((quantile_le_iff _ hu.1 hu.2).2 ?_) (Nat.floor_le hq)
  have hcdf := le_cdf_quantile (μ.map (Nat.cast : ℕ → ℝ)) hu.2
  simpa only [cdf_map_natCast μ hq,
    cdf_map_natCast μ (Nat.cast_nonneg _), Nat.floor_natCast] using hcdf

/-- The natural number represented by an interior quantile is the least index whose cumulative
mass reaches the level. -/
theorem isLeast_quantile_map_natCast (hu : u ∈ Ioo 0 1) :
    IsLeast {k : ℕ | u ≤ μ.real (Iic k)}
      ⌊(μ.map (Nat.cast : ℕ → ℝ)).quantile u⌋₊ := by
  constructor
  · have hcdf := le_cdf_quantile (μ.map (Nat.cast : ℕ → ℝ)) hu.2
    rwa [cdf_map_natCast μ (quantile_map_natCast_nonneg μ hu)] at hcdf
  · intro k hk
    have hle : (μ.map (Nat.cast : ℕ → ℝ)).quantile u ≤ (k : ℝ) := by
      rw [quantile_le_iff _ hu.1 hu.2, cdf_map_natCast μ (Nat.cast_nonneg k),
        Nat.floor_natCast]
      exact hk
    exact Nat.floor_le_of_le hle

/-- A natural number is the quantile exactly when it is the least cumulative crossing. This
includes finite supports and levels equal to an attained cumulative mass. -/
@[simp]
theorem quantile_map_natCast_eq_iff (hu : u ∈ Ioo 0 1) (k : ℕ) :
    (μ.map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {j : ℕ | u ≤ μ.real (Iic j)} k := by
  have hleast := isLeast_quantile_map_natCast μ hu
  rw [hleast.isLeast_iff_eq, ← Nat.cast_inj (R := ℝ),
    ← quantile_map_natCast_eq_floor μ hu]

/-- A positive natural quantile is characterized by the strict crossing above the preceding
cumulative mass and the weak crossing at the count itself. -/
theorem quantile_map_natCast_eq_succ_iff (hu : u ∈ Ioo 0 1) (k : ℕ) :
    (μ.map (Nat.cast : ℕ → ℝ)).quantile u = (k + 1 : ℕ) ↔
      μ.real (Iic k) < u ∧ u ≤ μ.real (Iic (k + 1)) := by
  rw [quantile_map_natCast_eq_iff μ hu]
  constructor
  · intro h
    exact ⟨lt_of_not_ge (fun hk ↦ Nat.not_succ_le_self k (h.2 hk)), h.1⟩
  · rintro ⟨hprev, hnext⟩
    refine ⟨hnext, fun j hj ↦ ?_⟩
    by_contra hjk
    have hle : μ.real (Iic j) ≤ μ.real (Iic k) :=
      measureReal_mono (Iic_subset_Iic.mpr (by omega))
    exact hprev.not_ge (hj.trans hle)

/-- The quantile of a natural-valued law is the first index at which its native cumulative mass
reaches the level, expressed by `Nat.find`. -/
theorem quantile_map_natCast_eq_find (hu : u ∈ Ioo 0 1) :
    (μ.map (Nat.cast : ℕ → ℝ)).quantile u =
      (Nat.find (exists_nat_le_measureReal_Iic μ hu.2) : ℝ) := by
  classical
  rw [quantile_map_natCast_eq_iff μ hu]
  exact ⟨Nat.find_spec _, fun _ hk ↦ Nat.find_min' _ hk⟩

end Nat

section Int

variable (μ : Measure ℤ) [IsProbabilityMeasure μ] {u : ℝ}

/-- An interior quantile of an integer-valued law is an integer, including for laws with
unbounded negative support. -/
theorem quantile_map_intCast_eq_floor (hu : u ∈ Ioo 0 1) :
    (μ.map (Int.cast : ℤ → ℝ)).quantile u =
      (⌊(μ.map (Int.cast : ℤ → ℝ)).quantile u⌋ : ℝ) := by
  refine le_antisymm ((quantile_le_iff _ hu.1 hu.2).2 ?_) (Int.floor_le _)
  have hcdf := le_cdf_quantile (μ.map (Int.cast : ℤ → ℝ)) hu.2
  simpa only [cdf_map_intCast, Int.floor_intCast] using hcdf

/-- The integer represented by an interior quantile is the least index whose cumulative mass
reaches the level. -/
theorem isLeast_quantile_map_intCast (hu : u ∈ Ioo 0 1) :
    IsLeast {k : ℤ | u ≤ μ.real (Iic k)}
      ⌊(μ.map (Int.cast : ℤ → ℝ)).quantile u⌋ := by
  constructor
  · have hcdf := le_cdf_quantile (μ.map (Int.cast : ℤ → ℝ)) hu.2
    rwa [cdf_map_intCast] at hcdf
  · intro k hk
    have hle : (μ.map (Int.cast : ℤ → ℝ)).quantile u ≤ (k : ℝ) := by
      rw [quantile_le_iff _ hu.1 hu.2, cdf_map_intCast, Int.floor_intCast]
      exact hk
    exact (Int.floor_mono hle).trans_eq (Int.floor_intCast k)

/-- An integer is the quantile exactly when it is the least cumulative crossing. -/
@[simp]
theorem quantile_map_intCast_eq_iff (hu : u ∈ Ioo 0 1) (k : ℤ) :
    (μ.map (Int.cast : ℤ → ℝ)).quantile u = k ↔
      IsLeast {j : ℤ | u ≤ μ.real (Iic j)} k := by
  have hleast := isLeast_quantile_map_intCast μ hu
  rw [hleast.isLeast_iff_eq, ← Int.cast_inj (α := ℝ),
    ← quantile_map_intCast_eq_floor μ hu]

end Int

end MeasureTheory.Measure
