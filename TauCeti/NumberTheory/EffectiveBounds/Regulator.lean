/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import TauCeti.NumberTheory.EffectiveBounds.UnitHeight
public import TauCeti.NumberTheory.NumberField.Units.FundamentalSystem

/-!
# Explicit lower bounds for number-field regulators

In degree `d` and unit rank `r`, the regulator is at least
`(log 2 / (unitPowerCountBound d + 1)) ^ r / r!`. This is a positive, explicit expression
depending only on `d` and `r`, including positive unit ranks. The estimate combines the
explicit nontorsion-unit height gap with Minkowski's second theorem for the unit logarithmic
lattice. It is intentionally coarse; it does not use a minimum obtained from finiteness.

In unit rank zero this bound is `1`, which is the exact value of the regulator there
(`NumberField.Units.regulator_eq_one_of_rank_eq_zero` in
`TauCeti.NumberTheory.NumberField.Units.Regulator.Basic`).

## Main results

* `TauCeti.NumberField.Units.regulatorLowerBound_le_regulator`: an explicit positive
  degree-and-rank bound for every number field.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.Units
open scoped NumberField

namespace TauCeti.NumberField.Units

/-- The explicit lower bound for the regulator in degree `d` and unit rank `r`. -/
noncomputable def regulatorLowerBound (d r : ℕ) : ℝ :=
  unitHeightLowerBound d ^ r / r.factorial

/-- The degree-and-rank formula for the explicit regulator lower bound. -/
theorem regulatorLowerBound_def (d r : ℕ) :
    regulatorLowerBound d r = unitHeightLowerBound d ^ r / r.factorial := by rfl

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
    exact (unitHeightLowerBound_le_logHeight₁ hut).trans (logHeight₁_le_sum_abs_logEmbedding (u i))
  rw [regulatorLowerBound, div_le_iff₀ (by positivity)]
  calc unitHeightLowerBound (finrank ℚ K) ^ rank K
      = ∏ _ : Fin (rank K), unitHeightLowerBound (finrank ℚ K) := by simp
    _ ≤ ∏ i, ∑ w, |logEmbedding K (Additive.ofMul (u i)) w| :=
      Finset.prod_le_prod₀ (fun _ _ ↦ (unitHeightLowerBound_pos _).le) (fun i _ ↦ hheight i)
    _ ≤ _ := by simpa only [mul_comm] using hprod

end TauCeti.NumberField.Units
