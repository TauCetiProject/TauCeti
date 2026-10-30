/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Measures on the half-line

A probability measure on the nonnegative half-line `ℝ≥0` either is the point mass at zero or
charges some half-line `[a, ∞)` with `a > 0`. This is the form in which the hypothesis
`F {0} < 1` is used to extract a positive threshold for a law of nonnegative increments.

## Main results

* `MeasureTheory.Measure.exists_pos_measure_Ici` — a probability measure on `ℝ≥0` that is not the
  point mass at zero charges some half-line `[a, ∞)` with `a > 0`.
* `MeasureTheory.Measure.eq_dirac_zero_of_measure_singleton_eq_one` — the degenerate case: a
  probability measure on `ℝ≥0` that gives mass one to `{0}` is the point mass at zero.
-/

public section

open scoped NNReal

open MeasureTheory Set

namespace MeasureTheory.Measure

/-- A probability measure on the half-line `ℝ≥0` that is not the point mass at zero charges some
half-line `[a, ∞)` with `a > 0`. -/
theorem exists_pos_measure_Ici {F : Measure ℝ≥0} [IsProbabilityMeasure F] (h0 : F {0} < 1) :
    ∃ a : ℝ≥0, 0 < a ∧ 0 < F (Ici a) := by
  have hcompl : ({0} : Set ℝ≥0)ᶜ = Ioi 0 := by
    ext x
    simp only [mem_compl_iff, mem_singleton_iff, mem_Ioi, pos_iff_ne_zero]
  have hunion : (⋃ k : ℕ, Ici (1 / ((k : ℝ≥0) + 1))) = Ioi 0 := by
    ext x
    simp only [mem_iUnion, mem_Ici, mem_Ioi]
    exact ⟨fun ⟨k, hk⟩ => lt_of_lt_of_le (by positivity) hk, fun hx =>
      let ⟨k, hk⟩ := exists_nat_one_div_lt hx
      ⟨k, hk.le⟩⟩
  have hpos : F (Ioi (0 : ℝ≥0)) ≠ 0 := by
    intro h
    have huniv : F univ = F {0} + F (Ioi 0) := by
      rw [← hcompl]
      exact (measure_add_measure_compl (measurableSet_singleton (0 : ℝ≥0))).symm
    rw [measure_univ, h, add_zero] at huniv
    exact h0.ne huniv.symm
  obtain ⟨k, hk⟩ := exists_measure_pos_of_not_measure_iUnion_null
    (s := fun k : ℕ => Ici (1 / ((k : ℝ≥0) + 1))) (by rw [hunion]; exact hpos)
  exact ⟨_, by positivity, hk⟩

/-- A probability measure on the half-line `ℝ≥0` that gives mass one to `{0}` is already the point
mass at zero. This is the degenerate complement of `exists_pos_measure_Ici`. -/
theorem eq_dirac_zero_of_measure_singleton_eq_one {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    (h : F {0} = 1) : F = Measure.dirac (0 : ℝ≥0) := by
  have hcompl : F ({0} : Set ℝ≥0)ᶜ = 0 := by
    rw [measure_compl (measurableSet_singleton (0 : ℝ≥0)) (measure_ne_top F _), h, measure_univ,
      tsub_self]
  have hae : ∀ᵐ x ∂F, x ∈ ({0} : Set ℝ≥0) := by
    rw [ae_iff]
    exact hcompl
  calc F = F.restrict {0} := (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ = F {0} • Measure.dirac (0 : ℝ≥0) := Measure.restrict_singleton F 0
    _ = Measure.dirac (0 : ℝ≥0) := by rw [h, one_smul]

end MeasureTheory.Measure
