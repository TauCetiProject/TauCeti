/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Topological support of the Poisson distribution

A positive-rate Poisson law has positive mass at every natural number, while the zero-rate law is
concentrated at zero. This file identifies the exact native support and the support after casting
the counts to real numbers.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- A Poisson singleton has nonzero mass exactly when the rate is positive or the count is zero. -/
theorem poissonMeasure_singleton_ne_zero_iff (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r {n} ≠ 0 ↔ r ≠ 0 ∨ n = 0 := by
  by_cases hr : r = 0
  · subst r
    cases n <;> simp [poissonMeasure_zero]
  · rw [poissonMeasure_singleton, ENNReal.ofReal_ne_zero_iff]
    constructor
    · exact fun _ ↦ Or.inl hr
    · intro _
      positivity

/-- The support of a Poisson law is the whole of `ℕ` at positive rate and the singleton zero at
rate zero. -/
@[simp]
theorem support_poissonMeasure (r : ℝ≥0) :
    (poissonMeasure r).support = if r = 0 then {0} else Set.univ := by
  by_cases hr : r = 0
  · subst r
    simp [poissonMeasure_zero]
  · simp only [hr, ↓reduceIte]
    ext n
    simp only [mem_univ, iff_true, Measure.mem_support_iff_forall]
    intro U hU
    exact
      (pos_iff_ne_zero.mpr
        ((poissonMeasure_singleton_ne_zero_iff r n).mpr (Or.inl hr))).trans_le
          (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

/-- The support of a real-valued Poisson law is the nonnegative integers at positive rate and the
singleton zero at rate zero. -/
@[simp]
theorem support_map_cast_poissonMeasure (r : ℝ≥0) :
    Po(ℝ, r).support = if r = 0 then {0} else Set.range (Nat.cast : ℕ → ℝ) := by
  by_cases hr : r = 0
  · subst r
    simp [poissonMeasure_zero]
  · simp only [hr, ↓reduceIte]
    rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
      support_poissonMeasure]
    simp only [hr, ↓reduceIte, image_univ]
    exact Nat.isClosedEmbedding_coe_real.isClosed_range.closure_eq

end TauCeti.Probability
