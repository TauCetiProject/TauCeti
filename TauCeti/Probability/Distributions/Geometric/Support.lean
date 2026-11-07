/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.Geometric.Basic

/-!
# Support of the geometric distribution

This file identifies the topological support of the geometric distribution, both on its native
natural-number carrier and after casting to the reals. For a success probability strictly between
zero and one, every natural number has positive mass. At either endpoint, the law is concentrated
at zero.

## Main results

* `support_geometricMeasure` gives the exact support on `ℕ`.
* `support_map_cast_geometricMeasure` gives the exact support after casting to `ℝ`.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The exact topological support of a geometric law on its native natural-number carrier.
The zero parameter is Mathlib's totalized Dirac law, while success probability one is the usual
degenerate geometric law. -/
@[simp]
theorem support_geometricMeasure (p : unitInterval) :
    (geometricMeasure p).support = if p = 0 ∨ p = 1 then {0} else Set.univ := by
  by_cases hp0 : p = 0
  · subst p
    simp [geometricMeasure_zero, Measure.support_dirac]
  by_cases hp1 : p = 1
  · subst p
    simp [Measure.support_dirac]
  rw [ite_eq_right (not_or_intro hp0 hp1)]
  ext n
  simp only [mem_univ, iff_true, Measure.mem_support_iff_forall]
  intro U hU
  refine (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU))).trans_lt' ?_
  rw [geometricMeasure_singleton hp0, ENNReal.ofReal_pos]
  exact geometricMeasure_pos hp0 hp1 n

/-- The exact topological support of a real-cast geometric law. For an interior success
probability it is the closed set of nonnegative integers; at either endpoint it is the singleton
zero. -/
@[simp]
theorem support_map_cast_geometricMeasure (p : unitInterval) :
    ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)).support =
      if p = 0 ∨ p = 1 then {0} else Set.range (Nat.cast : ℕ → ℝ) := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    support_geometricMeasure]
  split_ifs with hp
  · simp
  · rw [image_univ, Nat.isClosedEmbedding_coe_real.isClosed_range.closure_eq]

end TauCeti.Probability
