/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.DiscreteLaplace.Basic
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Topological support of discrete Laplace laws

For `0 < q < 1`, the discrete Laplace law assigns positive mass to every integer. Its native
support is therefore all of `ℤ`, and its real-cast support is the integer lattice. At `q = 0`,
both supports reduce to the center; invalid parameters give empty support.

The real support is a closed discrete set, rather than the whole real line. These formulas
include all parameter values and distinguish the point-mass boundary from positive parameters.

## References

* S. Inusah and T. J. Kozubowski, *A discrete analogue of the Laplace distribution*, Journal of
  Statistical Planning and Inference 136 (2006), 1090–1102.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The native support of a discrete Laplace law is all integers for `0 < q < 1`, the singleton
center for `q = 0`, and empty for invalid parameters. -/
@[simp]
theorem support_discreteLaplaceMeasure (m : ℤ) (q : ℝ) :
    (discreteLaplaceMeasure m q).support =
      if 0 ≤ q ∧ q < 1 then if q = 0 then {m} else univ else ∅ := by
  by_cases hvalid : 0 ≤ q ∧ q < 1
  · rw [ite_eq_left hvalid]
    by_cases hq : q = 0
    · simp [hq, Measure.support_dirac]
    · rw [ite_eq_right hq, Measure.support_eq_setOf_singleton_ne_zero]
      ext k
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact (discreteLaplaceMeasure_singleton_pos m
        (lt_of_le_of_ne hvalid.1 (Ne.symm hq)) hvalid.2 k).ne'
  · simp [hvalid]

/-- The real-cast support of a discrete Laplace law is the integer lattice for `0 < q < 1`,
the singleton cast center for `q = 0`, and empty for invalid parameters. -/
@[simp]
theorem support_map_cast_discreteLaplaceMeasure (m : ℤ) (q : ℝ) :
    ((discreteLaplaceMeasure m q).map (Int.cast : ℤ → ℝ)).support =
      if 0 ≤ q ∧ q < 1 then
        if q = 0 then {(m : ℝ)} else range (Int.cast : ℤ → ℝ)
      else ∅ := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    support_discreteLaplaceMeasure]
  by_cases hvalid : 0 ≤ q ∧ q < 1
  · simp only [ite_eq_left hvalid]
    by_cases hq : q = 0
    · simp [hq]
    · simp only [ite_eq_right hq]
      rw [image_univ, Int.isClosedEmbedding_coe_real.isClosed_range.closure_eq]
  · simp [hvalid]

end TauCeti.Probability
