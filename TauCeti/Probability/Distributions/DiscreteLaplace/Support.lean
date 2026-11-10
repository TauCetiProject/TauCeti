/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.DiscreteLaplace.Basic

/-!
# Topological support of discrete Laplace laws

This file identifies the exact topological support of every totalized discrete Laplace law on its
native integer carrier and after casting to the reals. A positive parameter gives full integer
support, the zero parameter gives the point mass at the center, and invalid parameters give the
zero measure.

## Main results

* `TauCeti.Probability.support_discreteLaplaceMeasure` gives the native support.
* `TauCeti.Probability.support_map_intCast_discreteLaplaceMeasure` gives the support of the
  real-cast law.

## References

* S. Inusah and T. J. Kozubowski, *A discrete analogue of the Laplace distribution*, Journal of
  Statistical Planning and Inference 136 (2006), 1090--1102.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The native support of a discrete Laplace law is all integers at a positive valid parameter,
the singleton center at parameter zero, and empty at invalid parameters. -/
@[simp]
theorem support_discreteLaplaceMeasure (m : ℤ) (q : ℝ) :
    (discreteLaplaceMeasure m q).support =
      if 0 ≤ q ∧ q < 1 then if q = 0 then {m} else univ else ∅ := by
  by_cases hvalid : 0 ≤ q ∧ q < 1
  · rw [ite_eq_left hvalid]
    by_cases hq : q = 0
    · subst q
      simp
    · rw [ite_eq_right hq, Measure.support_eq_setOf_singleton_ne_zero]
      ext k
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact (discreteLaplaceMeasure_singleton_pos m (lt_of_le_of_ne hvalid.1 (Ne.symm hq))
        hvalid.2 k).ne'
  · simp [hvalid, discreteLaplaceMeasure_eq_zero_of_invalid]

/-- The support of a real-cast discrete Laplace law is the integer lattice at a positive valid
parameter, the singleton cast center at parameter zero, and empty at invalid parameters. -/
@[simp]
theorem support_map_intCast_discreteLaplaceMeasure (m : ℤ) (q : ℝ) :
    ((discreteLaplaceMeasure m q).map (Int.cast : ℤ → ℝ)).support =
      if 0 ≤ q ∧ q < 1 then
        if q = 0 then {(m : ℝ)} else Set.range (Int.cast : ℤ → ℝ)
      else ∅ := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    support_discreteLaplaceMeasure]
  by_cases hvalid : 0 ≤ q ∧ q < 1
  · simp only [ite_eq_left hvalid]
    by_cases hq : q = 0
    · subst q
      simp
    · simp only [ite_eq_right hq, image_univ]
      exact Int.isClosedEmbedding_coe_real.isClosed_range.closure_eq
  · simp [hvalid]

end TauCeti.Probability
