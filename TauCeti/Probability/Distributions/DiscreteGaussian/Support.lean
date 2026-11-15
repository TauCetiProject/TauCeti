/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.DiscreteGaussian.Basic

/-!
# Topological support of discrete Gaussian laws

At positive width, every integer has positive discrete Gaussian mass, so the native support is
all of `ℤ`. After casting to the reals, the support is the closed integer lattice rather than the
whole real line. At nonpositive width, the totalized law is zero and both supports are empty.

## References

* C. L. Canonne, G. Kamath and T. Steinke, *The Discrete Gaussian for Differential Privacy*,
  Advances in Cryptology -- EUROCRYPT 2020, 552--578.
* `SampCert` verifies samplers for integer Gaussian laws. The measure-theoretic development here is
  independent of its programming and privacy interfaces.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The native support of a discrete Gaussian law is all integers at positive width and empty at
nonpositive width. -/
@[simp]
theorem support_discreteGaussianMeasure (c s : ℝ) :
    (discreteGaussianMeasure c s).support = if 0 < s then univ else ∅ := by
  by_cases hs : 0 < s
  · rw [ite_eq_left hs, Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact (discreteGaussianMeasure_singleton_pos c hs k).ne'
  · simp [discreteGaussianMeasure_of_nonpos c (le_of_not_gt hs), hs]

/-- The support of a real-cast discrete Gaussian law is the integer lattice at positive width and
empty at nonpositive width. -/
@[simp]
theorem support_map_intCast_discreteGaussianMeasure (c s : ℝ) :
    ((discreteGaussianMeasure c s).map (Int.cast : ℤ → ℝ)).support =
      if 0 < s then Set.range (Int.cast : ℤ → ℝ) else ∅ := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    support_discreteGaussianMeasure]
  by_cases hs : 0 < s
  · simp only [ite_eq_left hs, image_univ]
    exact Int.isClosedEmbedding_coe_real.isClosed_range.closure_eq
  · simp [hs]

end TauCeti.Probability
