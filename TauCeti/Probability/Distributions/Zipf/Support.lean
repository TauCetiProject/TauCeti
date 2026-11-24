/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Zipf.Finite
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of Zipf laws

The infinite Zipf law has topological support exactly the positive natural numbers when its
exponent exceeds one, and empty support otherwise. After casting to the reals, its support is
the closed discrete set of positive integers. The finite Zipf law similarly has real support
exactly the integers from one to its cutoff, including empty support at cutoff zero.

The support identities use the native singleton masses and
`MeasureTheory.Measure.support_map_eq_closure_image`. Closedness of the natural-number
embedding ensures that casting introduces no additional support points.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The native topological support of the infinite Zipf law is the positive naturals for
`s > 1`. Invalid exponents give empty support. -/
@[simp]
theorem support_zipfMeasure (s : ℝ) :
    (zipfMeasure s).support = if 1 < s then Ioi 0 else ∅ := by
  by_cases hs : 1 < s
  · rw [ite_eq_left hs, Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    simpa only [mem_ofPred_eq, mem_Ioi, Nat.pos_iff_ne_zero] using
      zipfMeasure_singleton_ne_zero_iff hs k
  · simp [zipfMeasure_of_le_one (le_of_not_gt hs), hs]

/-- The real-cast infinite Zipf law has support exactly the positive integers for `s > 1`,
and empty support for invalid exponents. -/
@[simp]
theorem support_map_cast_zipfMeasure (s : ℝ) :
    ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)).support =
      if 1 < s then (Nat.cast : ℕ → ℝ) '' Ioi 0 else ∅ := by
  by_cases hs : 1 < s
  · rw [ite_eq_left hs,
      Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
      support_zipfMeasure, ite_eq_left hs]
    exact (Nat.isClosedEmbedding_coe_real.isClosedMap _ (isClosed_discrete _)).closure_eq
  · simp [zipfMeasure_of_le_one (le_of_not_gt hs), hs]

/-- The real-cast finite Zipf law has support exactly the natural integers from one to `N`,
for every real exponent. At `N = 0` this image is empty. -/
@[simp]
theorem support_map_cast_finiteZipfMeasure (N : ℕ) (s : ℝ) :
    ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)).support =
      (Nat.cast : ℕ → ℝ) '' Icc 1 N := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    support_finiteZipfMeasure]
  exact (Nat.isClosedEmbedding_coe_real.isClosedMap _ (isClosed_discrete _)).closure_eq

end TauCeti.Probability
