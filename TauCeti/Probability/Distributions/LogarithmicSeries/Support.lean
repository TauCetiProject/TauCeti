/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.LogarithmicSeries.Basic

/-!
# Topological support of logarithmic-series laws

For `0 < q < 1`, the logarithmic-series law has topological support exactly the positive
natural numbers. After casting to the reals, its support is the closed discrete set of positive
integers. In particular, neither zero nor any noninteger is a support point. Invalid parameters
give the zero measure and empty support on both carriers.

## References

* N. L. Johnson, A. W. Kemp, and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The native topological support of a logarithmic-series law is the positive natural numbers
for `0 < q < 1`, and empty otherwise. -/
@[simp]
theorem support_logarithmicSeriesMeasure (q : ℝ) :
    (logarithmicSeriesMeasure q).support = if 0 < q ∧ q < 1 then Ioi 0 else ∅ := by
  by_cases hq : 0 < q ∧ q < 1
  · rw [ite_eq_left hq, Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    simp only [mem_ofPred_eq, logarithmicSeriesMeasure_singleton_ne_zero_iff hq.1 hq.2,
      mem_Ioi, Nat.pos_iff_ne_zero]
  · simp [hq]

/-- The real-cast topological support of a logarithmic-series law is the positive integer
lattice for `0 < q < 1`, and empty otherwise. -/
@[simp]
theorem support_map_cast_logarithmicSeriesMeasure (q : ℝ) :
    ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)).support =
      if 0 < q ∧ q < 1 then (Nat.cast : ℕ → ℝ) '' Ioi 0 else ∅ := by
  by_cases hq : 0 < q ∧ q < 1
  · rw [ite_eq_left hq,
      Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
      support_logarithmicSeriesMeasure, ite_eq_left hq]
    exact (Nat.isClosedEmbedding_coe_real.isClosedMap _ (isClosed_discrete _)).closure_eq
  · simp [hq]

end TauCeti.Probability
