/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.YuleSimon.Basic

/-!
# Topological support of Yule–Simon laws

For positive shape, the Yule–Simon law has topological support exactly the positive natural
numbers. After casting to the reals, its support is the closed discrete set of positive integers,
not the whole half-line. Nonpositive shapes give the zero measure and empty support.

## References

* N. L. Johnson, A. W. Kemp, and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Section 6.10.3.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The native topological support is the positive natural numbers for positive shape,
and empty for nonpositive shape. -/
@[simp]
theorem support_yuleSimonMeasure (ρ : ℝ) :
    (yuleSimonMeasure ρ).support = if 0 < ρ then Ioi 0 else ∅ := by
  by_cases hρ : 0 < ρ
  · rw [ite_eq_left hρ]
    refine Subset.antisymm
      (Measure.support_subset_of_isClosed (isClosed_discrete _) (ae_pos_yuleSimonMeasure ρ)) ?_
    intro k hk
    rw [Measure.mem_support_iff_forall]
    intro U hU
    exact (pos_iff_ne_zero.mpr
      ((yuleSimonMeasure_singleton_ne_zero_iff hρ k).mpr (Nat.ne_of_gt hk))).trans_le
        (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))
  · simp [yuleSimonMeasure_of_nonpos (le_of_not_gt hρ), hρ]

/-- The real-cast topological support is the set of positive integers for positive shape,
and empty for nonpositive shape. In particular, zero is not a support point. -/
@[simp]
theorem support_map_cast_yuleSimonMeasure (ρ : ℝ) :
    ((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)).support =
      if 0 < ρ then (Nat.cast : ℕ → ℝ) '' Ioi 0 else ∅ := by
  by_cases hρ : 0 < ρ
  · rw [ite_eq_left hρ,
      Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
      support_yuleSimonMeasure, ite_eq_left hρ]
    exact (Nat.isClosedEmbedding_coe_real.isClosedMap _ (isClosed_discrete _)).closure_eq
  · simp [yuleSimonMeasure_of_nonpos (le_of_not_gt hρ), hρ]

end TauCeti.Probability
