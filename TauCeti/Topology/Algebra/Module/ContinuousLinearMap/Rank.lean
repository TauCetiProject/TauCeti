/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Rank bounds for continuous linear maps

The rank of a continuous linear map `R` is the rank of its underlying linear map, the dimension of
its range. This file records two facts used to work with maps of bounded rank, for instance in the
infimum defining approximation numbers.

* `ContinuousLinearMap.instNonemptyRankLE`: for every cardinal `c`, some continuous linear map has
  rank at most `c`, namely the zero map.
* `ContinuousLinearMap.rank_comp_le_of_rank_le`: postcomposition preserves a rank bound by a
  natural number. The bound is a natural number so that the three spaces may lie in different
  universes.
-/

public section

namespace ContinuousLinearMap

variable {K E F G : Type*} [Semiring K]
  [TopologicalSpace E] [AddCommMonoid E] [Module K E]
  [TopologicalSpace F] [AddCommMonoid F] [Module K F]
  [TopologicalSpace G] [AddCommMonoid G] [Module K G]

/-- The continuous linear maps of rank at most `c` form a nonempty type: the zero map has
rank `0`. -/
instance instNonemptyRankLE [Nontrivial K] (c : Cardinal) :
    Nonempty {R : E →L[K] F // R.rank ≤ c} :=
  ⟨⟨0, by simp⟩⟩

/-- **Postcomposition preserves a finite rank bound.** If `R` has rank at most `n`, so does
`A ∘ R`, whatever the universes of the three spaces. -/
theorem rank_comp_le_of_rank_le (A : F →L[K] G) {R : E →L[K] F} {n : ℕ} (hR : R.rank ≤ n) :
    (A.comp R).rank ≤ n := by
  rw [toLinearMap_comp]
  exact Cardinal.lift_le_nat_iff.mp <|
    (LinearMap.lift_rank_comp_le_right _ _).trans (by simpa using hR)

end ContinuousLinearMap
