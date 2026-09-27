/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Data.Fintype.Order

/-!
# Orthogonality for the additive valuation of a discrete valuation ring

A finite sum of elements with pairwise distinct finite additive valuations has valuation equal to
the least valuation of its terms.  Zero terms cause no exception: their additive valuation is
`⊤`, so the same formula also covers the identically zero family.

This is the elementary nonarchimedean orthogonality principle used for power bases whose terms
have valuations in distinct congruence classes.
-/

public section

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The additive valuation of a sum of terms with pairwise distinct finite valuations is the
infimum of their valuations. -/
theorem addVal_sum_eq_iInf_of_ne {ι : Type*} [Fintype ι]
    (a : ι → R) (h : ∀ i j, i ≠ j → a i ≠ 0 → a j ≠ 0 → addVal R (a i) ≠ addVal R (a j)) :
    addVal R (∑ i, a i) = ⨅ i, addVal R (a i) := by
  classical
  let s : Finset ι := Finset.univ.filter fun i ↦ a i ≠ 0
  by_cases hs : s.Nonempty
  · obtain ⟨j, hj, hjmin⟩ := s.exists_min_image (fun i ↦ addVal R (a i)) hs
    have haj : a j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hlt : ∀ i ∈ s \ {j},
        (addVal R).toValuation (a i) < (addVal R).toValuation (a j) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      have hai : a i ≠ 0 := (Finset.mem_filter.mp hi.1).2
      have hle : addVal R (a j) ≤ addVal R (a i) := hjmin i hi.1
      have hlt' : addVal R (a j) < addVal R (a i) :=
        lt_of_le_of_ne hle (h i j hi.2 hai haj).symm
      exact hlt'.dual
    have hsum := (addVal R).toValuation.map_sum_eq_of_lt hj hlt
    have hsum' : (∑ i ∈ s, a i) = ∑ i, a i := by
      simp only [s, Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ ↦ by
        by_cases hai : a i = 0 <;> simp [hai]
    have hmin : (⨅ i, addVal R (a i)) = addVal R (a j) := by
      apply le_antisymm
      · exact iInf_le _ j
      · refine le_iInf fun i ↦ ?_
        by_cases hai : a i = 0
        · simp [hai]
        · exact hjmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hai⟩)
    rw [hsum'] at hsum
    exact hsum.trans hmin.symm
  · have ha : ∀ i, a i = 0 := by
      intro i
      by_contra hai
      exact hs ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hai⟩⟩
    simp [ha]

end IsDiscreteValuationRing
