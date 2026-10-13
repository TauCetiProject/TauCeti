/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.NestedDiscPoint

/-!
# Closed intersections of discs

The rational subset `closedSubdisc a c` is open in the adic unit disc, despite its name.
Its closure can contain points just outside its boundary. Enlarging its radius strictly
contains that closure. Consequently, an intersection of discs is closed whenever each
disc admits a strictly smaller disc of the family inside it.

For a decreasing sequence of discs with no common point in the ground field, every disc
admits such a refinement. The resulting closed intersection contains the attached
`nestedDiscPoint` and all its specializations. Identifying the intersection with a singleton
then proves that the point of type (4) is closed. The closed-intersection theorem itself
requires neither completeness nor algebraic closedness of the ground field.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Example 7.57.
* V. G. Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, §1.4.4.
-/

public section

namespace TauCeti.ValuationSpectrum

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]

/-- An intersection of discs is closed if each disc contains a disc of the family with
strictly smaller radius. The centres may vary, and the family need not be a sequence. -/
theorem isClosed_iInter_closedSubdisc {ι : Sort*} (a c : ι → K)
    (hrefine : ∀ i, ∃ j, ‖a j - a i‖ ≤ ‖c i‖ ∧ ‖c j‖ < ‖c i‖) :
    IsClosed (⋂ i, closedSubdisc (a i) (c i)) := by
  refine isClosed_of_closure_subset fun x hx ↦ Set.mem_iInter.mpr fun i ↦ ?_
  obtain ⟨j, hji, hrad⟩ := hrefine i
  exact closedSubdisc_subset_closedSubdisc hji le_rfl
    (closure_closedSubdisc_subset_closedSubdisc hrad
      (closure_mono (Set.iInter_subset _ j) hx))

/-- A decreasing sequence of discs with no common point in the ground field has closed
intersection in the adic unit disc. Its adic intersection need not be empty. -/
theorem isClosed_iInter_closedSubdisc_of_no_common_point (a c : ℕ → K)
    (hac : ∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖)
    (hcc : ∀ n, ‖c (n + 1)‖ ≤ ‖c n‖)
    (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) :
    IsClosed (⋂ n, closedSubdisc (a n) (c n)) := by
  -- Use classical closed balls to extract strict refinements, without Gauss points or
  -- completeness. In an ultrametric space every point of a ball is also a centre.
  have hanti : Antitone fun n ↦ Metric.closedBall (a n) ‖c n‖ :=
    antitone_nat_of_succ_le fun n ↦ by
      rw [IsUltrametricDist.closedBall_eq_of_mem (x := a n) (y := a (n + 1))
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hac n)]
      exact Metric.closedBall_subset_closedBall (hcc n)
  apply isClosed_iInter_closedSubdisc
  intro n
  obtain ⟨m, hm⟩ := hempty (a n)
  have hnm : n ≤ m := by
    by_contra! hmn
    have h := hanti hmn.le (Metric.mem_closedBall_self (norm_nonneg (c n)))
    exact hm.not_ge (by simpa only [Metric.mem_closedBall, dist_eq_norm] using h)
  have h := hanti hnm (Metric.mem_closedBall_self (norm_nonneg (c m)))
  have hdist : ‖a m - a n‖ ≤ ‖c n‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using h
  exact ⟨m, hdist, hm.trans_le (by simpa only [norm_sub_rev] using hdist)⟩

end NormedField

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NonarchimedeanRing K] [CompleteSpace K]

/-- Every specialization of a nested-disc point with no common field-valued centre remains
in every defining disc. Thus recognition of that intersection as a singleton proves closedness
of the point of type (4). -/
theorem mem_closedSubdisc_of_nestedDiscPoint_specializes (a c : ℕ → K)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hc₀ : ∀ n, c n ≠ 0) (hc₁ : ∀ n, ‖c n‖ ≤ 1)
    (hac : ∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖)
    (hcc : ∀ n, ‖c (n + 1)‖ ≤ ‖c n‖)
    (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) {x : closedPolydisc 1 K}
    (hx : nestedDiscPoint a ha c hc₀ hc₁ hac hcc ⤳ x) (n : ℕ) :
    x ∈ closedSubdisc (a n) (c n) := by
  have hclosed := isClosed_iInter_closedSubdisc_of_no_common_point a c hac hcc hempty
  exact Set.mem_iInter.mp (hx.mem_closed hclosed (Set.mem_iInter.mpr
    (nestedDiscPoint_mem_closedSubdisc a ha c hc₀ hc₁ hac hcc))) n

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
