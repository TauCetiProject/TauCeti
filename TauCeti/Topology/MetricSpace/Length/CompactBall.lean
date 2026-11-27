/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.Length.Lipschitz
public import TauCeti.Topology.MetricSpace.Completion
public import TauCeti.Topology.UniformSpace.Complete
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compact closed balls in incomplete length spaces

In a locally compact length space, a closed ball which is complete is compact. This is the
local form of the Hopf–Rinow–Cohn-Vossen theorem. A compact closed ball admits a slightly larger
compact closed ball because compact sets have compact uniform thickenings and length-space
paths approximate distances. Compactness at every smaller radius gives total boundedness at a
limiting radius; completeness of the containing ball supplies completeness there, hence
compactness.

No completeness of the whole space is assumed. In particular, a closed ball whose radius is
less than the distance, in the completion, from its center to the ideal boundary (the points of
the completion which are not in the space) is compact.

The distance to the ideal boundary is the extended distance `Metric.infEDist`, with values in
`ℝ≥0∞`. When the space is complete the ideal boundary is empty and its extended distance is `⊤`,
so the condition on the radius is empty and every closed ball is compact. The real-valued
`Metric.infDist` is `0` on the empty set and would allow no positive radius in that case.

## Main results

* `TauCeti.IsLengthSpace.isCompact_closedBall_of_isComplete`: a complete closed ball in a
  locally compact length space is compact.
* `TauCeti.IsLengthSpace.properSpace_of_completeSpace`: the Hopf–Rinow–Cohn-Vossen theorem, a
  complete locally compact length space is proper.
* `TauCeti.IsLengthSpace.isCompact_closedBall_of_ofReal_lt_infEDist_compl_range_coe`: a closed
  ball whose radius is less than the extended distance from its center to the ideal boundary
  of the completion is compact.

## References

* D. Burago, Y. Burago, and S. Ivanov, *A Course in Metric Geometry*, AMS, 2001,
  Proposition 2.5.22.
* Riccardo Brasca, *ColdingMinicozziTheory*: the
  [complete-ball proof](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/afd6c6c8),
  [properness corollary](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/4b2f398b),
  and [extended-distance formulation](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/cec8d447).
-/

public section

open Filter Metric Set
open scoped NNReal Topology unitInterval

namespace TauCeti

variable {X : Type*} [MetricSpace X]

variable [IsLengthSpace X]

/-- In a locally compact length space, a compact closed ball is contained
in a compact closed ball of strictly larger radius. -/
theorem IsLengthSpace.exists_isCompact_closedBall_add [LocallyCompactSpace X] {p : X} {s : ℝ}
    (hK : IsCompact (closedBall p s)) :
    ∃ δ > 0, IsCompact (closedBall p (s + δ)) := by
  rcases lt_or_ge s 0 with hs | hs
  · refine ⟨-s / 2, by linarith, ?_⟩
    rw [closedBall_eq_empty.2 (by linarith)]
    exact isCompact_empty
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_isCompact_cthickening
  refine ⟨δ / 2, half_pos hδ, hKδ.of_isClosed_subset isClosed_closedBall ?_⟩
  intro x hx
  rw [mem_closedBall, dist_comm] at hx
  obtain ⟨y, hy, hyx⟩ :=
    exists_dist_le_of_dist_le_add hs (half_pos hδ).le (half_pos hδ) hx
  exact mem_cthickening_of_dist_le x y δ _ (by rwa [mem_closedBall, dist_comm])
    (by rw [dist_comm]; linarith)

/-- In a length space, if every closed ball of radius less than `t` about `p` is compact, then
the closed ball of radius `t` is totally bounded. -/
theorem IsLengthSpace.totallyBounded_closedBall_of_forall_lt {p : X} {t : ℝ}
    (hK : ∀ s < t, IsCompact (closedBall p s)) : TotallyBounded (closedBall p t) := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [closedBall_eq_empty.2 ht]
    exact totallyBounded_empty
  rcases ht.eq_or_lt with rfl | ht
  · rw [closedBall_zero]
    exact (finite_singleton p).totallyBounded
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set η := min (ε / 2) t
  have hη : 0 < η := lt_min (half_pos hε) ht
  obtain ⟨T, hT, hcover⟩ := Metric.totallyBounded_iff.1
    (hK (t - η) (by linarith)).totallyBounded (ε / 4) (by positivity)
  refine ⟨T, hT, fun x hx ↦ ?_⟩
  rw [mem_closedBall, dist_comm] at hx
  obtain ⟨y, hy, hyx⟩ := exists_dist_le_of_dist_le_add (sub_nonneg.2 (min_le_right _ _))
    hη.le (by positivity : 0 < ε / 8) (by linarith : dist p x ≤ t - η + η)
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hcover (by rwa [mem_closedBall, dist_comm]))
  refine mem_iUnion₂.2 ⟨z, hz, ?_⟩
  rw [mem_ball] at hyz ⊢
  have hηε : η ≤ ε / 2 := min_le_left _ _
  calc dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
    _ < ε := by rw [dist_comm] at hyx; linarith

/-- **Hopf–Rinow–Cohn-Vossen, local form.** In a locally compact length space, a closed ball
which is complete is compact. -/
theorem IsLengthSpace.isCompact_closedBall_of_isComplete [LocallyCompactSpace X] {p : X}
    {R : ℝ} (hR : IsComplete (closedBall p R)) : IsCompact (closedBall p R) := by
  rcases lt_or_ge R 0 with hR0 | hR0
  · rw [closedBall_eq_empty.2 hR0]
    exact isCompact_empty
  let A : Set ℝ := {s | 0 ≤ s ∧ s ≤ R ∧ IsCompact (closedBall p s)}
  have hA0 : (0 : ℝ) ∈ A := ⟨le_rfl, hR0, by rw [closedBall_zero]; exact isCompact_singleton⟩
  have hAbdd : BddAbove A := ⟨R, fun s hs ↦ hs.2.1⟩
  set S := sSup A
  have hS0 : 0 ≤ S := le_csSup hAbdd hA0
  have hSR : S ≤ R := csSup_le ⟨0, hA0⟩ fun s hs ↦ hs.2.1
  have hSK : IsCompact (closedBall p S) := by
    rw [isCompact_iff_totallyBounded_isComplete]
    refine ⟨totallyBounded_closedBall_of_forall_lt fun s hs ↦ ?_,
      hR.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hSR)⟩
    obtain ⟨a, ha, hsa⟩ := exists_lt_of_lt_csSup ⟨0, hA0⟩ hs
    exact ha.2.2.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hsa.le)
  rcases hSR.eq_or_lt with hSR | hSR
  · rwa [← hSR]
  obtain ⟨δ, hδ, hKδ⟩ := exists_isCompact_closedBall_add hSK
  have hmem : min (S + δ) R ∈ A :=
    ⟨le_min (by linarith) hR0, min_le_right _ _, hKδ.of_isClosed_subset isClosed_closedBall
      (closedBall_subset_closedBall (min_le_left _ _))⟩
  have := le_csSup hAbdd hmem
  rcases min_cases (S + δ) R with h | h <;> linarith [h.1]

/-- **Hopf–Rinow–Cohn-Vossen.** A complete locally compact length space is proper. -/
theorem IsLengthSpace.properSpace_of_completeSpace [CompleteSpace X] [LocallyCompactSpace X] :
    ProperSpace X :=
  ⟨fun _ _ ↦ isCompact_closedBall_of_isComplete isClosed_closedBall.isComplete⟩

/-- In a locally compact length space, a closed ball whose radius is less than the extended
distance, in the completion, from its center to the ideal boundary is compact. -/
theorem IsLengthSpace.isCompact_closedBall_of_ofReal_lt_infEDist_compl_range_coe
    [LocallyCompactSpace X] {p : X} {R : ℝ}
    (hR : ENNReal.ofReal R < infEDist (p : UniformSpace.Completion X)
      (range ((↑) : X → UniformSpace.Completion X))ᶜ) :
    IsCompact (closedBall p R) :=
  isCompact_closedBall_of_isComplete
    (isComplete_closedBall_of_ofReal_lt_infEDist_compl_range_coe hR)

end TauCeti
