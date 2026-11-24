/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.Length.Lipschitz
public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compact closed balls in incomplete length spaces

In a locally compact length space, a closed ball which is complete is compact. This is the
local form of the Hopf–Rinow–Cohn-Vossen theorem: the radii of compact closed balls about a
point form an interval containing `0`; it is open because a compact set has a compact uniform
thickening and every point of a slightly larger ball is close to the smaller ball, and it is
closed because the larger ball is then totally bounded.

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
* `TauCeti.isComplete_closedBall_of_ofReal_lt_infEDist_compl_range_coe`: a closed ball whose
  radius is less than the extended distance from its center to the ideal boundary of the
  completion is complete.
* `TauCeti.IsLengthSpace.isCompact_closedBall_of_ofReal_lt_infEDist_compl_range_coe`: such a
  closed ball is compact.
* `TauCeti.infEDist_compl_range_coe_eq_top`: the extended distance to the ideal boundary of a
  complete space is `⊤`.

## References

* D. Burago, Y. Burago, and S. Ivanov, *A Course in Metric Geometry*, AMS, 2001,
  Proposition 2.5.22.
-/

public section

open Filter Metric Set
open scoped NNReal Topology unitInterval

namespace TauCeti

variable {X : Type*} [MetricSpace X]

/-- In a length space, a point at distance at most `s + t` from `p` lies within `t + ε` of a
point at distance at most `s` from `p`. -/
theorem IsLengthSpace.exists_dist_le_of_dist_le_add [IsLengthSpace X] {p x : X} {s t ε : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hε : 0 < ε) (hx : dist p x ≤ s + t) :
    ∃ y, dist p y ≤ s ∧ dist y x ≤ t + ε := by
  by_cases hxs : dist p x ≤ s
  · exact ⟨x, hxs, by rw [dist_self]; positivity⟩
  rw [not_le] at hxs
  set r := dist p x + ε with _hr_def
  have hr : 0 < r := by positivity
  obtain ⟨f, hf0, hf1, hf⟩ := IsLengthSpace.exists_lipschitz_path (x := p) (y := x)
    (r := r) (by linarith)
  have hsr : s / r ≤ 1 := (div_le_one hr).2 (by linarith)
  let τ : unitInterval := ⟨s / r, div_nonneg hs hr.le, hsr⟩
  have hK : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr.le
  refine ⟨f τ, ?_, ?_⟩
  · have h := hf.dist_le_mul 0 τ
    rw [hf0, hK, Subtype.dist_eq, Real.dist_eq] at h
    have hτ : |((0 : unitInterval) : ℝ) - (τ : ℝ)| = s / r := by
      simp only [Icc.coe_zero, zero_sub, abs_neg, τ]
      exact abs_of_nonneg (div_nonneg hs hr.le)
    rw [hτ, mul_div_cancel₀ _ hr.ne'] at h
    exact h
  · have h := hf.dist_le_mul τ 1
    rw [hf1, hK, Subtype.dist_eq, Real.dist_eq] at h
    have hτ : |(τ : ℝ) - ((1 : unitInterval) : ℝ)| = 1 - s / r := by
      simp only [Icc.coe_one, τ]
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [hτ, mul_sub, mul_one, mul_div_cancel₀ _ hr.ne'] at h
    linarith

variable [IsLengthSpace X]

/-- In a locally compact length space, a compact closed ball of nonnegative radius is contained
in a compact closed ball of strictly larger radius. -/
theorem IsLengthSpace.exists_isCompact_closedBall_add [LocallyCompactSpace X] {p : X} {s : ℝ}
    (hs : 0 ≤ s) (hK : IsCompact (closedBall p s)) :
    ∃ δ > 0, IsCompact (closedBall p (s + δ)) := by
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
  have hcomplete {s : ℝ} (hs : s ≤ R) : IsComplete (closedBall p s) := by
    intro f hf hfs
    obtain ⟨y, -, hfy⟩ := hR f hf (hfs.trans (principal_mono.2 (closedBall_subset_closedBall hs)))
    have := hf.1
    exact ⟨y, isClosed_closedBall.mem_of_tendsto hfy (le_principal_iff.1 hfs), hfy⟩
  let A : Set ℝ := {s | 0 ≤ s ∧ s ≤ R ∧ IsCompact (closedBall p s)}
  have hA0 : (0 : ℝ) ∈ A := ⟨le_rfl, hR0, by rw [closedBall_zero]; exact isCompact_singleton⟩
  have hAbdd : BddAbove A := ⟨R, fun s hs ↦ hs.2.1⟩
  set S := sSup A
  have hS0 : 0 ≤ S := le_csSup hAbdd hA0
  have hSR : S ≤ R := csSup_le ⟨0, hA0⟩ fun s hs ↦ hs.2.1
  have hSK : IsCompact (closedBall p S) := by
    rw [isCompact_iff_totallyBounded_isComplete]
    refine ⟨totallyBounded_closedBall_of_forall_lt fun s hs ↦ ?_, hcomplete hSR⟩
    obtain ⟨a, ha, hsa⟩ := exists_lt_of_lt_csSup ⟨0, hA0⟩ hs
    exact ha.2.2.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hsa.le)
  rcases hSR.eq_or_lt with hSR | hSR
  · rwa [← hSR]
  obtain ⟨δ, hδ, hKδ⟩ := exists_isCompact_closedBall_add hS0 hSK
  have hmem : min (S + δ) R ∈ A :=
    ⟨le_min (by linarith) hR0, min_le_right _ _, hKδ.of_isClosed_subset isClosed_closedBall
      (closedBall_subset_closedBall (min_le_left _ _))⟩
  have := le_csSup hAbdd hmem
  rcases min_cases (S + δ) R with h | h <;> linarith [h.1]

/-- **Hopf–Rinow–Cohn-Vossen.** A complete locally compact length space is proper. -/
theorem IsLengthSpace.properSpace_of_completeSpace [CompleteSpace X] [LocallyCompactSpace X] :
    ProperSpace X :=
  ⟨fun _ _ ↦ isCompact_closedBall_of_isComplete isClosed_closedBall.isComplete⟩

omit [IsLengthSpace X] in
/-- A closed ball whose radius is less than the extended distance, in the completion, from its
center to the points of the completion outside the space, is complete. When the space is
complete this set is empty, its extended distance is `⊤`, and every closed ball is complete. -/
theorem isComplete_closedBall_of_ofReal_lt_infEDist_compl_range_coe {p : X} {R : ℝ}
    (hR : ENNReal.ofReal R < infEDist (p : UniformSpace.Completion X)
      (range ((↑) : X → UniformSpace.Completion X))ᶜ) :
    IsComplete (closedBall p R) := by
  intro f hf hfs
  have := hf.1
  obtain ⟨z, hz⟩ :=
    CompleteSpace.complete (hf.map (UniformSpace.Completion.uniformContinuous_coe X))
  have hzR : dist (p : UniformSpace.Completion X) z ≤ R := by
    rw [dist_comm, ← mem_closedBall]
    refine isClosed_closedBall.mem_of_tendsto hz ?_
    filter_upwards [le_principal_iff.1 hfs] with x hx
    rw [mem_closedBall, UniformSpace.Completion.dist_eq]
    exact hx
  obtain ⟨y, rfl⟩ : z ∈ range ((↑) : X → UniformSpace.Completion X) := by
    by_contra hz'
    exact (infEDist_le_edist_of_mem hz').not_gt
      (((edist_le_ofReal (dist_nonneg.trans hzR)).2 hzR).trans_lt hR)
  have hfy : f ≤ 𝓝 y := tendsto_id'.1 <|
    ((UniformSpace.Completion.isUniformEmbedding_coe X).isInducing.tendsto_nhds_iff
      (f := id)).2 hz
  exact ⟨y, isClosed_closedBall.mem_of_tendsto hfy (le_principal_iff.1 hfs), hfy⟩

/-- In a locally compact length space, a closed ball whose radius is less than the extended
distance, in the completion, from its center to the ideal boundary is compact. -/
theorem IsLengthSpace.isCompact_closedBall_of_ofReal_lt_infEDist_compl_range_coe
    [LocallyCompactSpace X] {p : X} {R : ℝ}
    (hR : ENNReal.ofReal R < infEDist (p : UniformSpace.Completion X)
      (range ((↑) : X → UniformSpace.Completion X))ᶜ) :
    IsCompact (closedBall p R) :=
  isCompact_closedBall_of_isComplete
    (isComplete_closedBall_of_ofReal_lt_infEDist_compl_range_coe hR)

/-- A complete space has no ideal boundary: every point of its completion comes from the
space. -/
theorem range_coe_completion_eq_univ {α : Type*} [UniformSpace α] [CompleteSpace α] :
    range ((↑) : α → UniformSpace.Completion α) = univ := by
  rw [← (UniformSpace.Completion.isUniformInducing_coe α).isComplete_range.isClosed.closure_eq]
  exact UniformSpace.Completion.denseRange_coe.closure_range

/-- The extended distance to the ideal boundary of a complete space is `⊤`, whereas the
real-valued distance `Metric.infDist` to it is `0`. -/
@[simp]
theorem infEDist_compl_range_coe_eq_top {α : Type*} [PseudoMetricSpace α] [CompleteSpace α]
    (x : UniformSpace.Completion α) :
    infEDist x (range ((↑) : α → UniformSpace.Completion α))ᶜ = ⊤ := by
  rw [range_coe_completion_eq_univ, compl_univ, infEDist_empty]

/-- A closed ball about `p` of radius less than `ρ` is contained in `s` as soon as `ρ` is at
most the extended distance from `p` to the complement of `s`. When the complement is empty its
extended distance is `⊤` and there is no condition on `ρ`. -/
theorem closedBall_subset_of_lt_of_ofReal_le_infEDist_compl {α : Type*} [PseudoMetricSpace α]
    {s : Set α} {p : α} {ρ R : ℝ} (hR : R < ρ) (hρ : ENNReal.ofReal ρ ≤ infEDist p sᶜ) :
    closedBall p R ⊆ s := by
  intro y hy
  rw [mem_closedBall'] at hy
  by_contra hys
  refine (((infEDist_le_edist_of_mem hys).trans ?_).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (dist_nonneg.trans hy)).2 hR)).not_ge hρ
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal hy

end TauCeti
