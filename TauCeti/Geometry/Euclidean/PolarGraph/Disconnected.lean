/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.PolarGraph.Descent

/-!
# Failures of adjacent-sheet tests on disconnected polar domains

Two narrow annular sectors separated by two turns have no one-turn overlap. A constant height
still fails injectivity, and distinct constant heights on the two sectors fail descent.
-/

public noncomputable section

namespace TauCeti.PolarGraph

open Real

/-- Two annular sectors whose angular intervals differ by two full turns. -/
def twoStripDomain : Set PolarPoint :=
  {p | radius p ∈ Set.Ioo 1 2 ∧
    (angle p ∈ Set.Ioo 0 (π / 4) ∨ angle p ∈ Set.Ioo (4 * π) (4 * π + π / 4))}

theorem mem_twoStripDomain_iff {p : PolarPoint} :
    p ∈ twoStripDomain ↔ radius p ∈ Set.Ioo 1 2 ∧
      (angle p ∈ Set.Ioo 0 (π / 4) ∨ angle p ∈ Set.Ioo (4 * π) (4 * π + π / 4)) :=
  Iff.rfl

/-- Neither angular strip meets a one-turn translate of either strip. -/
theorem overlap_twoStripDomain_one : overlap twoStripDomain 1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨⟨_, h₁⟩, _, h₂⟩ := (mem_overlap_iff.trans
    (and_congr mem_twoStripDomain_iff mem_twoStripDomain_iff)).mp hp
  simp only [angle_deckShift, Int.cast_one, one_mul, Set.mem_Ioo] at h₁ h₂
  rcases h₁ with h | h <;> rcases h₂ with h' | h' <;> linarith [pi_pos, h.1, h.2, h'.1, h'.2]

/-- The two-turn overlap is exactly the lower angular strip. -/
theorem overlap_twoStripDomain_two :
    overlap twoStripDomain 2 =
      {p | radius p ∈ Set.Ioo 1 2 ∧ angle p ∈ Set.Ioo 0 (π / 4)} := by
  ext p
  simp only [mem_overlap_iff, mem_twoStripDomain_iff, radius_deckShift, angle_deckShift,
    Int.cast_ofNat, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨hr, h | h⟩, _, h'⟩
    · exact ⟨hr, h⟩
    · rcases h' with h' | h' <;> exfalso <;> linarith [pi_pos, h.1, h'.2]
  · rintro ⟨hr, ha, hb⟩
    exact ⟨⟨hr, Or.inl ⟨ha, hb⟩⟩, hr, Or.inr ⟨by linarith, by linarith⟩⟩

theorem overlap_twoStripDomain_two_nonempty : (overlap twoStripDomain 2).Nonempty := by
  rw [overlap_twoStripDomain_two]
  refine ⟨⟨(3 / 2, π / 8), by norm_num⟩, ?_⟩
  simp only [Set.mem_ofPred_eq, radius_mk, angle_mk, Set.mem_Ioo]
  exact ⟨⟨by norm_num, by norm_num⟩, by positivity, by linarith [pi_pos]⟩

/-- Positive separation on the empty adjacent overlap does not guarantee injectivity. -/
theorem not_injOn_graph_const_twoStripDomain (c : ℝ) :
    ¬ Set.InjOn (graph (fun _ ↦ c)) twoStripDomain := by
  obtain ⟨p, hp⟩ := overlap_twoStripDomain_two_nonempty
  exact not_injOn_graph_of_deckShift_eq (by decide : (2 : ℤ) ≠ 0) hp rfl

/-- Height zero on the first strip and one on the second strip. -/
def twoStripHeight (p : PolarPoint) : ℝ := if angle p < 2 * π then 0 else 1

/-- The step height is continuous on the two-strip domain. -/
theorem continuousOn_twoStripHeight : ContinuousOn twoStripHeight twoStripDomain := by
  have ha : Continuous angle := by
    change Continuous (fun p : PolarPoint ↦ angle p)
    simp_rw [angle_def]
    exact continuous_snd.comp continuous_subtypeVal
  intro p hp
  rcases (mem_twoStripDomain_iff.mp hp).2 with h | h
  · have he := ha.continuousAt.eventually_lt (continuousAt_const (y := 2 * π))
      (by linarith [h.2, pi_pos])
    exact (Filter.EventuallyEq.continuousAt (f := twoStripHeight) (y := 0)
      (he.mono fun _ hq ↦ ite_eq_left hq)).continuousWithinAt
  · have he := (continuousAt_const (y := 2 * π)).eventually_lt (ha.continuousAt (x := p))
      (by linarith [h.1, pi_pos])
    exact (Filter.EventuallyEq.continuousAt (f := twoStripHeight) (y := 1)
      (he.mono fun _ hq ↦ ite_eq_right hq.not_gt)).continuousWithinAt

/-- Each two-turn comparison sees the full unit jump between the strips. -/
theorem separation_twoStripHeight_two {p : PolarPoint} (hp : p ∈ overlap twoStripDomain 2) :
    separation twoStripHeight 2 p = 1 := by
  rw [overlap_twoStripDomain_two] at hp
  obtain ⟨_, ha, hb⟩ := hp
  rw [separation_def]
  simp only [twoStripHeight, angle_deckShift, Int.cast_ofNat]
  rw [ite_eq_right (by linarith [pi_pos]), ite_eq_left (by linarith [pi_pos]), sub_zero]

/-- Agreement on all adjacent comparisons does not suffice for descent on the two strips. -/
theorem not_exists_height_twoStripHeight :
    ¬ ∃ v : projection '' twoStripDomain → ℝ, (fun p : twoStripDomain ↦ twoStripHeight p) =
      v ∘ Set.imageFactorization projection twoStripDomain := by
  rintro ⟨v, hv⟩
  obtain ⟨p, hp⟩ := overlap_twoStripDomain_two_nonempty
  have hu : ∃! v : projection '' twoStripDomain → ℝ, (fun p : twoStripDomain ↦ twoStripHeight p) =
      v ∘ Set.imageFactorization projection twoStripDomain :=
    ⟨v, hv, fun w hw ↦ Set.imageFactorization_surjective.injective_comp_right (hw.symm.trans hv)⟩
  have h := (existsUnique_height_iff_separation_eq_zero _ _).mp hu 2 p hp
  simp [separation_twoStripHeight_two hp] at h

end TauCeti.PolarGraph
