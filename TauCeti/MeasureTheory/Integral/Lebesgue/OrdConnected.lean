/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Lebesgue integrals over intervals of the real line

The Lebesgue integral over an interval `J ⊆ ℝ`, that is, an order-connected set, is the supremum
of the integrals over the closed subintervals of `J`: `J` is the directed union of the countably
many closed intervals whose endpoints lie in `J` and are rational or endpoints of `J`. In
particular, a common bound for the integrals over the closed subintervals bounds the integral over
`J`, for any measure and without any measurability assumption on `J` or on the integrand.

## Main statements

* `TauCeti.setLIntegral_le_of_ordConnected`: `∫_J h ≤ c` when `∫_{[s, t]} h ≤ c` for all
  `s ≤ t` in `J`.
-/

public section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

/-- The integral of `h` over an interval `J ⊆ ℝ` is at most any common bound for its integrals over
the closed subintervals of `J`. -/
theorem setLIntegral_le_of_ordConnected {μ : Measure ℝ} {h : ℝ → ℝ≥0∞} {J : Set ℝ}
    (hJ : J.OrdConnected) {c : ℝ≥0∞}
    (hc : ∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∫⁻ x in Icc s t, h x ∂μ ≤ c) :
    ∫⁻ x in J, h x ∂μ ≤ c := by
  -- The points of `J` that are rational or one of the at most two endpoints of `J`.
  set S : Set ℝ := J ∩ (range ((↑) : ℚ → ℝ) ∪
    ({s ∈ J | ∀ x ∈ J, s ≤ x} ∪ {s ∈ J | ∀ x ∈ J, x ≤ s}))
  set U : Set ℝ := ⋃ q ∈ S ×ˢ S, Icc q.1 q.2
  have hS : S.Countable := by
    refine (countable_range _).union (Countable.union ?_ ?_) |>.mono inter_subset_right
    · exact Set.Subsingleton.countable fun s hs s' hs' => le_antisymm (hs.2 s' hs'.1) (hs'.2 s hs.1)
    · exact Set.Subsingleton.countable fun s hs s' hs' => le_antisymm (hs'.2 s hs.1) (hs.2 s' hs'.1)
  -- An endpoint of `J` is the interval `[s, s]`; every other point of `J` lies between two
  -- rational points of `J`.
  have hJU : J ⊆ U := by
    intro s hs
    by_cases h₁ : ∀ x ∈ J, s ≤ x
    · exact mem_biUnion (x := (s, s)) ⟨⟨hs, Or.inr (Or.inl ⟨hs, h₁⟩)⟩,
        ⟨hs, Or.inr (Or.inl ⟨hs, h₁⟩)⟩⟩ ⟨le_rfl, le_rfl⟩
    by_cases h₂ : ∀ x ∈ J, x ≤ s
    · exact mem_biUnion (x := (s, s)) ⟨⟨hs, Or.inr (Or.inr ⟨hs, h₂⟩)⟩,
        ⟨hs, Or.inr (Or.inr ⟨hs, h₂⟩)⟩⟩ ⟨le_rfl, le_rfl⟩
    push Not at h₁ h₂
    obtain ⟨x₁, hx₁, hx₁s⟩ := h₁
    obtain ⟨x₂, hx₂, hsx₂⟩ := h₂
    obtain ⟨q₁, hq₁, hq₁s⟩ := exists_rat_btwn hx₁s
    obtain ⟨q₂, hq₂, hq₂s⟩ := exists_rat_btwn hsx₂
    exact mem_biUnion (x := ((q₁ : ℝ), (q₂ : ℝ)))
      ⟨⟨hJ.out hx₁ hs ⟨hq₁.le, hq₁s.le⟩, Or.inl ⟨q₁, rfl⟩⟩,
        ⟨hJ.out hs hx₂ ⟨hq₂.le, hq₂s.le⟩, Or.inl ⟨q₂, rfl⟩⟩⟩ ⟨hq₁s.le, hq₂.le⟩
  have hD : (S ×ˢ S).Countable := hS.prod hS
  have hU : MeasurableSet U := MeasurableSet.biUnion hD fun _ _ => measurableSet_Icc
  calc ∫⁻ x in J, h x ∂μ ≤ ∫⁻ x in U, h x ∂μ := lintegral_mono_set hJU
    _ = μ.withDensity h U := (withDensity_apply _ hU).symm
    _ = ⨆ q ∈ S ×ˢ S, μ.withDensity h (Icc q.1 q.2) := by
        refine measure_biUnion_eq_iSup hD fun q hq q' hq' => ⟨(min q.1 q'.1, max q.2 q'.2),
          ⟨?_, ?_⟩, ?_, ?_⟩
        · rcases min_choice q.1 q'.1 with h | h <;> rw [h]
          exacts [hq.1, hq'.1]
        · rcases max_choice q.2 q'.2 with h | h <;> rw [h]
          exacts [hq.2, hq'.2]
        · exact Icc_subset_Icc (min_le_left _ _) (le_max_left _ _)
        · exact Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
    _ ≤ c := by
        refine iSup₂_le fun q hq => ?_
        rw [withDensity_apply _ measurableSet_Icc]
        rcases le_or_gt q.1 q.2 with hle | hlt
        · exact hc _ hq.1.1 _ hq.2.1 hle
        · simp [Icc_eq_empty_of_lt hlt]

end TauCeti
