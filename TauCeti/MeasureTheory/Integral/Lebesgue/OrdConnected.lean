/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Lebesgue integrals over intervals of the real line

The Lebesgue integral over an interval `J ⊆ ℝ`, that is, an order-connected set, against a measure
without atoms is the supremum of the integrals over the closed subintervals of `J`: up to its at
most two endpoints, `J` is the directed union of the countably many closed intervals with rational
endpoints in `J`. In particular, a common bound for the integrals over the closed subintervals
bounds the integral over `J`, without any measurability assumption on `J` or on the integrand.

## Main statements

* `TauCeti.setLIntegral_le_of_ordConnected`: `∫_J h ≤ c` when `∫_{[s, t]} h ≤ c` for all
  `s ≤ t` in `J`.
-/

public section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

/-- The integral of `h` over an interval `J ⊆ ℝ`, against a measure without atoms, is at most any
common bound for its integrals over the closed subintervals of `J`. -/
theorem setLIntegral_le_of_ordConnected {μ : Measure ℝ} [NullSingletonClass μ] {h : ℝ → ℝ≥0∞}
    {J : Set ℝ} (hJ : J.OrdConnected) {c : ℝ≥0∞}
    (hc : ∀ s ∈ J, ∀ t ∈ J, s ≤ t → ∫⁻ x in Icc s t, h x ∂μ ≤ c) :
    ∫⁻ x in J, h x ∂μ ≤ c := by
  set D : Set (ℚ × ℚ) := {q | (q.1 : ℝ) ∈ J ∧ (q.2 : ℝ) ∈ J}
  set U : Set ℝ := ⋃ q ∈ D, Icc (q.1 : ℝ) q.2
  set R : Set ℝ := {s ∈ J | ∀ x ∈ J, s ≤ x} ∪ {s ∈ J | ∀ x ∈ J, x ≤ s}
  -- Every point of `J` other than its endpoints lies between two rational points of `J`.
  have hJUR : J ⊆ U ∪ R := by
    intro s hs
    by_cases h₁ : ∀ x ∈ J, s ≤ x
    · exact Or.inr (Or.inl ⟨hs, h₁⟩)
    by_cases h₂ : ∀ x ∈ J, x ≤ s
    · exact Or.inr (Or.inr ⟨hs, h₂⟩)
    push Not at h₁ h₂
    obtain ⟨x₁, hx₁, hx₁s⟩ := h₁
    obtain ⟨x₂, hx₂, hsx₂⟩ := h₂
    obtain ⟨q₁, hq₁, hq₁s⟩ := exists_rat_btwn hx₁s
    obtain ⟨q₂, hq₂, hq₂s⟩ := exists_rat_btwn hsx₂
    refine Or.inl (mem_biUnion (x := (q₁, q₂)) ⟨hJ.out hx₁ hs ⟨hq₁.le, hq₁s.le⟩,
      hJ.out hs hx₂ ⟨hq₂.le, hq₂s.le⟩⟩ ⟨hq₁s.le, hq₂.le⟩)
  have hR : μ R = 0 := by
    refine measure_union_null (Set.Subsingleton.measure_zero ?_ _)
      (Set.Subsingleton.measure_zero ?_ _)
    · exact fun s hs s' hs' => le_antisymm (hs.2 s' hs'.1) (hs'.2 s hs.1)
    · exact fun s hs s' hs' => le_antisymm (hs'.2 s hs.1) (hs.2 s' hs'.1)
  have hD : D.Countable := D.to_countable
  have hU : MeasurableSet U := MeasurableSet.biUnion hD fun _ _ => measurableSet_Icc
  calc ∫⁻ x in J, h x ∂μ ≤ ∫⁻ x in U ∪ R, h x ∂μ := lintegral_mono_set hJUR
    _ ≤ (∫⁻ x in U, h x ∂μ) + ∫⁻ x in R, h x ∂μ := lintegral_union_le _ _ _
    _ = μ.withDensity h U := by rw [setLIntegral_measure_zero _ _ hR, add_zero,
        withDensity_apply _ hU]
    _ = ⨆ q ∈ D, μ.withDensity h (Icc (q.1 : ℝ) q.2) := by
        refine measure_biUnion_eq_iSup hD fun q hq q' hq' => ⟨(min q.1 q'.1, max q.2 q'.2),
          ⟨?_, ?_⟩, ?_, ?_⟩
        · rcases min_choice q.1 q'.1 with h | h <;> rw [h]
          exacts [hq.1, hq'.1]
        · rcases max_choice q.2 q'.2 with h | h <;> rw [h]
          exacts [hq.2, hq'.2]
        · exact Icc_subset_Icc (by exact_mod_cast min_le_left _ _)
            (by exact_mod_cast le_max_left _ _)
        · exact Icc_subset_Icc (by exact_mod_cast min_le_right _ _)
            (by exact_mod_cast le_max_right _ _)
    _ ≤ c := by
        refine iSup₂_le fun q hq => ?_
        rw [withDensity_apply _ measurableSet_Icc]
        rcases le_or_gt (q.1 : ℝ) q.2 with hle | hlt
        · exact hc _ hq.1 _ hq.2 hle
        · simp [Icc_eq_empty_of_lt hlt]

end TauCeti
