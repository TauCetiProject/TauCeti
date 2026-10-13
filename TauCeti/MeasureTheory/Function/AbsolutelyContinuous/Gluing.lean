/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MetricDerivative.Basic

/-!
# Gluing absolutely continuous curves

Absolute continuity on adjacent intervals implies absolute continuity on their union in a
pseudometric space. This permits splitting and reassembling raw curves with either orientation.
-/

public section

open MeasureTheory Set TauCeti

namespace AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {a b c : ℝ}

private theorem of_adjacent (h₁ : AbsolutelyContinuousOnInterval γ a c)
    (h₂ : AbsolutelyContinuousOnInterval γ c b) (hac : a ≤ c) (hcb : c ≤ b) :
    AbsolutelyContinuousOnInterval γ a b := by
  have hadd {s u : ℝ} (hsc : s ≤ c) (hcu : c ≤ u) :
      (∫⁻ r in Ioc s u, metricDerivative γ r) =
        (∫⁻ r in Ioc s c, metricDerivative γ r) +
          ∫⁻ r in Ioc c u, metricDerivative γ r := by
    rw [← Ioc_union_Ioc_eq_Ioc hsc hcu]
    exact lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)
  apply absolutelyContinuousOnInterval_of_edist_le_lintegral
  · rw [uIoc_of_le (hac.trans hcb), hadd hac hcb]
    exact (ENNReal.add_lt_top.mpr ⟨by simpa [uIoc_of_le hac] using
      h₁.lintegral_metricDerivative_lt_top, by simpa [uIoc_of_le hcb] using
      h₂.lintegral_metricDerivative_lt_top⟩).ne
  · intro s hs u hu
    wlog hsu : s ≤ u generalizing s u
    · simpa only [edist_comm, uIoc_comm] using this u hu s hs (le_of_not_ge hsu)
    rw [uIcc_of_le (hac.trans hcb)] at hs hu
    by_cases huc : u ≤ c
    · exact h₁.edist_le_lintegral_metricDerivative
        (by simpa [uIcc_of_le hac] using And.intro hs.1 (hsu.trans huc))
        (by simpa [uIcc_of_le hac] using And.intro hu.1 huc)
    by_cases hcs : c ≤ s
    · exact h₂.edist_le_lintegral_metricDerivative
        (by simpa [uIcc_of_le hcb] using And.intro hcs hs.2)
        (by simpa [uIcc_of_le hcb] using And.intro (hcs.trans hsu) hu.2)
    have hsc : s ≤ c := (le_of_not_ge hcs)
    have hcu : c ≤ u := (le_of_not_ge huc)
    rw [uIoc_of_le hsu, hadd hsc hcu]
    refine (edist_triangle (γ s) (γ c) (γ u)).trans (add_le_add ?_ ?_)
    · have hs₁ : s ∈ uIcc a c := by simpa [uIcc_of_le hac] using And.intro hs.1 hsc
      have h := h₁.edist_le_lintegral_metricDerivative (s := s) (u := c) hs₁ right_mem_uIcc
      rwa [uIoc_of_le hsc] at h
    · have hu₂ : u ∈ uIcc c b := by simpa [uIcc_of_le hcb] using And.intro hcu hu.2
      have h := h₂.edist_le_lintegral_metricDerivative (s := c) (u := u) left_mem_uIcc hu₂
      rwa [uIoc_of_le hcu] at h

/-- Absolute continuity on two intervals sharing an endpoint implies absolute continuity
between their other endpoints, in either orientation. -/
theorem trans (h₁ : AbsolutelyContinuousOnInterval γ a c)
    (h₂ : AbsolutelyContinuousOnInterval γ c b) :
    AbsolutelyContinuousOnInterval γ a b := by
  wlog hab : a ≤ b generalizing a b c
  · exact (this h₂.symm h₁.symm (le_of_not_ge hab)).symm
  by_cases hac : a ≤ c
  · by_cases hcb : c ≤ b
    · exact of_adjacent h₁ h₂ hac hcb
    · apply h₁.mono
      rw [uIcc_of_le hab, uIcc_of_le hac]
      exact Icc_subset_Icc le_rfl (le_of_not_ge hcb)
  · apply h₂.mono
    rw [uIcc_of_le hab, uIcc_of_le ((le_of_not_ge hac).trans hab)]
    exact Icc_subset_Icc (le_of_not_ge hac) le_rfl

/-- Absolute continuity can be checked on the two pieces of a parameter interval. -/
theorem _root_.absolutelyContinuousOnInterval_iff_and (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval γ a b ↔
      AbsolutelyContinuousOnInterval γ a c ∧ AbsolutelyContinuousOnInterval γ c b :=
  ⟨fun h ↦ ⟨h.mono (uIcc_subset_uIcc left_mem_uIcc hc),
    h.mono (uIcc_subset_uIcc hc right_mem_uIcc)⟩, fun h ↦ h.1.trans h.2⟩

end AbsolutelyContinuousOnInterval
