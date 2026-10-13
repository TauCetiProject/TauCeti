/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Gluing absolutely continuous curves

In a finite-dimensional real normed space, absolute continuity on adjacent intervals implies
absolute continuity on their union. This permits splitting and reassembling raw curves without
introducing a new curve carrier. The proof reconstructs the curve from its integrable derivative.
-/

public section

open MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {γ : ℝ → F} {a b c : ℝ}

/-- Absolute continuity glues across the common endpoint of two ordered intervals. -/
theorem of_adjacent (h₁ : AbsolutelyContinuousOnInterval γ a c)
    (h₂ : AbsolutelyContinuousOnInterval γ c b) (hac : a ≤ c) (hcb : c ≤ b) :
    AbsolutelyContinuousOnInterval γ a b := by
  have hd₁ := h₁.intervalIntegrable_deriv_of_finiteDimensional
  have hd₂ := h₂.intervalIntegrable_deriv_of_finiteDimensional
  have hd : IntervalIntegrable (deriv γ) volume a b := hd₁.trans hd₂
  have hI := hd.absolutelyContinuousOnInterval_intervalIntegral_of_finiteDimensional
    left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ γ a) a b :=
    (LipschitzWith.const (γ a)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hconst.fun_add hI).congr
  intro t ht
  dsimp only
  rw [uIcc_of_le (hac.trans hcb)] at ht
  by_cases htc : t ≤ c
  · have hsub : uIcc a t ⊆ uIcc a c := by
      rw [uIcc_of_le ht.1, uIcc_of_le hac]
      exact Icc_subset_Icc le_rfl htc
    rw [(h₁.mono hsub).integral_deriv_eq_sub_of_finiteDimensional]
    abel
  · have hsub : uIcc c t ⊆ uIcc c b := by
      rw [uIcc_of_le (le_of_not_ge htc), uIcc_of_le hcb]
      exact Icc_subset_Icc le_rfl ht.2
    rw [← intervalIntegral.integral_add_adjacent_intervals hd₁
      (hd₂.mono_set hsub), h₁.integral_deriv_eq_sub_of_finiteDimensional,
      (h₂.mono hsub).integral_deriv_eq_sub_of_finiteDimensional]
    abel

/-- Absolute continuity on two intervals sharing an endpoint implies absolute continuity
between their other endpoints, in either orientation. -/
theorem trans (h₁ : AbsolutelyContinuousOnInterval γ a c)
    (h₂ : AbsolutelyContinuousOnInterval γ c b) :
    AbsolutelyContinuousOnInterval γ a b := by
  wlog hab : a ≤ b generalizing a b c
  · exact (this h₂.symm h₁.symm (le_of_not_ge hab)).symm
  by_cases hac : a ≤ c
  · by_cases hcb : c ≤ b
    · exact h₁.of_adjacent h₂ hac hcb
    · apply h₁.mono
      rw [uIcc_of_le hab, uIcc_of_le hac]
      exact Icc_subset_Icc le_rfl (le_of_not_ge hcb)
  · apply h₂.mono
    rw [uIcc_of_le hab, uIcc_of_le ((le_of_not_ge hac).trans hab)]
    exact Icc_subset_Icc (le_of_not_ge hac) le_rfl

/-- Absolute continuity can be checked on the two pieces of a parameter interval. -/
theorem iff_split (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval γ a b ↔
      AbsolutelyContinuousOnInterval γ a c ∧ AbsolutelyContinuousOnInterval γ c b :=
  ⟨fun h ↦ ⟨h.mono (uIcc_subset_uIcc left_mem_uIcc hc),
    h.mono (uIcc_subset_uIcc hc right_mem_uIcc)⟩, fun h ↦ h.1.trans h.2⟩

end AbsolutelyContinuousOnInterval
