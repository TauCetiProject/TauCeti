/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Data.Set.SymmDiff

/-!
# A layer-cake formula for the distance between real functions

This file expresses the `L¹` distance between two almost everywhere measurable real functions as
the integral, over all levels, of the measure of the symmetric difference of their sublevel sets.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal symmDiff

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

/-- A level lies between two reals exactly when exactly one of them is at most that level. -/
private theorem mem_Ico_min_max_iff {x y s : ℝ} :
    s ∈ Ico (min x y) (max x y) ↔ ((x ≤ s ∧ ¬ y ≤ s) ∨ (y ≤ s ∧ ¬ x ≤ s)) := by
  rw [mem_Ico]
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right h]
    refine ⟨fun hs ↦ Or.inl ⟨hs.1, not_le.2 hs.2⟩, ?_⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, not_le.1 h2⟩
    · exact absurd (h.trans h1) h2
  · rw [min_eq_right h, max_eq_left h]
    refine ⟨fun hs ↦ Or.inr ⟨hs.1, not_le.2 hs.2⟩, ?_⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact absurd (h.trans h1) h2
    · exact ⟨h1, not_le.1 h2⟩

private theorem lintegral_enorm_sub_eq_lintegral_measure_symmDiff_of_measurable
    (m : Measure α) [SFinite m] {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, ‖f a - g a‖ₑ ∂m = ∫⁻ s, m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
  set F : Set (α × ℝ) := {q | min (f q.1) (g q.1) ≤ q.2 ∧ q.2 < max (f q.1) (g q.1)} with hFdef
  have hF : MeasurableSet F :=
    (measurableSet_le ((hf.comp measurable_fst).min (hg.comp measurable_fst)) measurable_snd).inter
      (measurableSet_lt measurable_snd ((hf.comp measurable_fst).max (hg.comp measurable_fst)))
  have hmem_Ico : ∀ (a : α) (s : ℝ),
      (a, s) ∈ F ↔ s ∈ Ico (min (f a) (g a)) (max (f a) (g a)) := by
    intro a s
    simp [hFdef, mem_Ico]
  have hmem_symmDiff : ∀ (a : α) (s : ℝ),
      (a, s) ∈ F ↔ a ∈ ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
    intro a s
    rw [hmem_Ico, Set.mem_symmDiff]
    exact mem_Ico_min_max_iff
  have hlevel : ∀ a : α, (∫⁻ s, F.indicator 1 (a, s)) = ‖f a - g a‖ₑ := by
    intro a
    have hfun : (fun s ↦ F.indicator (1 : α × ℝ → ℝ≥0∞) (a, s))
        = (Ico (min (f a) (g a)) (max (f a) (g a))).indicator 1 := by
      funext s
      by_cases hs : s ∈ Ico (min (f a) (g a)) (max (f a) (g a))
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem ((hmem_Ico a s).mpr hs), Pi.one_apply,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem hs,
          Set.indicator_of_notMem (fun hq ↦ hs ((hmem_Ico a s).mp hq))]
    rw [hfun, lintegral_indicator_one measurableSet_Ico, Real.volume_Ico, max_sub_min_eq_abs,
      abs_sub_comm, Real.enorm_eq_ofReal_abs]
  have hsection : ∀ s : ℝ,
      (∫⁻ a, F.indicator 1 (a, s) ∂m) = m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
    intro s
    have hmeas : MeasurableSet ({a | f a ≤ s} ∆ {a | g a ≤ s}) :=
      (measurableSet_le hf measurable_const).symmDiff (measurableSet_le hg measurable_const)
    have hfun : (fun a ↦ F.indicator (1 : α × ℝ → ℝ≥0∞) (a, s))
        = ({a | f a ≤ s} ∆ {a | g a ≤ s}).indicator 1 := by
      funext a
      by_cases ha : a ∈ ({a | f a ≤ s} ∆ {a | g a ≤ s})
      · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ((hmem_symmDiff a s).mpr ha),
          Pi.one_apply, Pi.one_apply]
      · rw [Set.indicator_of_notMem ha,
          Set.indicator_of_notMem (fun hq ↦ ha ((hmem_symmDiff a s).mp hq))]
    rw [hfun, lintegral_indicator_one hmeas]
  calc ∫⁻ a, ‖f a - g a‖ₑ ∂m = ∫⁻ a, (∫⁻ s, F.indicator 1 (a, s)) ∂m := by
        simp_rw [hlevel]
    _ = ∫⁻ s, (∫⁻ a, F.indicator 1 (a, s) ∂m) :=
        lintegral_lintegral_swap
          (f := fun (a : α) (s : ℝ) ↦ F.indicator (1 : α × ℝ → ℝ≥0∞) (a, s))
          (measurable_const.indicator hF).aemeasurable
    _ = ∫⁻ s, m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by simp_rw [hsection]

/-- **The area between two graphs.** The `L¹` distance of two almost everywhere measurable real
functions is the integral, over the levels `s`, of the measure of the set where exactly one of the
two functions is at most `s`. -/
theorem lintegral_enorm_sub_eq_lintegral_measure_symmDiff (m : Measure α) [SFinite m]
    {f g : α → ℝ} (hf : AEMeasurable f m) (hg : AEMeasurable g m) :
    ∫⁻ a, ‖f a - g a‖ₑ ∂m = ∫⁻ s, m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
  calc
    ∫⁻ a, ‖f a - g a‖ₑ ∂m = ∫⁻ a, ‖hf.mk f a - hg.mk g a‖ₑ ∂m := by
      apply lintegral_congr_ae
      filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with a hfa hga
      rw [hfa, hga]
    _ = ∫⁻ s, m ({a | hf.mk f a ≤ s} ∆ {a | hg.mk g a ≤ s}) :=
      lintegral_enorm_sub_eq_lintegral_measure_symmDiff_of_measurable m hf.measurable_mk
        hg.measurable_mk
    _ = ∫⁻ s, m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
      apply lintegral_congr
      intro s
      apply measure_congr
      filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with a hfa hga
      simp only [Set.mem_symmDiff, Set.mem_ofPred_eq]
      rw [hfa, hga]

end TauCeti
