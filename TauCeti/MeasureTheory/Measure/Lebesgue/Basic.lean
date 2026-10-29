/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lebesgue measure of intervals and centered interval differences

Replacing two subsets of the real line by open centered intervals of the same respective
volumes can only decrease the volume of their one-sided difference. The inequality uses
Mathlib's extended-radius balls and `Real.volume_eball`, and allows zero and infinite volumes.
It supplies the sectionwise contraction inequality for Steiner symmetrization.

An order-connected subset of the real line of positive finite volume agrees almost everywhere
with a nonempty bounded open interval (`Set.OrdConnected.exists_ae_eq_Ioo`): finite volume
bounds it, and it lies between the open and the closed interval spanned by its infimum and
supremum.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- Centering intervals can only decrease the length of a one-sided difference. -/
theorem volume_eball_sdiff_le (s u : Set ℝ) :
    volume (Metric.eball (0 : ℝ) (volume s / 2) \ Metric.eball 0 (volume u / 2)) ≤
      volume (s \ u) := by
  have hlength (a : ℝ≥0∞) : volume (Metric.eball (0 : ℝ) (a / 2)) = a := by
    rw [Real.volume_eball]
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  rcases le_total (volume s) (volume u) with h | h
  · rw [sdiff_eq_empty.mpr (Metric.eball_subset_eball (ENNReal.div_le_div_right h 2)),
      measure_empty]
    exact bot_le
  · by_cases hu : volume u = ∞
    · have hs : volume s = ∞ := top_le_iff.mp (hu ▸ h)
      simp [hu, hs]
    · rw [measure_sdiff (Metric.eball_subset_eball (ENNReal.div_le_div_right h 2))
        Metric.isOpen_eball.measurableSet.nullMeasurableSet (by rwa [hlength]), hlength, hlength]
      exact le_measure_sdiff

end TauCeti

/-- An order-connected subset of `ℝ` of positive finite volume agrees almost everywhere with a
nonempty bounded open interval. -/
theorem Set.OrdConnected.exists_ae_eq_Ioo {I : Set ℝ} (hI : I.OrdConnected) (h0 : volume I ≠ 0)
    (hfin : volume I ≠ ∞) : ∃ a b, a < b ∧ I =ᵐ[volume] Ioo a b := by
  obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero h0
  -- An unbounded order-connected set contains a ray, of infinite volume.
  have hbdd : BddBelow I ∧ BddAbove I := by
    refine ⟨by_contra fun h => hfin ?_, by_contra fun h => hfin ?_⟩
    · refine measure_mono_top (s₁ := Iic y) (fun z hz => ?_) Real.volume_Iic
      obtain ⟨w, hwI, hwz⟩ := not_bddBelow_iff.1 h z
      exact hI.out hwI hy ⟨hwz.le, hz⟩
    · refine measure_mono_top (s₁ := Ici y) (fun z hz => ?_) Real.volume_Ici
      obtain ⟨w, hwI, hwz⟩ := not_bddAbove_iff.1 h z
      exact hI.out hy hwI ⟨hz, hwz.le⟩
  have hsub := IsConnected.Ioo_csInf_csSup_subset ⟨⟨y, hy⟩, hI.isPreconnected⟩ hbdd.1 hbdd.2
  have hae : I =ᵐ[volume] Ioo (sInf I) (sSup I) :=
    ((subset_Icc_csInf_csSup hbdd.1 hbdd.2).eventuallyLE.trans Ioo_ae_eq_Icc.symm.le).antisymm
      hsub.eventuallyLE
  refine ⟨sInf I, sSup I, lt_of_not_ge fun hle => h0 ?_, hae⟩
  rw [measure_congr hae, Ioo_eq_empty_of_le hle, measure_empty]
