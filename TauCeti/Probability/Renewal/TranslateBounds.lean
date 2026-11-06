/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.LocalBound
public import TauCeti.MeasureTheory.Measure.Tight.ExponentialWeight

/-!
# Bounds on translated renewal measures

The renewal measure, regarded as a measure on the real line and translated by `-t`, has
uniformly bounded mass on intervals of a fixed length. Exponential weighting therefore gives
uniformly bounded, tight families of finite measures. These bounds supply compactness for
translated renewal measures without any moment or nonlattice assumption.

The renewal estimate used here is `Measure.renewalMeasure_Icc_add_le` from the local-renewal-bound
formalization. The compactness argument follows Feller, *An Introduction to Probability Theory
and Its Applications*, vol. II, second edition, Chapter XI.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

/-- The renewal measure on the real line, translated by `-t`. -/
def translatedRenewalMeasure (F : Measure ℝ≥0) (t : ℝ) : Measure ℝ :=
  F.renewalMeasure.map fun s : ℝ≥0 ↦ (s : ℝ) - t

/-- The translated renewal measure is the pushforward of the half-line renewal measure. -/
theorem translatedRenewalMeasure_def (F : Measure ℝ≥0) (t : ℝ) :
    F.translatedRenewalMeasure t =
      F.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t) := (rfl)

/-- Evaluation of a translated renewal measure on a measurable set. -/
theorem translatedRenewalMeasure_apply (F : Measure ℝ≥0) (t : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    F.translatedRenewalMeasure t s = F.renewalMeasure ((fun u : ℝ≥0 ↦ (u : ℝ) - t) ⁻¹' s) := by
  exact Measure.map_apply (by fun_prop) hs

/-- Translating the renewal measure preserves the uniform local renewal bound, including
intervals that meet or lie below the original endpoint zero. -/
theorem translatedRenewalMeasure_Icc_add_le (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (t a : ℝ) (h : ℝ≥0) :
    F.translatedRenewalMeasure t (Icc a (a + h)) ≤ F.renewalMeasure (Iic h) := by
  rw [translatedRenewalMeasure_apply F t measurableSet_Icc]
  by_cases ha : 0 ≤ a + t
  · let b : ℝ≥0 := .mk (a + t) ha
    have hsub : (fun u : ℝ≥0 ↦ (u : ℝ) - t) ⁻¹' Icc a (a + h) ⊆ Icc b (b + h) := by
      intro u hu
      simp only [mem_preimage, mem_Icc] at hu
      constructor
      · apply NNReal.coe_le_coe.mp
        simp only [b, NNReal.coe_mk]
        linarith [hu.1]
      · apply NNReal.coe_le_coe.mp
        simp only [b, NNReal.coe_add, NNReal.coe_mk]
        linarith [hu.2]
    exact (measure_mono hsub).trans (F.renewalMeasure_Icc_add_le b h)
  · apply (measure_mono ?_ : F.renewalMeasure _ ≤ F.renewalMeasure (Iic h))
    intro u hu
    simp only [mem_preimage, mem_Icc] at hu
    exact_mod_cast (by linarith [hu.2] : (u : ℝ) ≤ h)

/-- A translated renewal measure is locally finite whenever the interarrival law is not
concentrated at zero. -/
theorem isLocallyFiniteMeasure_translatedRenewalMeasure (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hF : F {0} < 1) (t : ℝ) :
    IsLocallyFiniteMeasure (F.translatedRenewalMeasure t) := by
  refine ⟨fun x ↦ ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩⟩
  have hend : x - 1 + 2 = x + 1 := by ring
  exact lt_of_le_of_lt (by simpa only [NNReal.coe_ofNat, hend]
    using F.translatedRenewalMeasure_Icc_add_le t (x - 1) 2)
    (F.renewalMeasure_Iic_lt_top hF 2)

/-- Exponential weighting makes arbitrary translates of a nondegenerate renewal measure a
uniformly bounded tight family. No assumption on the mean or lattice span is needed. -/
theorem exists_bound_isTightMeasureSet_withDensity_translatedRenewalMeasure
    (F : Measure ℝ≥0) [IsProbabilityMeasure F] (hF : F {0} < 1)
    {ι : Type*} (t : ι → ℝ) :
    ∃ C : ℝ≥0,
      (∀ i, (F.translatedRenewalMeasure (t i)).withDensity
        (fun x ↦ ENNReal.ofReal (Real.exp (-|x|))) univ ≤ C) ∧
      IsTightMeasureSet (range fun i ↦ (F.translatedRenewalMeasure (t i)).withDensity
        (fun x ↦ ENNReal.ofReal (Real.exp (-|x|)))) := by
  apply exists_bound_isTightMeasureSet_withDensity_exp_neg_abs
    (fun i ↦ F.translatedRenewalMeasure (t i)) (F.renewalMeasure (Iic 1)).toNNReal
  intro i a
  rw [ENNReal.coe_toNNReal (F.renewalMeasure_Iic_lt_top hF 1).ne]
  exact F.translatedRenewalMeasure_Icc_add_le (t i) a 1

end MeasureTheory.Measure
