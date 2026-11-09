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

Pulling real Lebesgue measure on `(0,T]` back to `ℝ≥0` commutes with restriction,
and the resulting finite-horizon measure has total mass `T`.

On a finite coordinate space `ι → ℝ`, permuting the coordinates and changing their signs
preserves Lebesgue measure (`TauCeti.volume_preserving_signedPerm`).
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NNReal

/-- Pulling Lebesgue measure on `(0,T]` back to `ℝ≥0` is the restriction of its pullback. -/
theorem comap_volume_restrict_Ioc (T : ℝ≥0) :
    (volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ) =
      (volume.comap ((↑) : ℝ≥0 → ℝ)).restrict (Ioc 0 T) := by
  rw [NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_restrict]
  -- The preimage is definitionally `Ioc 0 T`: the order on `ℝ≥0` is inherited from `ℝ`.
  congr 1

/-- The pullback of Lebesgue measure on `(0,T]` to `ℝ≥0` has total mass `T`. -/
theorem comap_volume_restrict_Ioc_univ (T : ℝ≥0) :
    (volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ) univ = T := by
  rw [comap_volume_restrict_Ioc, Measure.restrict_apply_univ,
    NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_apply]
  simp

end NNReal

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

/-- A permutation of the coordinates combined with sign changes, `x ↦ fun i => c i * x (e i)`
with `|c i| = 1`, preserves Lebesgue measure on `ι → ℝ`. -/
theorem volume_preserving_signedPerm {ι : Type*} [Fintype ι] (e : Equiv.Perm ι) (c : ι → ℝ)
    (hc : ∀ i, |c i| = 1) :
    MeasurePreserving (fun (x : ι → ℝ) i => c i * x (e i)) := by
  have hmul : MeasurePreserving (fun (y : ι → ℝ) i => c i * y i) :=
    volume_preserving_pi fun i => ⟨measurable_const_mul _, by
      rw [Real.map_volume_mul_left fun h0 => by simpa [h0] using hc i,
        abs_inv, hc i, inv_one, ENNReal.ofReal_one, one_smul]⟩
  exact hmul.comp
    (volume_preserving_arrowCongr' e.symm (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))

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
