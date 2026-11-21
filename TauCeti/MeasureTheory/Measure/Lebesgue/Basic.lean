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

The Lebesgue measure of a finite union of pairwise disjoint intervals `Ι (a i) (b i)` is the sum of
their lengths (`TauCeti.volume_biUnion_uIoc_eq_ofReal_sum`).
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Interval symmDiff

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

/-- The symmetric difference of centered real `eball`s of lengths `ENNReal.ofReal a` and
`ENNReal.ofReal b` has Lebesgue measure at most `ENNReal.ofReal |a - b|`. -/
theorem volume_eball_ofReal_symmDiff_le (a b : ℝ) :
    volume (Metric.eball (0 : ℝ) (ENNReal.ofReal a / 2) ∆
        Metric.eball (0 : ℝ) (ENNReal.ofReal b / 2)) ≤ ENNReal.ofReal |a - b| := by
  have hvol (r : ℝ) : volume (Metric.eball (0 : ℝ) (ENNReal.ofReal r / 2)) = ENNReal.ofReal r := by
    rw [Real.volume_eball, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  have hofmax (r : ℝ) : ENNReal.ofReal r = ENNReal.ofReal (max r 0) := by
    rcases le_or_gt r 0 with hr | hr
    · rw [max_eq_right hr, ENNReal.ofReal_of_nonpos hr, ENNReal.ofReal_zero]
    · rw [max_eq_left hr.le]
  have hle {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
      volume (Metric.eball (0 : ℝ) (ENNReal.ofReal x / 2) ∆
          Metric.eball (0 : ℝ) (ENNReal.ofReal y / 2)) ≤ ENNReal.ofReal |x - y| := by
    have hsub : Metric.eball (0 : ℝ) (ENNReal.ofReal x / 2) ⊆
        Metric.eball (0 : ℝ) (ENNReal.ofReal y / 2) :=
      Metric.eball_subset_eball (ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hxy) 2)
    rw [symmDiff_def, Set.sdiff_eq_empty.2 hsub, empty_union,
      measure_sdiff hsub Metric.isOpen_eball.measurableSet.nullMeasurableSet
        (by rw [hvol]; exact ENNReal.ofReal_ne_top),
      hvol, hvol, ← ENNReal.ofReal_sub _ hx, abs_of_nonpos (sub_nonpos.2 hxy), neg_sub]
  rw [hofmax a, hofmax b]
  refine (le_total (max a 0) (max b 0) |>.elim (hle (le_max_right _ _)) fun hba ↦ ?_).trans
    (ENNReal.ofReal_le_ofReal (abs_max_sub_max_le_abs a b 0))
  rw [symmDiff_comm, abs_sub_comm]
  exact hle (le_max_right _ _) hba

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

/-- The measure of a finite union of pairwise disjoint intervals `Ι (a i) (b i)` is the sum of their
lengths `max (a i) (b i) - min (a i) (b i)`. -/
theorem volume_biUnion_uIoc_eq_ofReal_sum {ι : Type*} (I : Finset ι) (a b : ι → ℝ)
    (h : (I : Set ι).PairwiseDisjoint fun i ↦ Ι (a i) (b i)) :
    volume (⋃ i ∈ I, Ι (a i) (b i)) =
      ENNReal.ofReal (∑ i ∈ I, (max (a i) (b i) - min (a i) (b i))) := by
  rw [measure_biUnion_finset h fun _ _ ↦ measurableSet_uIoc,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sub_nonneg.2 min_le_max]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Real.volume_uIoc, ← max_sub_min_eq_abs', max_comm, min_comm]

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
    ((subset_Icc_csInf_csSup hbdd.1 hbdd.2).eventuallySubset.trans
        Ioo_ae_eq_Icc.symm.subset).antisymm
      hsub.eventuallySubset
  refine ⟨sInf I, sSup I, lt_of_not_ge fun hle => h0 ?_, hae⟩
  rw [measure_congr hae, Ioo_eq_empty_of_le hle, measure_empty]
