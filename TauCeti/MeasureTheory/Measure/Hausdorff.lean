/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Zero-dimensional Hausdorff measure

Zero-dimensional Hausdorff measure `μH[0]` is counting measure on every extended metric Borel
space: each singleton has measure `1`, so finite sets are counted by finite additivity, and an
infinite set contains finite subsets of every cardinality, so its measure is `∞`.

## Fiber measures on compact sets

If `K` is a compact subset of an extended metric space and `f` is continuous on `K` with values in
a Hausdorff space, then `y ↦ μH[d] (K ∩ f ⁻¹' {y})` is Borel measurable for every real `d`. The
same follows for σ-compact sets, by continuity of measures from below. These are the fiber
measures integrated by the coarea formula.

Fix a scale `r`. Write `H_r (s)` for the approximate Hausdorff content of `s` at scale `r`,
the infimum of `∑ i, diam (t i) ^ d` over countable covers of `s` by sets of diameter at most
`r`, and `G_r (s)` for the same infimum over covers by *open* sets. For a compact set `K`, the
function `y ↦ G_r (K ∩ f ⁻¹' {y})` is upper semicontinuous. Indeed, if an open set `U` contains
the fiber over `y`, then the image under `f` of the compact set `K \ U` is closed and misses `y`,
so `U` also contains the fibers over all `y'` near `y`. Enlarging each set of a cover to a small
open neighbourhood gives `H_r ≤ G_r ≤ H_r'` for `r' < r`. Hence
`μH[d] (s) = ⨆ r > 0, H_r (s)` is the countable supremum `⨆ k, G_(1 / k) (s)` of upper
semicontinuous functions of `y`.

## Main declarations

* `TauCeti.hausdorffMeasure_zero_eq_count`: zero-dimensional Hausdorff measure is counting
  measure.
* `IsCompact.measurable_hausdorffMeasure_inter_preimage`: fiber measures of a continuous map on a
  compact set are measurable.
* `IsSigmaCompact.measurable_hausdorffMeasure_inter_preimage`: the same on a σ-compact set.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4.1 (measurability of the fiber measures in the coarea formula).
-/

public section

open Set MeasureTheory Measure Metric Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

/-- Zero-dimensional Hausdorff measure is counting measure. Thus the normalized Euclidean
Hausdorff measure `μHE[0]` also counts points, by `euclideanHausdorffMeasure_zero`. -/
@[simp]
theorem hausdorffMeasure_zero_eq_count {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] : (μH[0] : Measure X) = count := by
  have hfinite (s : Set X) (hs : s.Finite) : μH[0] s = count s := by
    simpa [count_apply_finite _ hs] using
      (sum_measure_singleton (μ := μH[0]) (s := hs.toFinset)).symm
  ext s hs
  rcases s.finite_or_infinite with hfin | hinf
  · exact hfinite s hfin
  · rw [count_apply_infinite hinf]
    refine top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n ↦ ?_)
    obtain ⟨t, ht, htcard⟩ := hinf.exists_subset_card_eq n
    calc
      (n : ℝ≥0∞) = count (t : Set X) := by simp [htcard]
      _ = μH[0] (t : Set X) := (hfinite t t.finite_toSet).symm
      _ ≤ μH[0] s := measure_mono ht

end TauCeti

variable {X Y : Type*} [EMetricSpace X]

/-- The approximate `d`-dimensional Hausdorff content of `s` at scale `r`: the infimum of the
`d`-dimensional sums of countable covers of `s` by sets of diameter at most `r`. -/
private noncomputable def content (d : ℝ) (r : ℝ≥0∞) (s : Set X) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
    ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d

/-- The approximate `d`-dimensional Hausdorff content of `s` at scale `r` computed with covers by
open sets. -/
private noncomputable def openContent (d : ℝ) (r : ℝ≥0∞) (s : Set X) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set X) (_ : ∀ n, IsOpen (t n)) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r),
    ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d

private theorem content_anti (d : ℝ) {r r' : ℝ≥0∞} (hr : r' ≤ r) (s : Set X) :
    content d r s ≤ content d r' s :=
  iInf_mono fun _ ↦ iInf_mono fun _ ↦ iInf_mono' fun h ↦ ⟨fun n ↦ (h n).trans hr, le_rfl⟩

private theorem content_le_openContent (d : ℝ) (r : ℝ≥0∞) (s : Set X) :
    content d r s ≤ openContent d r s :=
  iInf_mono fun _ ↦ le_iInf fun _ ↦ le_rfl

/-- Enlarging the sets of a cover to small open neighbourhoods shows that covers by open sets of
diameter at most `r` are as efficient as arbitrary covers of diameter at most `r' < r`. -/
private theorem openContent_le_content (d : ℝ) {r r' : ℝ≥0∞} (hr : r' < r) (s : Set X) :
    openContent d r s ≤ content d r' s := by
  refine le_iInf₂ fun t hst ↦ le_iInf fun htr ↦ ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨ε', hε'0, hε'⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.coe_ne_zero.2 hε.ne') ℕ
  choose η' hη'0 hηr hηd using fun n ↦ ENNReal.exists_pos_forall_mem_Icc_rpow_le_add
    ((htr n).trans_lt hr) (ENNReal.coe_ne_zero.2 (hε'0 n).ne') d
  -- Thicken by `η' n / 2`, which enlarges the diameter by at most `η' n`.
  set η : ℕ → ℝ≥0 := fun n ↦ η' n / 2
  have hη0 (n : ℕ) : 0 < η n := half_pos (hη'0 n)
  have hdiam (n : ℕ) : ediam (thickening (η n) (t n)) ≤ ediam (t n) + η' n := by
    refine (ediam_thickening_le _).trans_eq ?_
    rw [← ENNReal.coe_ofNat, ← ENNReal.coe_mul, mul_div_cancel₀ _ two_ne_zero]
  calc openContent d r s
      ≤ ∑' n, ⨆ _ : (thickening (η n) (t n)).Nonempty, ediam (thickening (η n) (t n)) ^ d :=
        iInf_le_of_le (fun n ↦ thickening (η n) (t n)) <| iInf_le_of_le (fun _ ↦ isOpen_thickening)
          <| iInf_le_of_le (hst.trans (iUnion_mono fun n ↦ self_subset_thickening
            (NNReal.coe_pos.2 (hη0 n)) _)) <| iInf_le_of_le (fun n ↦ (hdiam n).trans (hηr n)) le_rfl
    _ ≤ ∑' n, ((⨆ _ : (t n).Nonempty, ediam (t n) ^ d) + ε' n) := by
        refine ENNReal.tsum_le_tsum fun n ↦ iSup_le fun hne ↦ ?_
        have hne' : (t n).Nonempty :=
          (thickening_nonempty_iff_of_pos (NNReal.coe_pos.2 (hη0 n))).1 hne
        rw [iSup_pos hne']
        exact hηd n _ ⟨ediam_mono (self_subset_thickening (NNReal.coe_pos.2 (hη0 n)) _),
          hdiam n⟩
    _ = (∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d) + ∑' n, (ε' n : ℝ≥0∞) := ENNReal.tsum_add
    _ ≤ (∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d) + ε := by gcongr

/-- The open-cover content of the fibers of a map continuous on a compact set is upper
semicontinuous in the base point. -/
private theorem upperSemicontinuous_openContent [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    {K : Set X} (hK : IsCompact K) (hf : ContinuousOn f K) (d : ℝ) (r : ℝ≥0∞) :
    UpperSemicontinuous fun y ↦ openContent d r (K ∩ f ⁻¹' {y}) := by
  intro y a ha
  obtain ⟨t, ht⟩ := iInf_lt_iff.1 ha
  obtain ⟨hto, ht⟩ := iInf_lt_iff.1 ht
  obtain ⟨hcov, ht⟩ := iInf_lt_iff.1 ht
  obtain ⟨htr, ht⟩ := iInf_lt_iff.1 ht
  -- The points of `K` outside the open set `⋃ n, t n` have a compact image, which misses `y`.
  have hC : IsClosed (f '' (K \ ⋃ n, t n)) :=
    ((hK.diff (isOpen_iUnion hto)).image_of_continuousOn (hf.mono sdiff_subset)).isClosed
  have hy : y ∉ f '' (K \ ⋃ n, t n) := by
    rintro ⟨x, hx, rfl⟩
    exact hx.2 (hcov ⟨hx.1, rfl⟩)
  filter_upwards [hC.isOpen_compl.mem_nhds hy] with y' hy'
  refine lt_of_le_of_lt (iInf_le_of_le t <| iInf_le_of_le hto <| iInf_le_of_le
    (fun x hx ↦ ?_) <| iInf_le_of_le htr le_rfl) ht
  by_contra hxU
  exact hy' ⟨x, ⟨hx.1, hxU⟩, hx.2⟩

variable [MeasurableSpace X] [BorelSpace X]

/-- Hausdorff measure is the countable supremum of the open-cover contents at the scales
`1 / k`. -/
private theorem hausdorffMeasure_eq_iSup_openContent (d : ℝ) (s : Set X) :
    μH[d] s = ⨆ k : ℕ, openContent d (k : ℝ≥0∞)⁻¹ s := by
  refine le_antisymm ?_ (iSup_le fun k ↦ ?_)
  · rw [hausdorffMeasure_apply]
    refine iSup₂_le fun r hr ↦ ?_
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hr.ne'
    exact (content_anti d hk.le s).trans ((content_le_openContent d _ s).trans
      (le_iSup (fun k : ℕ ↦ openContent d (k : ℝ≥0∞)⁻¹ s) k))
  · have hk : ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ < (k : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_lt_inv.2 (by exact_mod_cast k.lt_succ_self)
    refine (openContent_le_content d hk s).trans ?_
    rw [hausdorffMeasure_apply]
    exact le_iSup₂ (f := fun r (_ : 0 < r) ↦ content d r s) _
      (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _))

section Compact

variable [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  {f : X → Y}

/-- **Fiber measures on a compact set are measurable.** If `f` is continuous on a compact set
`K` of an extended metric space, with values in a Hausdorff space, then for every `d` the
function `y ↦ μH[d] (K ∩ f ⁻¹' {y})` is Borel measurable. -/
theorem IsCompact.measurable_hausdorffMeasure_inter_preimage {K : Set X} (hK : IsCompact K)
    (hf : ContinuousOn f K) (d : ℝ) : Measurable fun y ↦ μH[d] (K ∩ f ⁻¹' {y}) := by
  simp_rw [hausdorffMeasure_eq_iSup_openContent d]
  exact Measurable.iSup fun k ↦ (upperSemicontinuous_openContent hK hf d _).measurable

/-- **Fiber measures on a σ-compact set are measurable.** If `f` is continuous on a σ-compact set
`A` of an extended metric space, with values in a Hausdorff space, then for every `d` the
function `y ↦ μH[d] (A ∩ f ⁻¹' {y})` is Borel measurable. -/
theorem IsSigmaCompact.measurable_hausdorffMeasure_inter_preimage {A : Set X}
    (hA : IsSigmaCompact A) (hf : ContinuousOn f A) (d : ℝ) :
    Measurable fun y ↦ μH[d] (A ∩ f ⁻¹' {y}) := by
  obtain ⟨K, hK, rfl⟩ := hA
  have h (y : Y) : μH[d] ((⋃ n, K n) ∩ f ⁻¹' {y}) =
      ⨆ n, μH[d] (accumulate K n ∩ f ⁻¹' {y}) := by
    rw [← iUnion_accumulate, iUnion_inter]
    exact (monotone_accumulate.inter monotone_const).measure_iUnion
  simp_rw [h]
  exact Measurable.iSup fun n ↦
    (isCompact_accumulate hK n).measurable_hausdorffMeasure_inter_preimage
      (hf.mono (accumulate_subset_iUnion n)) d

end Compact
