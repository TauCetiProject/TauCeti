/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import TauCeti.MeasureTheory.Function.Coarea.Eilenberg
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.MeasureTheory.Measure.Regular

/-!
# Measurability of the fiber measures of a map

The coarea formula integrates the Hausdorff measures `y ↦ μH[t] (A ∩ f ⁻¹' {y})` of the fibers of
a map `f`. This file shows that this integrand is measurable, so that the formula is an identity
between genuine integrals, and so that it can be summed over a countable partition of `A`.

* **Compact sets.** If `K` is a compact subset of an extended metric space and `f` is continuous
  on `K` with values in a Hausdorff space, then `y ↦ μH[d] (K ∩ f ⁻¹' {y})` is Borel measurable
  for every real `d`. The same follows for σ-compact sets, by continuity of measures from below.
* **Measurable sets.** If `f` is Lipschitz on `A` with values in a finite-dimensional real normed
  space with additive Haar measure `μ`, and `A` is σ-compact up to a `μH[m + t]`-null set, where
  `m` is the dimension of the target, then `y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere
  measurable: the fibers of the null part are null for almost every `y` by Eilenberg's inequality.
  In particular this holds for every Lebesgue measurable subset `A` of a finite-dimensional real
  inner product space of dimension `n` and the normalized Hausdorff measures `μHE[k]` with
  `n ≤ m + k`, which include the coarea dimension `k = n - m`.

## The argument

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

* `IsCompact.measurable_hausdorffMeasure_inter_preimage`: fiber measures of a continuous map on a
  compact set are measurable.
* `IsSigmaCompact.measurable_hausdorffMeasure_inter_preimage`: the same on a σ-compact set.
* `LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage`: fiber measures of a Lipschitz
  map are almost everywhere measurable on a set that is σ-compact up to a null set.
* `LipschitzOnWith.aemeasurable_euclideanHausdorffMeasure_inter_preimage`: the normalized fiber
  measures `μHE[k]` of a Lipschitz map on a Lebesgue measurable subset of a finite-dimensional
  real inner product space are almost everywhere measurable.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4.1 (measurability of the fiber measures in the coarea formula).
-/

public section

open MeasureTheory Measure Metric Set Filter Module
open scoped ENNReal NNReal Topology

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

/-- A set of diameter `x < r` can be enlarged to diameter `x + 2 η ≤ r`, for some `η > 0`, while
changing `x ^ d` by at most `ε`. -/
private theorem exists_pos_rpow_le {x r ε : ℝ≥0∞} (hx : x ≠ ⊤) (hxr : x < r) (hε : 0 < ε)
    (d : ℝ) : ∃ η : ℝ≥0, 0 < η ∧ x + 2 * η ≤ r ∧
      ∀ y, x ≤ y → y ≤ x + 2 * η → y ^ d ≤ x ^ d + ε := by
  have hg : Tendsto (fun η : ℝ≥0 ↦ x + 2 * (η : ℝ≥0∞)) (𝓝 0) (𝓝 x) := by
    have hc : Continuous fun η : ℝ≥0 ↦ x + 2 * (η : ℝ≥0∞) := continuous_const.add
      ((ENNReal.continuous_const_mul ENNReal.ofNat_ne_top).comp ENNReal.continuous_coe)
    simpa using hc.tendsto 0
  have hpow : ∀ᶠ η : ℝ≥0 in 𝓝 0, ∀ y, x ≤ y → y ≤ x + 2 * η → y ^ d ≤ x ^ d + ε := by
    rcases le_or_gt 0 d with hd | hd
    · -- For `d ≥ 0` the power is monotone and continuous at the finite value `x`.
      have hlt : x ^ d < x ^ d + ε :=
        ENNReal.lt_add_right (ENNReal.rpow_ne_top_of_nonneg hd hx) hε.ne'
      filter_upwards [((ENNReal.continuous_rpow_const.tendsto x).comp hg).eventually_lt_const hlt]
        with η hη y _ hy
      exact (ENNReal.rpow_le_rpow hy hd).trans hη.le
    · -- For `d < 0` the power is antitone, so enlarging a set does not increase it.
      refine Eventually.of_forall fun η y hxy _ ↦ le_add_right ?_
      simpa [ENNReal.rpow_neg] using
        ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hxy (neg_nonneg.2 hd.le))
  obtain ⟨η, ⟨hηr, hηd⟩, hη0⟩ := (((hg.eventually_lt_const hxr).and hpow).filter_mono
    nhdsWithin_le_nhds |>.and self_mem_nhdsWithin).exists (f := 𝓝[>] (0 : ℝ≥0))
  exact ⟨η, hη0, hηr.le, hηd⟩

/-- Enlarging the sets of a cover to small open neighbourhoods shows that covers by open sets of
diameter at most `r` are as efficient as arbitrary covers of diameter at most `r' < r`. -/
private theorem openContent_le_content (d : ℝ) {r r' : ℝ≥0∞} (hr : r' < r) (s : Set X) :
    openContent d r s ≤ content d r' s := by
  refine le_iInf₂ fun t hst ↦ le_iInf fun htr ↦ ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨ε', hε'0, hε'⟩ := ENNReal.exists_pos_sum_of_countable (ENNReal.coe_ne_zero.2 hε.ne') ℕ
  choose η hη0 hηr hηd using fun n ↦ exists_pos_rpow_le
    ((htr n).trans_lt (hr.trans_le le_top)).ne ((htr n).trans_lt hr)
    (ENNReal.coe_pos.2 (hε'0 n)) d
  have hdiam (n : ℕ) : ediam (thickening (η n) (t n)) ≤ ediam (t n) + 2 * η n :=
    ediam_thickening_le _
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
        exact hηd n _ (ediam_mono (self_subset_thickening (NNReal.coe_pos.2 (hη0 n)) _))
          (hdiam n)
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

private theorem hausdorffMeasure_eq_iSup_content (d : ℝ) (s : Set X) :
    μH[d] s = ⨆ (r : ℝ≥0∞) (_ : 0 < r), content d r s :=
  hausdorffMeasure_apply d s

/-- Hausdorff measure is the countable supremum of the open-cover contents at the scales
`1 / k`. -/
private theorem hausdorffMeasure_eq_iSup_openContent (d : ℝ) (s : Set X) :
    μH[d] s = ⨆ k : ℕ, openContent d (k : ℝ≥0∞)⁻¹ s := by
  refine le_antisymm ?_ (iSup_le fun k ↦ ?_)
  · rw [hausdorffMeasure_eq_iSup_content]
    refine iSup₂_le fun r hr ↦ ?_
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hr.ne'
    exact (content_anti d hk.le s).trans ((content_le_openContent d _ s).trans
      (le_iSup (fun k : ℕ ↦ openContent d (k : ℝ≥0∞)⁻¹ s) k))
  · have hk : ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ < (k : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_lt_inv.2 (by exact_mod_cast k.lt_succ_self)
    refine (openContent_le_content d hk s).trans ?_
    rw [hausdorffMeasure_eq_iSup_content]
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

section Lipschitz

variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  [BorelSpace Y] (μ : Measure Y) [μ.IsAddHaarMeasure] {K : ℝ≥0} {t : ℝ}

/-- **Fiber measures of a Lipschitz map are almost everywhere measurable.** Let `f` be Lipschitz
on `A`, with values in an `m`-dimensional real normed space with additive Haar measure `μ`, and
let `t ≥ 0`. If `A` contains a σ-compact set `S` with `μH[m + t] (A \ S) = 0`, then
`y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable. -/
theorem LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage {f : X → Y} {A S : Set X}
    (hf : LipschitzOnWith K f A) (ht : 0 ≤ t) (hSA : S ⊆ A) (hS : IsSigmaCompact S)
    (hAS : μH[finrank ℝ Y + t] (A \ S) = 0) :
    AEMeasurable (fun y ↦ μH[t] (A ∩ f ⁻¹' {y})) μ := by
  refine (hS.measurable_hausdorffMeasure_inter_preimage (hf.continuousOn.mono hSA)
    t).aemeasurable.congr ?_
  -- By Eilenberg's inequality, almost every fiber of the null part `A \ S` is null.
  filter_upwards [(hf.mono sdiff_subset).ae_hausdorffMeasure_inter_preimage_eq_zero μ ht hAS]
    with y hy
  refine le_antisymm (measure_mono (inter_subset_inter_left _ hSA)) ?_
  calc μH[t] (A ∩ f ⁻¹' {y}) ≤ μH[t] (S ∩ f ⁻¹' {y}) + μH[t] ((A \ S) ∩ f ⁻¹' {y}) := by
        refine (measure_mono ?_).trans (measure_union_le _ _)
        rw [← union_inter_distrib_right, union_sdiff_self]
        exact inter_subset_inter_left _ subset_union_right
    _ = μH[t] (S ∩ f ⁻¹' {y}) := by rw [hy, add_zero]

/-- **Normalized fiber measures of a Lipschitz map on a Lebesgue measurable set are almost
everywhere measurable.** Let `f` be Lipschitz on a Lebesgue measurable subset `A` of an
`n`-dimensional real inner product space, with values in an `m`-dimensional real normed space
with additive Haar measure `μ`. If `n ≤ m + k`, then `y ↦ μHE[k] (A ∩ f ⁻¹' {y})` is
`μ`-almost everywhere measurable. This applies to the coarea dimension `k = n - m`, for which
`n ≤ m + k` is `le_add_tsub`. -/
theorem LipschitzOnWith.aemeasurable_euclideanHausdorffMeasure_inter_preimage {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {f : E → Y} {A : Set E} (hf : LipschitzOnWith K f A)
    (hA : NullMeasurableSet A) {k : ℕ} (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ μHE[k] (A ∩ f ⁻¹' {y})) μ := by
  obtain ⟨S, hSA, hS, hSA'⟩ := hA.exists_isSigmaCompact_subset_ae_eq
  -- The null part `A \ S` is null for the `n`-dimensional, hence the `(m + k)`-dimensional,
  -- Hausdorff measure.
  have hnull : μH[finrank ℝ Y + (k : ℝ)] (A \ S) = 0 := by
    have h := (ae_eq_set.1 hSA').2
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      euclideanHausdorffMeasure_eq_zero_iff] at h
    exact nonpos_iff_eq_zero.1 ((hausdorffMeasure_mono (by exact_mod_cast hk) _).trans h.le)
  simp only [euclideanHausdorffMeasure_def, Measure.smul_apply]
  exact (hf.aemeasurable_hausdorffMeasure_inter_preimage μ k.cast_nonneg hSA hS
    hnull).const_smul _

end Lipschitz
