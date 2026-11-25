/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.UrysohnsLemma

/-!
# Tightness after weighting by a positive continuous function

On a locally compact, σ-compact R₁ space (for instance a Hausdorff one) whose open sets are
measurable, a set of measures whose masses on every compact set are uniformly bounded becomes
tight, with uniformly bounded total mass, after weighting every measure by one strictly positive
continuous function. The weight is a series of Urysohn cutoffs along a compact exhaustion, scaled
down by the mass bounds so that its tails are geometrically small. The measures themselves may have
infinite total mass.

## Main declarations

* `TauCeti.exists_isTightMeasureSet_withDensity_of_iSup_measure_ne_top`: under these hypotheses,
  a set of measures with uniformly bounded masses on every compact set becomes tight, with masses
  at most `2`, after weighting by a strictly positive continuous function.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]

/-- A term of the weight built in `exists_weight_of_iSup_measure_ne_top`: a cutoff `f ≤ 1`
supported in `T`, scaled by `(1 / 4) ^ k / (M + 1)` where `M` bounds `ν T`, integrates over `S`
to at most `(1 / 2) ^ N (1 / 2) ^ k` when `N ≤ k`, and to zero when `T` and `S` are disjoint. -/
private lemma ofReal_mul_setLIntegral_le {ν : Measure α} {T S : Set α} (hT : MeasurableSet T)
    {f : C(α, ℝ)} (hf : ∀ x, f x ≤ 1) (hfT : tsupport f ⊆ T) {M : ℝ}
    (hνT : ν T ≤ ENNReal.ofReal M) {k N : ℕ} (hkN : N ≤ k ∨ Disjoint T S) :
    ENNReal.ofReal ((1 / 4) ^ k * (M + 1)⁻¹) * ∫⁻ x in S, ENNReal.ofReal (f x) ∂ν ≤
      ENNReal.ofReal ((1 / 2) ^ N * (1 / 2) ^ k) := by
  -- The cutoff is at most the indicator of `T`, so its integral over `S` is at most `ν (T ∩ S)`.
  have hint : ∫⁻ x in S, ENNReal.ofReal (f x) ∂ν ≤ ν (T ∩ S) := by
    refine (lintegral_mono fun x ↦ ?_).trans_eq
      (by rw [lintegral_indicator_one hT, Measure.restrict_apply hT])
    by_cases hx : x ∈ T
    · simpa [hx] using ENNReal.ofReal_le_one.2 (hf x)
    · simp [hx, image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfT h)]
  rcases hkN with hNk | hTS
  · -- A negative bound `M` forces `ν T = 0`.
    rcases lt_or_ge M 0 with hM | hM
    · have : ∫⁻ x in S, ENNReal.ofReal (f x) ∂ν = 0 := le_antisymm ((hint.trans
          (measure_mono inter_subset_left)).trans (hνT.trans_eq (ENNReal.ofReal_of_nonpos hM.le)))
          zero_le
      simp [this]
    grw [hint, measure_mono inter_subset_left, hνT, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : M * (M + 1)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ (by linarith)]
      linarith
    have h2 : ((1 : ℝ) / 2) ^ k ≤ (1 / 2) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hNk
    have hquarter : (1 / 4 : ℝ) = 1 / 2 * (1 / 2) := by norm_num
    calc (1 / 4) ^ k * (M + 1)⁻¹ * M = (1 / 2) ^ k * (1 / 2) ^ k * (M * (M + 1)⁻¹) := by
          rw [hquarter, mul_pow]; ring
      _ ≤ (1 / 2) ^ k * (1 / 2) ^ k := mul_le_of_le_one_right (by positivity) h1
      _ ≤ (1 / 2) ^ N * (1 / 2) ^ k := by gcongr
  · have : ∫⁻ x in S, ENNReal.ofReal (f x) ∂ν = 0 :=
      le_antisymm (hint.trans (by rw [hTS.inter_eq, measure_empty])) zero_le
    simp [this]

/-- An exhausting sequence of cutoffs gives a positive continuous weight whose integrals against
the measures of a set with uniformly bounded masses on compact sets are uniformly bounded, with
uniformly small tails outside the exhaustion. -/
private lemma exists_weight_of_iSup_measure_ne_top [R1Space α] [OpensMeasurableSpace α]
    [LocallyCompactSpace α] [SigmaCompactSpace α] {S : Set (Measure α)}
    (hS : ∀ K, IsCompact K → ⨆ μ ∈ S, μ K ≠ ∞) :
    ∃ (w : α → ℝ≥0) (K : CompactExhaustion α), Continuous w ∧ (∀ x, 0 < w x) ∧
      ∀ (A : Set α) (N : ℕ), (∀ k < N, Disjoint (K (k + 1)) A) → ∀ μ ∈ S,
        ∫⁻ x in A, w x ∂μ ≤ ENNReal.ofReal ((1 / 2) ^ N * 2) := by
  let K := CompactExhaustion.choice α
  -- Cutoffs `0 ≤ f k ≤ 1`, equal to one on `K k` and supported in `K (k + 1)`.
  choose f hfK _ hfV hfr using fun k : ℕ ↦ exists_continuousMap_one_of_isCompact_subset_isOpen
    (K.isCompact k) isOpen_interior (K.subset_interior_succ k)
  -- The weight is `∑ a k f k`, where `a k = (1 / 4) ^ k / (M k + 1)` and `M k` bounds the masses
  -- of `K (k + 1)`.
  let M : ℕ → ℝ := fun k ↦ (⨆ μ ∈ S, μ (K (k + 1))).toReal
  let a : ℕ → ℝ := fun k ↦ (1 / 4) ^ k * (M k + 1)⁻¹
  have hM (k : ℕ) : 0 ≤ M k := ENNReal.toReal_nonneg
  have ha (k : ℕ) : 0 < a k := by positivity
  have hsum : Summable a :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).of_nonneg_of_le
      (fun k ↦ (ha k).le) fun k ↦
        mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ (by linarith [hM k]))
  have hterm (k : ℕ) (x : α) : 0 ≤ a k * f k x := mul_nonneg (ha k).le (hfr k x).1
  have hle (k : ℕ) (x : α) : a k * f k x ≤ a k := mul_le_of_le_one_right (ha k).le (hfr k x).2
  have hsumx (x : α) : Summable fun k ↦ a k * f k x :=
    hsum.of_nonneg_of_le (hterm · x) (hle · x)
  refine ⟨fun x ↦ (∑' k, a k * f k x).toNNReal, K, ?_, fun x ↦ ?_, fun A N hAN μ hμ ↦ ?_⟩
  · exact continuous_real_toNNReal.comp (continuous_tsum (f := fun k x ↦ a k * f k x)
      (fun k ↦ continuous_const.mul (f k).continuous) hsum fun k x ↦ by
        rw [Real.norm_of_nonneg (hterm k x)]; exact hle k x)
  · obtain ⟨k, hk⟩ := K.exists_mem x
    refine Real.toNNReal_pos.2 ((ha k).trans_le ((le_of_eq ?_).trans
      ((hsumx x).le_tsum k fun j _ ↦ hterm j x)))
    rw [hfK k hk, Pi.one_apply, mul_one]
  -- Expand the weight and bound the `k`-th term by `(1 / 2) ^ N (1 / 2) ^ k`.
  have hw (x : α) : ((∑' k, a k * f k x).toNNReal : ℝ≥0∞) =
      ∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal (f k x) := by
    rw [ENNReal.ofNNReal_toNNReal, ENNReal.ofReal_tsum_of_nonneg (hterm · x) (hsumx x)]
    exact tsum_congr fun k ↦ ENNReal.ofReal_mul (ha k).le
  have hgeom : ENNReal.ofReal ((1 / 2) ^ N * 2) =
      ∑' k, ENNReal.ofReal ((1 / 2) ^ N * (1 / 2) ^ k) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun k : ℕ ↦ (1 / 2 : ℝ) ^ N * (1 / 2) ^ k)
      (fun k ↦ by positivity) (summable_geometric_two.mul_left _), tsum_mul_left,
      tsum_geometric_two]
  simp_rw [hw]
  rw [lintegral_tsum fun k ↦
    ((f k).continuous.measurable.ennreal_ofReal.const_mul _).aemeasurable, hgeom]
  refine tsum_le_tsum fun k ↦ ?_
  rw [lintegral_const_mul _ (f k).continuous.measurable.ennreal_ofReal]
  -- Compact sets need not be closed, so the cutoff is compared with its closed support.
  refine ofReal_mul_setLIntegral_le (isClosed_tsupport _).measurableSet (fun x ↦ (hfr k x).2)
    subset_rfl ?_ ((le_or_gt N k).imp_right fun hk ↦ (hAN k hk).mono_left
      ((hfV k).trans interior_subset))
  rw [ENNReal.ofReal_toReal (hS _ (K.isCompact (k + 1)))]
  exact (measure_mono ((hfV k).trans interior_subset)).trans
    (le_iSup₂ (f := fun ν (_ : ν ∈ S) ↦ ν (K (k + 1))) μ hμ)

/-- **Tight weighting.** On a locally compact, σ-compact R₁ space (for instance a Hausdorff one)
whose open sets are measurable, a set `S` of measures with uniformly bounded masses on every
compact set becomes tight, with total masses at most `2`, after weighting by a suitable strictly
positive continuous function `w`. -/
theorem exists_isTightMeasureSet_withDensity_of_iSup_measure_ne_top [R1Space α]
    [OpensMeasurableSpace α] [LocallyCompactSpace α] [SigmaCompactSpace α] {S : Set (Measure α)}
    (hS : ∀ K, IsCompact K → ⨆ μ ∈ S, μ K ≠ ∞) :
    ∃ w : α → ℝ≥0, Continuous w ∧ (∀ x, 0 < w x) ∧
      (∀ μ ∈ S, (μ.withDensity fun x ↦ w x) univ ≤ (2 : ℝ≥0)) ∧
      IsTightMeasureSet ((fun μ : Measure α ↦ μ.withDensity fun x ↦ w x) '' S) := by
  obtain ⟨w, K, hw, hpos, htail⟩ := exists_weight_of_iSup_measure_ne_top hS
  refine ⟨w, hw, hpos, fun μ hμ ↦ ?_, ?_⟩
  -- The total mass is the case `A = univ`, `N = 0`.
  · rw [withDensity_apply _ MeasurableSet.univ]
    simpa using htail univ 0 (fun k hk ↦ absurd hk (Nat.not_lt_zero k)) μ hμ
  -- The tails outside the compact closure of `K N` are uniformly small.
  · refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε hε ↦ ?_
    have hlim : Tendsto (fun N : ℕ ↦ ENNReal.ofReal ((1 / 2) ^ N * 2)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (1 : ℝ) / 2) (by norm_num) (by norm_num)).mul_const 2)
    obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
    refine ⟨closure (K N), (K.isCompact N).closure, ?_⟩
    rintro - ⟨μ, hμ, rfl⟩
    rw [withDensity_apply _ isClosed_closure.measurableSet.compl]
    exact (htail _ N (fun k hk ↦ disjoint_compl_right_iff_subset.2
      ((K.subset (Nat.succ_le_of_lt hk)).trans subset_closure)) μ hμ).trans hN.le

end TauCeti
