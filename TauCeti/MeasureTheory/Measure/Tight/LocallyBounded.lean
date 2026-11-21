/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Topology.UrysohnsLemma

/-!
# Weighting measures with locally bounded masses

On a locally compact, σ-compact Hausdorff space, let `μ i` be a family of measures whose masses
are bounded on every compact set uniformly in `i`. The family may have infinite total mass, and
it need not be tight. Multiplying every member by one strictly positive continuous weight `w`
makes it a tight family of uniformly bounded total mass.

The weight is `w = ∑ⱼ aⱼ gⱼ`, where `Kⱼ` is a compact exhaustion of the space, `gⱼ` is a
continuous cutoff with values in `[0, 1]`, equal to one on `Kⱼ` and supported in `Kⱼ₊₁`, and the
coefficient `aⱼ` is small compared with the uniform bound on the masses of `Kⱼ₊₁`. It is the
general form of the exponential weight `exp (-|x|)` used on the real line, and it reduces the
extraction of locally (vaguely) convergent subsequences of locally bounded measures to
Prokhorov's theorem for finite measures.

## Main statements

* `MeasureTheory.exists_weight_bound_isTightMeasureSet_withDensity`: a family of measures with
  uniformly bounded masses on compact sets becomes tight with bounded total mass after weighting
  by a strictly positive continuous function.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [TopologicalSpace α]

/-- The weight `∑ⱼ aⱼ gⱼ` built from cutoffs along a compact exhaustion and positive
coefficients `aⱼ ≤ 2⁻ʲ` is continuous and strictly positive, and the weighted mass of a
measurable set `s` is at most `∑ⱼ aⱼ ρ (K (j + 1) ∩ s)`. -/
private theorem exists_weight_le_tsum [T2Space α] [LocallyCompactSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (K : CompactExhaustion α) (a : ℕ → ℝ≥0)
    (ha_pos : ∀ j, 0 < a j) (ha_le : ∀ j, a j ≤ 2⁻¹ ^ j) :
    ∃ w : α → ℝ≥0, Continuous w ∧ (∀ x, 0 < w x) ∧ ∀ (ρ : Measure α) {s : Set α},
      MeasurableSet s →
        ρ.withDensity (fun x ↦ w x) s ≤ ∑' j, (a j : ℝ≥0∞) * ρ (K (j + 1) ∩ s) := by
  obtain ⟨g, hg1, hgs, hgr⟩ := K.exists_cutoffs
  -- The weight, as a uniformly convergent series of continuous functions.
  let f : ℕ → α → ℝ := fun j x ↦ a j * g j x
  have hf_nonneg (j : ℕ) (x : α) : 0 ≤ f j x := mul_nonneg (a j).2 (hgr j x).1
  have hf_le (j : ℕ) (x : α) : ‖f j x‖ ≤ 2⁻¹ ^ j := by
    rw [Real.norm_of_nonneg (hf_nonneg j x)]
    exact (mul_le_of_le_one_right (a j).2 (hgr j x).2).trans (by exact_mod_cast ha_le j)
  have hgeom : Summable fun j : ℕ ↦ (2⁻¹ : ℝ) ^ j := summable_geometric_two.congr fun j ↦ by simp
  have hsum (x : α) : Summable fun j ↦ f j x := .of_norm_bounded hgeom (hf_le · x)
  let w : α → ℝ≥0 := fun x ↦ ⟨∑' j, f j x, tsum_nonneg (hf_nonneg · x)⟩
  have hw_eq (x : α) : (w x : ℝ≥0∞) = ∑' j, (a j : ℝ≥0∞) * ENNReal.ofReal (g j x) := by
    have hw : (w x : ℝ) = ∑' j, f j x := NNReal.coe_mk _ _
    rw [← ENNReal.ofReal_coe_nnreal, hw, ENNReal.ofReal_tsum_of_nonneg (hf_nonneg · x) (hsum x)]
    simp only [f, ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  refine ⟨w, ?_, fun x ↦ ?_, fun ρ s hs ↦ ?_⟩
  · exact (continuous_tsum (fun j ↦ continuous_const.mul (g j).continuous) hgeom
      hf_le).subtype_mk _
  · obtain ⟨j, hj⟩ := K.exists_mem x
    have : (0 : ℝ) < f j x := by simpa [f, hg1 j hj] using ha_pos j
    exact_mod_cast this.trans_le ((hsum x).le_tsum j fun k _ ↦ hf_nonneg k x)
  -- Integrate the series term by term, bounding each cutoff by the indicator of `K (j + 1)`.
  rw [withDensity_apply _ hs]
  simp_rw [hw_eq]
  rw [lintegral_tsum fun j ↦
    ((g j).continuous.measurable.ennreal_ofReal.const_mul _).aemeasurable]
  refine tsum_le_tsum fun j ↦ ?_
  have hKm : MeasurableSet (K (j + 1)) := (K.isCompact _).isClosed.measurableSet
  have hgK (x : α) : ENNReal.ofReal (g j x) ≤ (K (j + 1)).indicator 1 x := by
    by_cases hx : x ∈ K (j + 1)
    · simpa [hx] using ENNReal.ofReal_le_ofReal (hgr j x).2
    · simp [hx, image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgs j h)]
  calc ∫⁻ x in s, (a j : ℝ≥0∞) * ENNReal.ofReal (g j x) ∂ρ
      ≤ ∫⁻ x in s, (a j : ℝ≥0∞) * (K (j + 1)).indicator 1 x ∂ρ :=
        lintegral_mono fun x ↦ by gcongr; exact hgK x
    _ = (a j : ℝ≥0∞) * ρ (K (j + 1) ∩ s) := by
        rw [lintegral_const_mul _ (measurable_one.indicator hKm), lintegral_indicator_one hKm,
          Measure.restrict_apply hKm]

/-- If the `j`-th coefficient times the mass of `K (j + 1)` is at most `4⁻ʲ`, then a set missing
`K m` gets at most `2 * 2⁻ᵐ` from the series of cutoff contributions. -/
private theorem tsum_mul_measure_inter_le [MeasurableSpace α] (K : CompactExhaustion α)
    (a : ℕ → ℝ≥0) (ρ : Measure α)
    (h : ∀ j, (a j : ℝ≥0∞) * ρ (K (j + 1)) ≤ 2⁻¹ ^ j * 2⁻¹ ^ j) (m : ℕ)
    {s : Set α} (hs : ∀ j < m, K (j + 1) ∩ s = ∅) :
    ∑' j, (a j : ℝ≥0∞) * ρ (K (j + 1) ∩ s) ≤ 2⁻¹ ^ m * 2 := by
  calc ∑' j, (a j : ℝ≥0∞) * ρ (K (j + 1) ∩ s)
      ≤ ∑' j, 2⁻¹ ^ m * 2⁻¹ ^ j := tsum_le_tsum fun j ↦ by
        rcases lt_or_ge j m with hjm | hmj
        · rw [hs j hjm, measure_empty, mul_zero]
          exact bot_le
        · calc (a j : ℝ≥0∞) * ρ (K (j + 1) ∩ s) ≤ (a j : ℝ≥0∞) * ρ (K (j + 1)) := by
                gcongr; exact inter_subset_left
            _ ≤ 2⁻¹ ^ j * 2⁻¹ ^ j := h j
            _ ≤ 2⁻¹ ^ m * 2⁻¹ ^ j := by
                gcongr ?_ * _
                exact pow_le_pow_of_le_one bot_le (by norm_num) hmj
    _ = 2⁻¹ ^ m * 2 := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

/-- A family of measures whose masses are bounded on every compact set, uniformly over the
family, becomes tight with total mass at most `2` after weighting by a strictly positive
continuous function. The measures may have infinite total mass. -/
theorem exists_weight_bound_isTightMeasureSet_withDensity [T2Space α] [LocallyCompactSpace α]
    [SigmaCompactSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] {ι : Type*}
    (μ : ι → Measure α)
    (hμ : ∀ K, IsCompact K → ⨆ i, μ i K ≠ ∞) :
    ∃ w : α → ℝ≥0, Continuous w ∧ (∀ x, 0 < w x) ∧
      (∀ i, (μ i).withDensity (fun x ↦ w x) univ ≤ 2) ∧
      IsTightMeasureSet (range fun i ↦ (μ i).withDensity fun x ↦ w x) := by
  let K := CompactExhaustion.choice α
  -- The uniform mass bound on `K (j + 1)` and the coefficient of the `j`-th cutoff.
  let T : ℕ → ℝ≥0 := fun j ↦ (⨆ i, μ i (K (j + 1))).toNNReal
  let a : ℕ → ℝ≥0 := fun j ↦ 2⁻¹ ^ j * 2⁻¹ ^ j / (T j + 1)
  have ha_le (j : ℕ) : a j ≤ 2⁻¹ ^ j :=
    (div_le_self bot_le (le_add_of_nonneg_left bot_le)).trans
      (mul_le_of_le_one_right' (pow_le_one₀ bot_le (by norm_num)))
  have haT (i : ι) (j : ℕ) : (a j : ℝ≥0∞) * μ i (K (j + 1)) ≤ 2⁻¹ ^ j * 2⁻¹ ^ j := by
    have hT : μ i (K (j + 1)) ≤ T j := by
      rw [ENNReal.coe_toNNReal (hμ _ (K.isCompact _))]
      exact le_iSup (fun i ↦ μ i (K (j + 1))) i
    have : a j * T j ≤ 2⁻¹ ^ j * 2⁻¹ ^ j := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      gcongr
      exact le_add_of_nonneg_right zero_le_one
    calc (a j : ℝ≥0∞) * μ i (K (j + 1)) ≤ (a j : ℝ≥0∞) * T j := by gcongr
      _ ≤ 2⁻¹ ^ j * 2⁻¹ ^ j := by simpa [ENNReal.inv_pow] using ENNReal.coe_le_coe.mpr this
  obtain ⟨w, hw, hpos, hle⟩ := exists_weight_le_tsum K a (fun j ↦ by positivity) ha_le
  have htail (i : ι) (m : ℕ) {s : Set α} (hsm : MeasurableSet s)
      (hs : ∀ j < m, K (j + 1) ∩ s = ∅) :
      (μ i).withDensity (fun x ↦ w x) s ≤ 2⁻¹ ^ m * 2 :=
    (hle (μ i) hsm).trans (tsum_mul_measure_inter_le K a (μ i) (haT i) m hs)
  refine ⟨w, hw, hpos, fun i ↦ ?_, ?_⟩
  · simpa using htail i 0 MeasurableSet.univ fun j hj ↦ absurd hj (Nat.not_lt_zero j)
  · refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr fun ε hε ↦ ?_
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_two_pow_lt (ENNReal.half_pos hε.ne').ne'
    refine ⟨K m, K.isCompact m, ?_⟩
    rintro ν ⟨i, rfl⟩
    refine (htail i m (K.isCompact m).isClosed.measurableSet.compl
      fun j hj ↦ by rw [← Set.sdiff_eq, Set.sdiff_eq_empty]; exact K.subset hj).trans ?_
    rw [← ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    exact hm.le

end MeasureTheory
