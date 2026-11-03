/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Coarea.Eilenberg
public import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Null fibers of the zero-differential set

If a map between finite-dimensional real normed spaces has zero differential on a set, then
almost every fiber of that set has zero Hausdorff measure in the complementary dimension,
provided the target has positive dimension at most the source dimension. No measurability of
the set is needed, and differentiability within the set suffices.

For real-valued Lipschitz functions this also includes the nondifferentiability set: almost
every level surface meets the set where the totalized derivative vanishes in a Hausdorff-null
set. This removes the critical part of level surfaces in coarea arguments for rearrangements.
It is not Sard's theorem: the image of the critical set need not have measure zero.

The proof partitions the zero-differential set into pieces with arbitrarily small Lipschitz
constant and applies Eilenberg's inequality. Measurable majorants, rather than measurability
of the fiber measures, justify the almost-everywhere conclusion.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §3.4 (coarea and its critical-set argument).
-/

public section

open MeasureTheory Measure Set Filter Module
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [Nontrivial F]
  (μ : Measure F) [μ.IsAddHaarMeasure] {f : E → F} {s : Set E}

/-- On a zero-differential set, the fiber measures admit measurable majorants satisfying
Eilenberg's bound at every positive Lipschitz scale. -/
private theorem exists_measurable_majorant_of_hasFDerivWithinAt_zero
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (0 : E →L[ℝ] F) s x) {t : ℝ} (ht : 0 ≤ t)
    (ε : ℝ≥0) (hε : ε ≠ 0) :
    ∃ G : F → ℝ≥0∞, Measurable G ∧
      (∀ y, μH[t] (s ∩ f ⁻¹' {y}) ≤ G y) ∧
      ∫⁻ y, G y ∂μ ≤ μ (Metric.ball (0 : F) 1) * ε ^ finrank ℝ F *
        μH[finrank ℝ F + t] s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, measurable_const, by simp, by simp⟩
  obtain ⟨u, A, hdis, hum, hcover, happ, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fun _ ↦ 0) hf
      (fun _ ↦ ε) (fun _ ↦ hε)
  have hLip (n : ℕ) : LipschitzOnWith ε f (s ∩ u n) := by
    obtain ⟨x, hx, hAx⟩ := hA hs n
    have h := (happ n).lipschitzOnWith
    simpa [hAx] using h
  choose G hGm hGle hGint using fun n ↦
    (hLip n).exists_measurable_hausdorffMeasure_inter_preimage_le μ ht
  have hsum : ∑' n, μH[finrank ℝ F + t] (s ∩ u n) = μH[finrank ℝ F + t] s := by
    calc
      _ = ∑' n, (μH[finrank ℝ F + t].restrict s) (u n) := by
        congr 1
        funext n
        rw [Measure.restrict_apply (hum n), inter_comm]
      _ = (μH[finrank ℝ F + t].restrict s) (⋃ n, u n) :=
        (measure_iUnion hdis hum).symm
      _ = μH[finrank ℝ F + t] s := by
        rw [Measure.restrict_apply (MeasurableSet.iUnion hum), inter_eq_right.mpr hcover]
  refine ⟨fun y ↦ ∑' n, G n y, Measurable.tsum hGm, fun y ↦ ?_, ?_⟩
  · calc
      μH[t] (s ∩ f ⁻¹' {y}) ≤ μH[t] (⋃ n, (s ∩ u n) ∩ f ⁻¹' {y}) := by
        apply measure_mono
        intro x hx
        obtain ⟨n, hn⟩ := mem_iUnion.1 (hcover hx.1)
        exact mem_iUnion.2 ⟨n, ⟨hx.1, hn⟩, hx.2⟩
      _ ≤ ∑' n, μH[t] ((s ∩ u n) ∩ f ⁻¹' {y}) := measure_iUnion_le _
      _ ≤ ∑' n, G n y := tsum_le_tsum fun n ↦ hGle n y
  · rw [lintegral_tsum fun n ↦ (hGm n).aemeasurable]
    calc
      _ ≤ ∑' n, μ (Metric.ball (0 : F) 1) * ε ^ finrank ℝ F *
          μH[finrank ℝ F + t] (s ∩ u n) := tsum_le_tsum hGint
      _ = _ := by rw [ENNReal.tsum_mul_left, hsum]

/-- If the differential vanishes on a set of finite `(dim F + t)`-dimensional Hausdorff
measure, then almost every fiber has zero `t`-dimensional Hausdorff measure. Differentiability
within the set suffices, and no measurability of the set is required. -/
theorem ae_hausdorffMeasure_inter_preimage_eq_zero_of_hasFDerivWithinAt_zero_of_measure_ne_top
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (0 : E →L[ℝ] F) s x) {t : ℝ} (ht : 0 ≤ t)
    (hs : μH[finrank ℝ F + t] s ≠ ∞) :
    ∀ᵐ y ∂μ, μH[t] (s ∩ f ⁻¹' {y}) = 0 := by
  let ε : ℕ → ℝ≥0 := fun n ↦ 1 / ((n : ℝ≥0) + 1)
  have hε (n : ℕ) : ε n ≠ 0 := by positivity
  choose G hGm hGle hGint using fun n ↦
    exists_measurable_majorant_of_hasFDerivWithinAt_zero μ hf ht (ε n) (hε n)
  have hlim : Tendsto (fun n ↦ (ε n : ℝ≥0∞)) atTop (𝓝 0) :=
    ENNReal.tendsto_coe.2 tendsto_one_div_add_atTop_nhds_zero_nat
  have hbound : Tendsto (fun n ↦ μ (Metric.ball (0 : F) 1) *
      (ε n : ℝ≥0∞) ^ finrank ℝ F * μH[finrank ℝ F + t] s) atTop (𝓝 0) := by
    have hp := ENNReal.Tendsto.pow (n := finrank ℝ F) hlim
    simpa [zero_pow finrank_pos.ne'] using
      ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.const_mul hp (Or.inr (measure_ball_lt_top (μ := μ)).ne)) (Or.inr hs)
  have hzero : ∫⁻ y, liminf (fun n ↦ G n y) atTop ∂μ = 0 := by
    apply nonpos_iff_eq_zero.1
    calc
      _ ≤ liminf (fun n ↦ ∫⁻ y, G n y ∂μ) atTop := lintegral_liminf_le hGm
      _ ≤ liminf (fun n ↦ μ (Metric.ball (0 : F) 1) *
          (ε n : ℝ≥0∞) ^ finrank ℝ F * μH[finrank ℝ F + t] s) atTop :=
        liminf_le_liminf (Eventually.of_forall hGint)
      _ = 0 := hbound.liminf_eq
  filter_upwards [(lintegral_eq_zero_iff (Measurable.liminf hGm)).1 hzero] with y hy
  exact nonpos_iff_eq_zero.1 ((le_liminf_of_le (by isBoundedDefault)
    (Eventually.of_forall fun n ↦ hGle n y)).trans_eq hy)

/-- The zero-differential part of almost every fiber is Hausdorff-null in the complementary
dimension. This holds for any set, including nonmeasurable sets, on which the map has zero
derivative within that set. -/
theorem ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_hasFDerivWithinAt_zero
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (0 : E →L[ℝ] F) s x)
    (hdim : finrank ℝ F ≤ finrank ℝ E) :
    ∀ᵐ y ∂μ, μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) = 0 := by
  have hdim' : (finrank ℝ F : ℝ) + (finrank ℝ E - finrank ℝ F : ℕ) = finrank ℝ E := by
    exact_mod_cast Nat.add_sub_of_le hdim
  have hpiece (n : ℕ) : ∀ᵐ y ∂μ,
      μH[(finrank ℝ E - finrank ℝ F : ℕ)]
        ((s ∩ Metric.closedBall 0 n) ∩ f ⁻¹' {y}) = 0 := by
    apply ae_hausdorffMeasure_inter_preimage_eq_zero_of_hasFDerivWithinAt_zero_of_measure_ne_top μ
      (s := s ∩ Metric.closedBall 0 n)
      (fun x hx ↦ (hf x hx.1).mono inter_subset_left) (Nat.cast_nonneg _)
    rw [hdim']
    exact ne_top_of_le_ne_top (isCompact_closedBall (0 : E) (n : ℝ)).measure_lt_top.ne
      (measure_mono inter_subset_right)
  filter_upwards [ae_all_iff.2 hpiece] with y hy
  rw [euclideanHausdorffMeasure_eq_zero_iff]
  apply measure_mono_null (t := ⋃ n : ℕ, (s ∩ Metric.closedBall 0 n) ∩ f ⁻¹' {y})
  · intro x hx
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.2 ⟨n, ⟨hx.1, by simpa [Metric.mem_closedBall, dist_zero_right] using hn⟩, hx.2⟩
  · exact measure_iUnion_null hy

/-- For a Lipschitz map, the zero set of its totalized Fréchet derivative meets almost every
fiber in a Hausdorff-null set. The set includes nondifferentiability points, where the
totalized derivative `fderiv ℝ f x` is `0`.
For a real-valued function this is the nullity of the critical part of almost every level
surface. -/
theorem
    _root_.LipschitzWith.ae_euclideanHausdorffMeasure_setOf_fderiv_eq_zero_inter_preimage_eq_zero
    {K : ℝ≥0} (hf : LipschitzWith K f) (μ : Measure F) [μ.IsAddHaarMeasure]
    (hdim : finrank ℝ F ≤ finrank ℝ E) :
    ∀ᵐ y ∂μ, μHE[finrank ℝ E - finrank ℝ F]
      ({x | fderiv ℝ f x = 0} ∩ f ⁻¹' {y}) = 0 := by
  have hcritical : ∀ᵐ y ∂μ, μHE[finrank ℝ E - finrank ℝ F]
      ({x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x = 0} ∩ f ⁻¹' {y}) = 0 :=
    ae_euclideanHausdorffMeasure_inter_preimage_eq_zero_of_hasFDerivWithinAt_zero μ
      (fun x hx ↦ (hx.2 ▸ hx.1.hasFDerivAt).hasFDerivWithinAt) hdim
  have hnull : μHE[finrank ℝ E] {x | ¬DifferentiableAt ℝ f x} = 0 := by
    simpa only [ae_iff] using hf.ae_differentiableAt (μ := μHE[finrank ℝ E])
  have hexceptional : ∀ᵐ y ∂μ, μHE[finrank ℝ E - finrank ℝ F]
      ({x | ¬DifferentiableAt ℝ f x} ∩ f ⁻¹' {y}) = 0 := by
    apply hf.lipschitzOnWith.ae_euclideanHausdorffMeasure_inter_preimage_eq_zero μ
    simpa only [Nat.add_sub_of_le hdim] using hnull
  filter_upwards [hcritical, hexceptional] with y hcrit hexc
  apply measure_mono_null (t :=
    ({x | DifferentiableAt ℝ f x ∧ fderiv ℝ f x = 0} ∩ f ⁻¹' {y}) ∪
      ({x | ¬DifferentiableAt ℝ f x} ∩ f ⁻¹' {y}))
  · intro x hx
    by_cases hd : DifferentiableAt ℝ f x
    · exact Or.inl ⟨⟨hd, hx.1⟩, hx.2⟩
    · exact Or.inr ⟨hd, hx.2⟩
  · exact measure_union_null hcrit hexc

end MeasureTheory.Measure
