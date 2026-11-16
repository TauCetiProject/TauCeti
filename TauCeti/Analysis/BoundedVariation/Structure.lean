/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.Geometry.Euclidean.Volume.Measure
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.Analysis.BoundedVariation.DensityEstimates
import TauCeti.Geometry.MeasureTheory.Rectifiable.Cone
import TauCeti.Geometry.MeasureTheory.Rectifiable.Density
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# De Giorgi's structure theorem for sets of finite perimeter

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 2`, let `Ω` be an open
subset of `E`, and let `s ⊆ E` be a set. This file proves **De Giorgi's structure theorem** for the
reduced boundary `∂*s` (`TauCeti.reducedBoundary`) and the perimeter measure `|Dχ_s|`
(`TauCeti.variationMeasure`).

* **Countable rectifiability** (`TauCeti.countablyRectifiable_reducedBoundary`): against any
  additive Haar measure `μ`, the reduced boundary `∂*s` is countably `(n - 1)`-rectifiable. By the
  density-one-half theorem (`TauCeti.hasDensityAt_of_mem_reducedBoundary`), `∂*s` is the countable
  union of the subsets `F_N` on which both `s` and `sᶜ` fill at least a quarter of every ball of
  radius at most `1 / (N + 1)`. At each point `x ∈ ∂*s`, blow-up convergence to the half-space
  `{w | ⟪w, ν_s x⟫ < 0}` (`TauCeti.tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter`)
  forces every nearby point `y ∈ F_N` to lie in the cone `|⟪y - x, ν_s x⟫| ≤ (1 / 2) ‖y - x‖`;
  otherwise a small ball around `(y - x) / ‖y - x‖` lies entirely on one side of the limiting
  half-space while carrying positive measure of both the blow-up and its complement. The
  codimension-one cone criterion (`TauCeti.CountablyRectifiable.of_forall_exists_unit_abs_inner_le`)
  then makes each `F_N` countably `(n - 1)`-rectifiable.
* **Identification of the perimeter measure**
  (`TauCeti.map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary`): for
  Lebesgue measure, the pushforward of `|Dχ_s|` to `E` equals `(n - 1)`-dimensional Euclidean
  Hausdorff measure restricted to the reduced boundary:
  `|Dχ_s| = μHE[n - 1]⌊∂*s`.
  On each precompact open subset `U` of `Ω`, the upper density estimate
  (`TauCeti.variationMeasure_preimage_le_mul_hausdorffMeasure`) and concentration on `∂*s`
  (`TauCeti.ae_mem_reducedBoundary`) show `|Dχ_s|⌊U ≪ μHE[n - 1]⌊(∂*s ∩ U)`, while the lower
  density bound (`MeasureTheory.Measure.mul_euclideanHausdorffMeasure_le_measure_of_isOpen`) shows
  `μHE[n - 1] (∂*s ∩ U) < ∞`. Combining density one of `|Dχ_s|`
  (`TauCeti.tendsto_variationMeasure_closedBall_div_volume_closedBall`) with the density theorem
  for rectifiable sets
  (`TauCeti.CountablyRectifiable.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div`) gives
  Radon–Nikodym derivative `1` via Besicovitch differentiation (`Besicovitch.ae_tendsto_rnDeriv`).
  Exhausting `Ω` by precompact open sets yields the global identity.
* **Perimeter, integrals, and the Gauss–Green theorem**: evaluating the measure identity gives
  `|Dχ_s|(A) = μHE[n - 1] (A ∩ ∂*s)` for every set `A`
  (`TauCeti.variationMeasure_preimage_eq_euclideanHausdorffMeasure_inter_reducedBoundary`),
  `P(s; U) = μHE[n - 1] (U ∩ ∂*s)` and `P(s; Ω) = μHE[n - 1] (∂*s)` for sets of locally finite
  perimeter (`TauCeti.perimeter_eq_euclideanHausdorffMeasure_inter_reducedBoundary`,
  `TauCeti.perimeter_eq_euclideanHausdorffMeasure_reducedBoundary`), transport of Lebesgue and
  Bochner integrals (`TauCeti.lintegral_variationMeasure_eq_setLIntegral_reducedBoundary`,
  `TauCeti.integral_variationMeasure_eq_setIntegral_reducedBoundary`), and the surface-measure
  **Gauss–Green theorem** `Dχ_s = -ν_s μHE[n - 1]⌊∂*s`:
  `∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dμHE[n - 1]` for every compactly supported `C¹` vector field `φ`
  on `Ω` (`TauCeti.integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal`) and every
  test vector field `φ : 𝓓(Ω, E)`
  (`TauCeti.integral_divergenceCLM_mul_indicator_eq_setIntegral_inner_outerNormal`).

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 15 (Theorem
  15.9, De Giorgi's structure theorem).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.3 (Theorem 5.15, Structure theorem for sets of finite perimeter).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.59.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric Module TestFunction
open scoped ENNReal NNReal Topology RealInnerProductSpace Distributions symmDiff

section Rectifiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E}

/-- At a point `x` of the reduced boundary, every nearby point `y` where both `s` and `sᶜ` fill at
least a quarter of every ball of radius at most `1 / (N + 1)` lies inside the cone
`|⟪y - x, ν_s x⟫| ≤ (1 / 2) ‖y - x‖`. -/
private theorem exists_ball_abs_inner_le_of_uniform_density [μ.IsAddHaarMeasure]
    (hn : 2 ≤ finrank ℝ E) {x : E} (hx : x ∈ reducedBoundary μ Ω s) (N : ℕ) :
    ∃ δ > (0 : ℝ), ∀ y ∈ ball x δ,
      (∀ r ∈ Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
        (1 / 4 : ℝ≥0∞) * μ (closedBall y r) ≤ μ (s ∩ closedBall y r) ∧
        (1 / 4 : ℝ≥0∞) * μ (closedBall y r) ≤ μ (sᶜ ∩ closedBall y r)) →
      |⟪y - x, outerNormal μ Ω s x⟫| ≤ (1 / 2 : ℝ) * ‖y - x‖ := by
  set ν := outerNormal μ Ω s x
  have hν1 : ‖ν‖ = 1 := norm_outerNormal hx
  set c₀ : ℝ≥0∞ := (1 / 4 : ℝ≥0∞) * μ (closedBall (0 : E) (1 / 4))
  have hc₀ : 0 < c₀ := ENNReal.mul_pos (by norm_num)
    (measure_closedBall_pos μ (0 : E) (by norm_num)).ne'
  have hblow := tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx
    (isCompact_closedBall (0 : E) 2)
  obtain ⟨δ₁, hδ₁, hδ₁lt⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 (hblow.eventually (gt_mem_nhds hc₀))
  refine ⟨min δ₁ (1 / ((N : ℝ) + 1)), lt_min hδ₁ (by positivity), fun y hy hdens => ?_⟩
  rcases eq_or_ne y x with rfl | hyx
  · simp
  set r : ℝ := ‖y - x‖
  have hr0 : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  have hrδ : r < min δ₁ (1 / ((N : ℝ) + 1)) := by simpa [r, dist_eq_norm] using hy
  by_contra hgt
  push Not at hgt
  -- Rescale `y - x` to a unit vector `z` and place the ball `closedBall z (1 / 4)` inside
  -- `closedBall 0 2`, strictly on one side of the limiting half-space `{w | ⟪w, ν⟫ < 0}`.
  set z : E := r⁻¹ • (y - x)
  have hz1 : ‖z‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr0), inv_mul_cancel₀ hr0.ne']
  have hB2 : closedBall z (1 / 4 : ℝ) ⊆ closedBall (0 : E) 2 := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ 1 / 4 + 1 := by linarith [mem_closedBall_iff_norm.1 hw, hz1]
      _ ≤ 2 := by norm_num
  have hpreBall : (fun w => x + r • w) ⁻¹' closedBall y ((1 / 4) * r) = closedBall z (1 / 4) := by
    ext w
    simp only [mem_preimage, mem_closedBall_iff_norm]
    have hsub : x + r • w - y = r • (w - z) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
      abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hr0, mul_comm (1 / 4 : ℝ) r,
      mul_le_mul_iff_right₀ hr0]
  -- Pull back the quarter-density bound at `y` to `closedBall z (1 / 4)`.
  have hscale (t : Set E)
      (ht : (1 / 4 : ℝ≥0∞) * μ (closedBall y ((1 / 4) * r)) ≤ μ (t ∩ closedBall y ((1 / 4) * r))) :
      c₀ ≤ μ (((fun w => x + r • w) ⁻¹' t) ∩ closedBall z (1 / 4)) := by
    calc c₀ = (1 / 4 : ℝ≥0∞) * μ (closedBall z (1 / 4)) := by
          rw [Measure.addHaar_closedBall_center μ z]
      _ = (1 / 4 : ℝ≥0∞) *
            (ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * μ (closedBall y ((1 / 4) * r))) := by
          rw [← hpreBall, Measure.addHaar_preimage_add_smul μ x hr0.ne']
      _ = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| *
            ((1 / 4 : ℝ≥0∞) * μ (closedBall y ((1 / 4) * r))) := by ring
      _ ≤ ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * μ (t ∩ closedBall y ((1 / 4) * r)) :=
          mul_le_mul_right ht _
      _ = μ (((fun w => x + r • w) ⁻¹' t) ∩ closedBall z (1 / 4)) := by
          rw [← hpreBall, ← preimage_inter, Measure.addHaar_preimage_add_smul μ x hr0.ne']
  have hdens' := hdens ((1 / 4) * r) ⟨by positivity, by
    linarith [hrδ.trans_le (min_le_right _ _)]⟩
  have hsmall : μ ((((fun w => x + r • w) ⁻¹' s) ∆ {w | ⟪w, ν⟫ < 0}) ∩ closedBall 0 2) < c₀ :=
    hδ₁lt ⟨hr0, hrδ.le.trans (min_le_left _ _)⟩
  have hzν : (1 / 2 : ℝ) < |⟪z, ν⟫| := by
    rw [real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.2 hr0), inv_mul_eq_div,
      lt_div_iff₀ hr0]
    exact hgt
  have hw_diff {w : E} (hwB : w ∈ closedBall z (1 / 4 : ℝ)) : |⟪w, ν⟫ - ⟪z, ν⟫| ≤ 1 / 4 := by
    rw [← inner_sub_left]
    calc |⟪w - z, ν⟫| ≤ ‖w - z‖ * ‖ν‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 / 4 * 1 := mul_le_mul (mem_closedBall_iff_norm.1 hwB) hν1.le (norm_nonneg _)
          (by norm_num)
      _ = 1 / 4 := mul_one _
  -- Depending on the sign of `⟪z, ν⟫`, `closedBall z (1 / 4)` lies either outside or inside the
  -- half-space `{w | ⟪w, ν⟫ < 0}`, forcing `c₀ ≤ μ((s_{x,r} ∆ H) ∩ closedBall 0 2) < c₀`.
  rcases le_or_gt 0 ⟪z, ν⟫ with hpos | hneg
  · rw [abs_of_nonneg hpos] at hzν
    have hsub : ((fun w => x + r • w) ⁻¹' s) ∩ closedBall z (1 / 4) ⊆
        (((fun w => x + r • w) ⁻¹' s) ∆ {w | ⟪w, ν⟫ < 0}) ∩ closedBall 0 2 := by
      rintro w ⟨hws, hwB⟩
      refine ⟨Or.inl ⟨hws, ?_⟩, hB2 hwB⟩
      simp only [mem_ofPred_eq, not_lt]
      linarith [(abs_le.1 (hw_diff hwB)).1]
    exact hsmall.not_ge ((hscale s hdens'.1).trans (measure_mono hsub))
  · rw [abs_of_neg hneg] at hzν
    have hsub : ((fun w => x + r • w) ⁻¹' sᶜ) ∩ closedBall z (1 / 4) ⊆
        (((fun w => x + r • w) ⁻¹' s) ∆ {w | ⟪w, ν⟫ < 0}) ∩ closedBall 0 2 := by
      rintro w ⟨hws, hwB⟩
      refine ⟨Or.inr ⟨?_, hws⟩, hB2 hwB⟩
      simp only [mem_ofPred_eq]
      linarith [(abs_le.1 (hw_diff hwB)).2]
    exact hsmall.not_ge ((hscale sᶜ hdens'.2).trans (measure_mono hsub))

/-- **De Giorgi's structure theorem (rectifiability).** Let `E` have dimension `n ≥ 2` and let `μ`
be an additive Haar measure. The reduced boundary `∂*s` of any set `s` in an open set `Ω` is
countably `(n - 1)`-rectifiable. -/
theorem countablyRectifiable_reducedBoundary [μ.IsAddHaarMeasure] (hn : 2 ≤ finrank ℝ E) :
    CountablyRectifiable (finrank ℝ E - 1) (reducedBoundary μ Ω s) := by
  let F (N : ℕ) : Set E :=
    {y ∈ reducedBoundary μ Ω s | ∀ r ∈ Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
      (1 / 4 : ℝ≥0∞) * μ (closedBall y r) ≤ μ (s ∩ closedBall y r) ∧
      (1 / 4 : ℝ≥0∞) * μ (closedBall y r) ≤ μ (sᶜ ∩ closedBall y r)}
  have hrect (N : ℕ) : CountablyRectifiable (finrank ℝ E - 1) (F N) := by
    refine CountablyRectifiable.of_forall_exists_unit_abs_inner_le fun x hx => ?_
    obtain ⟨δ, hδ, hcone⟩ := exists_ball_abs_inner_le_of_uniform_density hn hx.1 N
    exact ⟨outerNormal μ Ω s x, norm_outerNormal hx.1, 1 / 2, by norm_num, δ, hδ,
      fun y hy => hcone y hy.2 hy.1.2⟩
  have hcov : reducedBoundary μ Ω s ⊆ ⋃ N : ℕ, F N := by
    intro y hy
    have hs1 : (1 / 4 : ℝ≥0∞) < 1 / 2 := by
      simpa only [one_div] using ENNReal.inv_lt_inv.2 (by norm_num : (2 : ℝ≥0∞) < 4)
    have h1 := (hasDensityAt_iff.1 (hasDensityAt_of_mem_reducedBoundary hn hy)).eventually
      (lt_mem_nhds hs1)
    have hyc : y ∈ reducedBoundary μ Ω sᶜ := by rwa [reducedBoundary_compl]
    have h2 := (hasDensityAt_iff.1 (hasDensityAt_of_mem_reducedBoundary hn hyc)).eventually
      (lt_mem_nhds hs1)
    obtain ⟨δ, hδ, hδle⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 (h1.and h2)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine mem_iUnion.2 ⟨N, hy, fun r hr => ?_⟩
    have hrδ : r ∈ Ioc 0 δ := ⟨hr.1, hr.2.trans hN.le⟩
    have hB0 : μ (closedBall y r) ≠ 0 := (measure_closedBall_pos μ y hr.1).ne'
    have hBtop : μ (closedBall y r) ≠ ∞ := measure_closedBall_lt_top.ne
    exact ⟨(ENNReal.le_div_iff_mul_le (.inl hB0) (.inl hBtop)).1 (hδle hrδ).1.le,
      (ENNReal.le_div_iff_mul_le (.inl hB0) (.inl hBtop)).1 (hδle hrδ).2.le⟩
  exact (CountablyRectifiable.iUnion hrect).mono hcov

end Rectifiability

section PerimeterMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {s : Set E}

/-- The pushforward of the perimeter measure restricted to a set `U` is absolutely continuous with
respect to `μHE[n - 1]` restricted to `∂*s ∩ U`. -/
private theorem restrict_map_variationMeasure_absolutelyContinuous (U : Set E) :
    ((variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)).restrict U ≪
      μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s ∩ U) := by
  refine Measure.AbsolutelyContinuous.mk fun A hAm hA0 => ?_
  have hAU0 : μHE[finrank ℝ E - 1] (A ∩ (reducedBoundary volume Ω s ∩ U)) = 0 := by
    simpa [Measure.restrict_apply hAm] using hA0
  have hH0 : μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (A ∩ (reducedBoundary volume Ω s ∩ U)) = 0 := by
    rw [euclideanHausdorffMeasure_eq_smul_hausdorffMeasure, _root_.smul_apply, smul_eq_mul,
      mul_eq_zero] at hAU0
    exact hAU0.resolve_left (EuclideanSpace.volume_ball_div_two_pow_ne_zero _)
  have hlam_inter : variationMeasure volume Ω (s.indicator 1)
      (((↑) : Ω → E) ⁻¹' (A ∩ (reducedBoundary volume Ω s ∩ U))) = 0 := by
    have hle := variationMeasure_preimage_le_mul_hausdorffMeasure (μ := volume) (Ω := Ω) (s := s)
      (A := A ∩ (reducedBoundary volume Ω s ∩ U)) (inter_subset_right.trans inter_subset_left)
    simpa [hH0] using hle
  have hsub : ((↑) : Ω → E) ⁻¹' (A ∩ U) ⊆
      (((↑) : Ω → E) ⁻¹' (A ∩ (reducedBoundary volume Ω s ∩ U))) ∪
      (((↑) : Ω → E) ⁻¹' (reducedBoundary volume Ω s)ᶜ) := by
    intro y ⟨hyA, hyU⟩
    by_cases hyR : (y : E) ∈ reducedBoundary volume Ω s
    · exact Or.inl ⟨hyA, hyR, hyU⟩
    · exact Or.inr hyR
  have hzero : variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' (A ∩ U)) = 0 :=
    measure_mono_null hsub (measure_union_null hlam_inter ae_mem_reducedBoundary)
  simpa [Measure.restrict_apply hAm, Ω.isOpenEmbedding'.measurableEmbedding.map_apply] using hzero

/-- On any open set `U` where the pushed-forward perimeter measure is finite, `∂*s ∩ U` has finite
`(n - 1)`-dimensional Euclidean Hausdorff measure. -/
private theorem euclideanHausdorffMeasure_reducedBoundary_inter_lt_top (hn : 2 ≤ finrank ℝ E)
    {U : Set E} (hU : IsOpen U)
    [hfin : IsFiniteMeasure
      (((variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)).restrict U)] :
    μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩ U) < ∞ := by
  set k := finrank ℝ E - 1
  set ν₁ : Measure E := ((variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)).restrict U
  have hlow : (1 / 2 : ℝ≥0∞) * μHE[k] (reducedBoundary volume Ω s ∩ U) ≤ ν₁ U := by
    refine Measure.mul_euclideanHausdorffMeasure_le_measure_of_isOpen ν₁ k hU
      inter_subset_right fun x hx => ?_
    have hball : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν₁ (closedBall x r) =
        variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (eventually_closedBall_subset (hU.mem_nhds hx.2))] with r hr
      rw [Measure.restrict_apply measurableSet_closedBall, inter_eq_left.2 hr,
        Ω.isOpenEmbedding'.measurableEmbedding.map_apply]
    have hgt : (1 / 2 : ℝ≥0∞) < 1 := by
      rw [ENNReal.div_lt_iff (.inl two_ne_zero) (.inl ENNReal.ofNat_ne_top)]
      norm_num
    refine (((tendsto_variationMeasure_closedBall_div_volume_closedBall hn hx.1).eventually
      (lt_mem_nhds hgt)).and (hball.and self_mem_nhdsWithin)).frequently.mono
      fun r ⟨hdiv, hbr, (hr : 0 < r)⟩ => ?_
    rw [hbr]
    have hV0 : volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≠ 0 :=
      (measure_closedBall_pos volume 0 hr).ne'
    have hVtop : volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≠ ∞ :=
      measure_closedBall_lt_top.ne
    exact (ENNReal.le_div_iff_mul_le (.inl hV0) (.inl hVtop)).1 hdiv.le
  have hne : μHE[k] (reducedBoundary volume Ω s ∩ U) ≠ ∞ := fun htop => by
    have htop' : (1 / 2 : ℝ≥0∞) * μHE[k] (reducedBoundary volume Ω s ∩ U) = ∞ := by
      rw [htop]
      exact ENNReal.mul_top (by norm_num)
    exact (measure_lt_top ν₁ U).ne (top_unique (htop' ▸ hlow))
  exact hne.lt_top

/-- Local form of De Giorgi's measure identity: on every open set `U` with compact closure inside
`Ω`, the pushforward of the perimeter measure agrees with `μHE[n - 1]` restricted to `∂*s ∩ U`. -/
private theorem restrict_map_variationMeasure_eq_restrict_euclideanHausdorffMeasure
    (hn : 2 ≤ finrank ℝ E) {U : Set E} (hU : IsOpen U) (hKU : IsCompact (closure U))
    (hKUΩ : closure U ⊆ Ω) :
    ((variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)).restrict U =
      μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s ∩ U) := by
  have := Ω.isOpen.locallyCompactSpace
  set k := finrank ℝ E - 1
  set lam := variationMeasure volume Ω (s.indicator 1)
  set R := reducedBoundary volume Ω s
  set ν₁ : Measure E := (lam.map ((↑) : Ω → E)).restrict U
  set ν₂ : Measure E := μHE[k].restrict (R ∩ U)
  have hRUm : MeasurableSet (R ∩ U) := measurableSet_reducedBoundary.inter hU.measurableSet
  have hν₁_fin : IsFiniteMeasure ν₁ := by
    refine ⟨?_⟩
    have hK : IsCompact (((↑) : Ω → E) ⁻¹' closure U) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hKU (by rwa [Subtype.range_coe])
    calc ν₁ univ = lam (((↑) : Ω → E) ⁻¹' U) := by
          rw [Measure.restrict_apply_univ, Ω.isOpenEmbedding'.measurableEmbedding.map_apply]
      _ ≤ lam (((↑) : Ω → E) ⁻¹' closure U) := measure_mono (preimage_mono subset_closure)
      _ < ∞ := hK.measure_lt_top
  have hν₂_fin : IsFiniteMeasure ν₂ :=
    ⟨by simpa [ν₂, Measure.restrict_apply_univ] using
      euclideanHausdorffMeasure_reducedBoundary_inter_lt_top (Ω := Ω) (s := s) hn hU⟩
  have hac : ν₁ ≪ ν₂ := restrict_map_variationMeasure_absolutelyContinuous U
  have hdens_rect := ((countablyRectifiable_reducedBoundary (μ := volume) (Ω := Ω) (s := s) hn).mono
    inter_subset_left).ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div
    hRUm.nullMeasurableSet
  -- By Besicovitch differentiation and the rectifiable density theorem, `dν₁ / dν₂ = 1` a.e.
  have hrn : ν₁.rnDeriv ν₂ =ᵐ[ν₂] 1 := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv ν₁ ν₂, ae_restrict_mem hRUm,
      ae_restrict_of_ae hdens_rect] with x hrn hx hμ₂
    have hball : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ν₁ (closedBall x r) = lam (((↑) : Ω → E) ⁻¹' closedBall x r) := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (eventually_closedBall_subset (hU.mem_nhds hx.2))] with r hr
      rw [Measure.restrict_apply measurableSet_closedBall, inter_eq_left.2 hr,
        Ω.isOpenEmbedding'.measurableEmbedding.map_apply]
    have h1 : Tendsto (fun r => ν₁ (closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) :=
      (tendsto_variationMeasure_closedBall_div_volume_closedBall hn hx.1).congr'
        (hball.mono fun _ h => by dsimp only; rw [h])
    have h2 : Tendsto (fun r => ν₂ (closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 1) :=
      (hμ₂ hx).congr fun r => by
        rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
    have hdiv : Tendsto (fun r => ν₁ (closedBall x r) / ν₂ (closedBall x r)) (𝓝[>] 0) (𝓝 1) := by
      have hq := ENNReal.Tendsto.div h1 (.inl one_ne_zero) h2 (.inl ENNReal.one_ne_top)
      rw [div_one] at hq
      refine hq.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
      have hV0 : volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≠ 0 :=
        (measure_closedBall_pos volume 0 hr).ne'
      have hVtop : volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r) ≠ ∞ :=
        measure_closedBall_lt_top.ne
      dsimp only
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
        ENNReal.mul_inv (.inr (ENNReal.inv_ne_top.2 hV0)) (.inr (ENNReal.inv_ne_zero.2 hVtop)),
        inv_inv, mul_comm (ν₂ (closedBall x r))⁻¹, mul_assoc, ← mul_assoc _ (volume _),
        ENNReal.inv_mul_cancel hV0 hVtop, one_mul, ← div_eq_mul_inv]
    exact tendsto_nhds_unique hrn hdiv
  calc ν₁ = ν₂.withDensity (ν₁.rnDeriv ν₂) := (Measure.withDensity_rnDeriv_eq ν₁ ν₂ hac).symm
    _ = ν₂.withDensity 1 := withDensity_congr_ae hrn
    _ = ν₂ := withDensity_one

/-- **De Giorgi's structure theorem (perimeter measure = Hausdorff measure on `∂*s`).** Let `E`
have dimension `n ≥ 2`. The pushforward of the perimeter measure `|Dχ_s|` from `Ω` to `E` equals
`(n - 1)`-dimensional normalized Euclidean Hausdorff measure restricted to the reduced boundary:

`|Dχ_s| = μHE[n - 1]⌊∂*s`. -/
theorem map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary
    (hn : 2 ≤ finrank ℝ E) :
    (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E) =
      μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let K : CompactExhaustion Ω := CompactExhaustion.choice Ω
  let V (n : ℕ) : Set E := ((↑) : Ω → E) '' interior (K n)
  have hVopen (n : ℕ) : IsOpen (V n) := Ω.isOpen.isOpenMap_subtype_val _ isOpen_interior
  have hVcl (n : ℕ) : closure (V n) ⊆ ((↑) : Ω → E) '' K n :=
    closure_minimal (image_mono interior_subset)
      ((K.isCompact n).image continuous_subtype_val).isClosed
  have hVcomp (n : ℕ) : IsCompact (closure (V n)) :=
    ((K.isCompact n).image continuous_subtype_val).of_isClosed_subset isClosed_closure (hVcl n)
  have hVΩ (n : ℕ) : closure (V n) ⊆ Ω := (hVcl n).trans (Subtype.coe_image_subset _ _)
  have hVmono : Monotone V := fun _ _ h => image_mono (interior_mono (K.subset h))
  have hVcov : ⋃ n, V n = Ω := by
    refine Subset.antisymm (iUnion_subset fun n => subset_closure.trans (hVΩ n)) fun x hx => ?_
    obtain ⟨n, hn⟩ := K.exists_mem ⟨x, hx⟩
    exact mem_iUnion.2 ⟨n + 1, ⟨x, hx⟩, K.subset_interior_succ n hn, rfl⟩
  set μ₁ := (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E)
  set μ₂ := μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s)
  have hμ₁Ω : μ₁ Ωᶜ = 0 := by
    rw [Ω.isOpenEmbedding'.measurableEmbedding.map_apply]
    have hpre : ((↑) : Ω → E) ⁻¹' (Ω : Set E)ᶜ = ∅ :=
      eq_empty_of_forall_notMem fun y hy => hy y.2
    simp [hpre]
  have hμ₂Ω : μ₂ Ωᶜ = 0 := by
    rw [Measure.restrict_apply' measurableSet_reducedBoundary]
    have hempty : (Ω : Set E)ᶜ ∩ reducedBoundary volume Ω s = ∅ :=
      eq_empty_of_forall_notMem fun x ⟨hxΩ, hxR⟩ => hxΩ (reducedBoundary_subset hxR)
    simp [hempty]
  ext A hAm
  have hA₁ : μ₁ A = μ₁ (A ∩ Ω) := by
    rw [← measure_inter_add_sdiff A Ω.isOpen.measurableSet,
      measure_mono_null (sdiff_subset_compl A _) hμ₁Ω, add_zero]
  have hA₂ : μ₂ A = μ₂ (A ∩ Ω) := by
    rw [← measure_inter_add_sdiff A Ω.isOpen.measurableSet,
      measure_mono_null (sdiff_subset_compl A _) hμ₂Ω, add_zero]
  have hstep (n : ℕ) : μ₁ (A ∩ V n) = μ₂ (A ∩ V n) := by
    have hloc := restrict_map_variationMeasure_eq_restrict_euclideanHausdorffMeasure
      (Ω := Ω) (s := s) hn (hVopen n) (hVcomp n) (hVΩ n)
    have h1 : μ₁ (A ∩ V n) = μ₁.restrict (V n) A := (Measure.restrict_apply hAm).symm
    have h2 : μ₂ (A ∩ V n) =
        μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s ∩ V n) A := by
      rw [Measure.restrict_apply (hAm.inter (hVopen n).measurableSet),
        Measure.restrict_apply hAm, inter_comm (reducedBoundary volume Ω s) (V n), ← inter_assoc]
    rw [h1, h2, hloc]
  rw [hA₁, hA₂, ← hVcov, inter_iUnion,
    Monotone.measure_iUnion fun _ _ hij => inter_subset_inter_right A (hVmono hij),
    Monotone.measure_iUnion fun _ _ hij => inter_subset_inter_right A (hVmono hij)]
  simp_rw [hstep]

/-- **De Giorgi's structure theorem on arbitrary sets.** In dimension `n ≥ 2`, the perimeter
measure of the preimage of any set `A : Set E` equals the `(n - 1)`-dimensional Euclidean
Hausdorff measure of `A ∩ ∂*s`. No measurability of `A` is required. -/
theorem variationMeasure_preimage_eq_euclideanHausdorffMeasure_inter_reducedBoundary
    (hn : 2 ≤ finrank ℝ E) (A : Set E) :
    variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' A) =
      μHE[finrank ℝ E - 1] (A ∩ reducedBoundary volume Ω s) := by
  rw [← Ω.isOpenEmbedding'.measurableEmbedding.map_apply,
    map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary hn,
    Measure.restrict_apply' measurableSet_reducedBoundary]

/-- **Relative perimeter equals Hausdorff measure of the reduced boundary.** For a set `s` of
locally finite perimeter in `Ω` (in dimension `n ≥ 2`), its perimeter in any open subset `U ≤ Ω`
equals `μHE[n - 1] (U ∩ ∂*s)`. -/
theorem perimeter_eq_euclideanHausdorffMeasure_inter_reducedBoundary (hn : 2 ≤ finrank ℝ E)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞)
    {U : Opens E} (hU : U ≤ Ω) :
    perimeter volume U s = μHE[finrank ℝ E - 1] ((U : Set E) ∩ reducedBoundary volume Ω s) := by
  rw [perimeter_def, ← variationMeasure_preimage_coe hu hfin hU,
    variationMeasure_preimage_eq_euclideanHausdorffMeasure_inter_reducedBoundary hn]

/-- **Perimeter equals Hausdorff measure of the reduced boundary.** For a set `s` of locally finite
perimeter in `Ω` (in dimension `n ≥ 2`), `P(s; Ω) = μHE[n - 1] (∂*s)`. -/
theorem perimeter_eq_euclideanHausdorffMeasure_reducedBoundary (hn : 2 ≤ finrank ℝ E)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞) :
    perimeter volume Ω s = μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s) := by
  rw [perimeter_eq_euclideanHausdorffMeasure_inter_reducedBoundary hn hu hfin le_rfl,
    inter_eq_right.2 reducedBoundary_subset]

/-- In dimension `n ≥ 2`, the reduced boundary has finite `(n - 1)`-dimensional Euclidean Hausdorff
measure inside every compact subset `K ⊆ Ω`. -/
theorem euclideanHausdorffMeasure_inter_reducedBoundary_lt_top_of_isCompact (hn : 2 ≤ finrank ℝ E)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    μHE[finrank ℝ E - 1] (K ∩ reducedBoundary volume Ω s) < ∞ := by
  have := Ω.isOpen.locallyCompactSpace
  rw [← variationMeasure_preimage_eq_euclideanHausdorffMeasure_inter_reducedBoundary hn]
  have hK' : IsCompact (((↑) : Ω → E) ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by rwa [Subtype.range_coe])
  exact hK'.measure_lt_top

end PerimeterMeasure

section IntegralsAndGaussGreen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {s : Set E}

/-- Transport of Lebesgue integrals from the perimeter measure to `μHE[n - 1]` on the reduced
boundary. -/
theorem lintegral_variationMeasure_eq_setLIntegral_reducedBoundary (hn : 2 ≤ finrank ℝ E)
    (f : E → ℝ≥0∞) :
    ∫⁻ y : Ω, f y ∂variationMeasure volume Ω (s.indicator 1) =
      ∫⁻ x in reducedBoundary volume Ω s, f x ∂μHE[finrank ℝ E - 1] := by
  rw [← map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary hn,
    Ω.isOpenEmbedding'.measurableEmbedding.lintegral_map]

/-- Transport of Bochner integrals from the perimeter measure to `μHE[n - 1]` on the reduced
boundary. -/
theorem integral_variationMeasure_eq_setIntegral_reducedBoundary {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hn : 2 ≤ finrank ℝ E) (f : E → F) :
    ∫ y : Ω, f y ∂variationMeasure volume Ω (s.indicator 1) =
      ∫ x in reducedBoundary volume Ω s, f x ∂μHE[finrank ℝ E - 1] := by
  rw [← map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary hn,
    Ω.isOpenEmbedding'.measurableEmbedding.integral_map]

/-- Integrability against `μHE[n - 1]` on the reduced boundary is equivalent to integrability
against the perimeter measure on `Ω`. -/
theorem integrableOn_reducedBoundary_iff {F : Type*} [NormedAddCommGroup F] (hn : 2 ≤ finrank ℝ E)
    {f : E → F} :
    IntegrableOn f (reducedBoundary volume Ω s) μHE[finrank ℝ E - 1] ↔
      Integrable (fun y : Ω => f y) (variationMeasure volume Ω (s.indicator 1)) := by
  rw [IntegrableOn, ← map_variationMeasure_eq_euclideanHausdorffMeasure_restrict_reducedBoundary hn,
    Ω.isOpenEmbedding'.measurableEmbedding.integrable_map_iff]
  rfl

/-- For any continuous compactly supported vector field `φ` with `tsupport φ ⊆ Ω`, the pairing
`x ↦ ⟪φ x, ν_s x⟫` is integrable on the reduced boundary against `μHE[n - 1]`. -/
theorem integrableOn_inner_outerNormal_reducedBoundary (hn : 2 ≤ finrank ℝ E) {φ : E → E}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    IntegrableOn (fun x => ⟪φ x, outerNormal volume Ω s x⟫) (reducedBoundary volume Ω s)
      μHE[finrank ℝ E - 1] := by
  have := Ω.isOpen.locallyCompactSpace
  rw [integrableOn_reducedBoundary_iff hn]
  set lam := variationMeasure volume Ω (s.indicator 1)
  set K : Set Ω := ((↑) : Ω → E) ⁻¹' tsupport φ
  have hK : IsCompact K := Topology.IsInducing.subtypeVal.isCompact_preimage' hc
    (by rwa [Subtype.range_coe])
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hc
  have hion : IntegrableOn (fun y : Ω => ⟪φ y, outerNormal volume Ω s y⟫) K lam := by
    refine Measure.integrableOn_of_bounded hK.measure_lt_top.ne ?_ (M := max M 0) ?_
    · have hmeas : AEStronglyMeasurable (fun y : Ω => outerNormal volume Ω s y) lam :=
        (measurable_polarDensity.neg.aestronglyMeasurable).congr
          (ae_outerNormal_eq.mono fun _ h => h.symm)
      exact (hφ.comp continuous_subtype_val).aestronglyMeasurable.inner hmeas
    · filter_upwards [ae_restrict_of_ae ae_mem_reducedBoundary] with y hy
      calc ‖⟪φ y, outerNormal volume Ω s y⟫‖
          ≤ ‖φ y‖ * ‖outerNormal volume Ω s y‖ := norm_inner_le_norm _ _
        _ ≤ max M 0 * 1 := by
            gcongr
            · exact (hM y).trans (le_max_left M 0)
            · exact (norm_outerNormal hy).le
        _ = max M 0 := mul_one _
  rw [← integrable_indicator_iff hK.isClosed.measurableSet] at hion
  refine hion.congr (.of_forall fun y => ?_)
  by_cases hy : y ∈ K
  · simp [indicator_of_mem hy]
  · have h0 : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [indicator_of_notMem hy, h0]

/-- **De Giorgi's Gauss–Green theorem, `Dχ_s = -ν_s μHE[n - 1]⌊∂*s`.** Let `E` have dimension
`n ≥ 2` and let `s` have locally finite perimeter in `Ω`. For every `C¹` vector field `φ : E → E`
with compact support in `Ω`,

`∫_s tr (Dφ) = ∫_{∂*s} ⟪φ, ν_s⟫ dμHE[n - 1]`. -/
theorem integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal (hn : 2 ≤ finrank ℝ E)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * s.indicator 1 x =
      ∫ x in reducedBoundary volume Ω s, ⟪φ x, outerNormal volume Ω s x⟫ ∂μHE[finrank ℝ E - 1] := by
  rw [integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal hu hfin hφ hc hs,
    integral_variationMeasure_eq_setIntegral_reducedBoundary hn
      (fun x => ⟪φ x, outerNormal volume Ω s x⟫)]

/-- **De Giorgi's Gauss–Green theorem for test vector fields.** Let `E` have dimension `n ≥ 2` and
let `s` have locally finite perimeter in `Ω`. For every test vector field `φ : 𝓓(Ω, E)`,

`∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dμHE[n - 1]`. -/
theorem integral_divergenceCLM_mul_indicator_eq_setIntegral_inner_outerNormal
    (hn : 2 ≤ finrank ℝ E)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞)
    (φ : 𝓓(Ω, E)) :
    ∫ x, divergenceCLM φ x * s.indicator 1 x =
      ∫ x in reducedBoundary volume Ω s, ⟪φ x, outerNormal volume Ω s x⟫ ∂μHE[finrank ℝ E - 1] := by
  rw [integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hu hfin φ, ← integral_neg,
    ← integral_variationMeasure_eq_setIntegral_reducedBoundary hn
      (fun x => ⟪φ x, outerNormal volume Ω s x⟫)]
  refine integral_congr_ae ?_
  filter_upwards [ae_outerNormal_eq] with y hy
  rw [hy, inner_neg_right]

end IntegralsAndGaussGreen

end TauCeti
