/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Approximation
public import TauCeti.Analysis.BoundedVariation.RegularLevel
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.LayerCake
import TauCeti.Topology.Instances.ENNReal

/-!
# Relative smooth approximation of sets in perimeter

Let `Ω` be an open subset of a finite-dimensional real inner product space with an additive Haar
measure `μ`, and let `s` be null-measurable. This file proves that there are functions `u_j`
smooth on `Ω` and levels `t_j ∈ (0, 1)`, regular for `u_j` on `Ω`, such that `{u_j > t_j}`
converges to `s` in measure on `Ω` and `P({u_j > t_j}; Ω) → P(s; Ω)`, finite or infinite
(`MeasureTheory.NullMeasurableSet.exists_contDiffOn_perimeter_approximation`). Neither `s` nor
`Ω` is assumed to have finite volume, and `s` need not have finite perimeter in `Ω`.

The route applies the strict approximation on open sets
(`MeasureTheory.LocallyIntegrableOn.exists_contDiffOn_strict_approximation`) to the indicator of
`s`. For a function smooth on `Ω`, the coarea formula
`TauCeti.totalVariationOn_eq_lintegral_perimeter` and the Morse–Sard theorem on `Ω`
(`TauCeti.addHaar_image_criticalPoints_eq_zero`) give, in every interval `(a, b)`, a level regular
on `Ω` whose superlevel set has perimeter in `Ω` at most the variation on `Ω` divided by `b - a`
(`ContDiffOn.exists_mem_Ioo_surjective_fderiv_perimeter_le`). Thresholding at a level in
`(δ, 1 - δ)` controls the volume error by the `L¹(Ω)` error divided by `δ`
(`MeasureTheory.Measure.measure_symmDiff_setOf_lt_indicator_le`), and lower semicontinuity of the
perimeter gives the reverse inequality. The whole-space form for sets of finite volume is
`MeasureTheory.NullMeasurableSet.exists_smooth_perimeter_approximation`.

## Main results

* `MeasureTheory.NullMeasurableSet.exists_contDiffOn_perimeter_approximation`: relative smooth
  approximation of a set in measure and in perimeter on `Ω`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 13 (§13.2).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.2.2.
-/

public section

open Function MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal Topology ContDiff symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {u : E → ℝ} {Ω : Opens E} {a b : ℝ} {s : Set E}

namespace TauCeti

/-- Lower semicontinuity for superlevel sets of functions continuous on `Ω`: if they converge to
`s` in measure on `Ω`, then `P(s; Ω)` is at most the lower limit of their perimeters in `Ω`. -/
private theorem perimeter_le_liminf_setOf_lt {w : ℕ → E → ℝ} {t : ℕ → ℝ}
    (hw : ∀ k, ContinuousOn (w k) Ω) (hs : NullMeasurableSet s μ)
    (hvol : Tendsto (fun k ↦ μ (({x | t k < w k x} ∆ s) ∩ Ω)) atTop (𝓝 0)) :
    perimeter μ Ω s ≤ liminf (fun k ↦ perimeter μ Ω {x | t k < w k x}) atTop := by
  -- Apply lower semicontinuity to the open sets `Ω ∩ {w k > t k}`.
  have hcongr (k : ℕ) : perimeter μ Ω {x | t k < w k x} =
      perimeter μ Ω ((Ω : Set E) ∩ {x | t k < w k x}) :=
    perimeter_congr_of_inter_eq (by rw [inter_comm (Ω : Set E), inter_assoc, inter_self])
  simp_rw [hcongr]
  refine perimeter_le_liminf (.of_forall fun k ↦ ?_) hs fun K _ hKΩ ↦ ?_
  · exact ((hw k).isOpen_inter_preimage Ω.isOpen isOpen_Ioi).measurableSet.nullMeasurableSet
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvol
      (fun _ ↦ zero_le) fun k ↦ measure_mono ?_
    rintro x ⟨hx, hxK⟩
    have hxΩ : x ∈ (Ω : Set E) := hKΩ hxK
    refine ⟨?_, hxΩ⟩
    simpa [mem_symmDiff, hxΩ] using hx

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- Thresholding a function continuous on `Ω` at a level in `[δ, 1 - δ]` approximates `s` in
measure on `Ω` within its `L¹(Ω)` distance from the indicator divided by `δ`. -/
private theorem measure_symmDiff_inter_le {w : E → ℝ} (hw : ContinuousOn w Ω)
    (hs : NullMeasurableSet s μ) {δ ε t : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (ht : t ∈ Ioo δ (1 - δ))
    (hL : ∫⁻ x in Ω, ‖w x - s.indicator 1 x‖ₑ ∂μ < ENNReal.ofReal (ε * δ)) :
    μ (({x | t < w x} ∆ s) ∩ Ω) ≤ ENNReal.ofReal ε := by
  rw [← Measure.restrict_apply' Ω.isOpen.measurableSet]
  refine ((μ.restrict Ω).measure_symmDiff_setOf_lt_indicator_le
    (hw.aestronglyMeasurable Ω.isOpen.measurableSet) (hs.mono Measure.restrict_le_self) hδ
    ht.1.le ht.2.le).trans ?_
  rw [ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.2 hδ)) ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_mul hε.le]
  exact hL.le

/-- **Relative smooth approximation in perimeter.** For a null-measurable set `s` and an open set
`Ω`, there are functions `u n` smooth on `Ω` and levels `t n ∈ (0, 1)`, regular for `u n` on `Ω`,
such that the superlevel sets `{u n > t n}` converge to `s` in measure on `Ω` and their perimeters
in `Ω` converge to `P(s; Ω)`, finite or infinite. Neither `s` nor `Ω` needs finite volume. -/
theorem _root_.MeasureTheory.NullMeasurableSet.exists_contDiffOn_perimeter_approximation
    (hs : NullMeasurableSet s μ) (Ω : Opens E) :
    ∃ (u : ℕ → E → ℝ) (t : ℕ → ℝ),
      (∀ n, ContDiffOn ℝ ∞ (u n) Ω ∧ t n ∈ Ioo 0 1 ∧
        ∀ x ∈ Ω, u n x = t n → Surjective (fderiv ℝ (u n) x)) ∧
      Tendsto (fun n ↦ μ (({x | t n < u n x} ∆ s) ∩ Ω)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ perimeter μ Ω {x | t n < u n x}) atTop (𝓝 (perimeter μ Ω s)) := by
  have hsΩ : NullMeasurableSet s (μ.restrict Ω) := hs.mono Measure.restrict_le_self
  have hχ : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ :=
    locallyIntegrableOn_indicator_const hsΩ 1
  obtain ⟨w, hw, hL, hV⟩ := hχ.exists_contDiffOn_strict_approximation
  obtain ⟨δ, -, hδ, hδconv⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨ε, -, hε, hεconv⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have hδ' (k : ℕ) : δ k < 1 - δ k := by linarith [(hδ k).2]
  -- Choose an approximant whose `L¹(Ω)` error is below `ε k * δ k`, along a sequence of indices
  -- tending to infinity.
  have hidx (k : ℕ) : ∃ m, k ≤ m ∧
      ∫⁻ x in Ω, ‖w m x - s.indicator 1 x‖ₑ ∂μ < ENNReal.ofReal (ε k * δ k) :=
    ((eventually_ge_atTop k).and
      (hL.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (mul_pos (hε k) (hδ k).1))))).exists
  choose m hkm hm using hidx
  have hmT : Tendsto m atTop atTop := tendsto_atTop_mono hkm tendsto_id
  choose t ht hreg hP using fun k ↦
    (hw (m k)).exists_mem_Ioo_surjective_fderiv_perimeter_le (μ := μ) Ω.isOpen subset_rfl (hδ' k)
  have hvol (k : ℕ) : μ (({x | t k < w (m k) x} ∆ s) ∩ Ω) ≤ ENNReal.ofReal (ε k) :=
    measure_symmDiff_inter_le (hw (m k)).continuousOn hs (hδ k).1 (hε k) (ht k) (hm k)
  have hvolconv : Tendsto (fun k ↦ μ (({x | t k < w (m k) x} ∆ s) ∩ Ω)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using ENNReal.tendsto_ofReal hεconv) (fun _ ↦ zero_le) hvol
  refine ⟨fun k ↦ w (m k), t, fun k ↦ ⟨hw (m k), ⟨(hδ k).1.trans (ht k).1,
    (ht k).2.trans (by linarith [(hδ k).1])⟩, hreg k⟩, hvolconv, ?_⟩
  refine ENNReal.tendsto_of_le_liminf_of_le_div ?_ ?_
    (perimeter_le_liminf_setOf_lt (fun k ↦ (hw (m k)).continuousOn) hs hvolconv) (.of_forall hP)
  · rw [perimeter_def]
    exact hV.comp hmT
  · simpa using ENNReal.tendsto_ofReal (((tendsto_const_nhds (x := (1 : ℝ))).sub hδconv).sub hδconv)

end TauCeti
