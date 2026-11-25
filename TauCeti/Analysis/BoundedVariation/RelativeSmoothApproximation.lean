/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Approximation
public import TauCeti.Analysis.BoundedVariation.RegularLevel
import Mathlib.MeasureTheory.Integral.Average
import TauCeti.Analysis.Calculus.Sard.OutermostStratum
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.LayerCake

/-!
# Relative smooth approximation of sets in perimeter

Let `Ω` be an open subset of a finite-dimensional real inner product space with an additive Haar
measure `μ`, and let `s` be null-measurable. This file proves that there are functions `u_j`
smooth on `Ω` and levels `t_j ∈ (0, 1)`, regular for `u_j` on `Ω`, such that `{u_j > t_j}`
converges to `s` in measure on `Ω` and `P({u_j > t_j}; Ω) → P(s; Ω)`, finite or infinite
(`TauCeti.exists_contDiffOn_perimeter_approximation`). Neither `s` nor `Ω` is assumed to have
finite volume, and `s` need not have finite perimeter in `Ω`.

The route applies the strict approximation on open sets
(`MeasureTheory.LocallyIntegrableOn.exists_contDiffOn_strict_approximation`) to the indicator of
`s`. For a function smooth on `Ω`, the coarea formula
`TauCeti.totalVariationOn_eq_lintegral_perimeter` and the Morse–Sard theorem on `Ω`
(`TauCeti.addHaar_image_criticalPoints_eq_zero`) give, in every interval `(a, b)`, a level regular
on `Ω` whose superlevel set has perimeter in `Ω` at most the variation on `Ω` divided by `b - a`
(`ContDiffOn.exists_mem_Ioo_surjective_fderiv_perimeter_le`, the `Ω`-local form of
`ContDiff.exists_mem_Ioo_surjective_fderiv_perimeter_le`). Thresholding at a level in
`(δ, 1 - δ)` controls the volume error by the `L¹(Ω)` error divided by `δ`
(`MeasureTheory.Measure.measure_symmDiff_setOf_lt_indicator_le`), and lower semicontinuity of the
perimeter gives the reverse inequality. The whole-space form for sets of finite volume is
`MeasureTheory.NullMeasurableSet.exists_smooth_perimeter_approximation`.

## Main results

* `ContDiffOn.exists_mem_Ioo_surjective_fderiv_perimeter_le`: a regular level on `Ω` with the
  perimeter bound, for a function smooth on `Ω`.
* `TauCeti.exists_contDiffOn_perimeter_approximation`: relative smooth approximation of a set in
  measure and in perimeter on `Ω`.
-/

public section

open Function MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal Topology ContDiff symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {u : E → ℝ} {Ω : Opens E} {a b : ℝ} {s : Set E}

/-- A function smooth on an open set `Ω` has a level in every nonempty interval `(a, b)` that is
regular on `Ω` and whose superlevel set has perimeter in `Ω` at most the variation of the function
on `Ω` divided by `b - a`. The estimate also holds when the variation is infinite. -/
theorem ContDiffOn.exists_mem_Ioo_surjective_fderiv_perimeter_le (hu : ContDiffOn ℝ ∞ u Ω)
    (hab : a < b) :
    ∃ t ∈ Ioo a b, (∀ x ∈ Ω, u x = t → Surjective (fderiv ℝ u x)) ∧
      TauCeti.perimeter μ Ω {x | t < u x} ≤
        TauCeti.totalVariationOn μ Ω u / ENNReal.ofReal (b - a) := by
  let ν : Measure ℝ := volume.restrict (Ioo a b)
  let N : Set ℝ := (Ioo a b)ᶜ ∪ u '' ((Ω : Set E) ∩ {x | ¬ Surjective (fderiv ℝ u x)})
  have hν : ν ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (sub_pos.mpr hab)
  have hN : ν N = 0 := by
    refine measure_union_null ?_ ?_
    · simp [ν]
    · exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq
        (TauCeti.addHaar_image_criticalPoints_eq_zero volume
          (fun x hx ↦ (hu x hx).contDiffAt (Ω.isOpen.mem_nhds hx))
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl _))) bot_le
  have hmeas : Measurable (fun t ↦ TauCeti.perimeter μ Ω {x | t < u x}) :=
    TauCeti.measurable_perimeter_setOf_lt (hu.continuousOn.aemeasurable Ω.isOpen.measurableSet)
  obtain ⟨t, htN, ht⟩ := exists_notMem_null_le_laverage hν hmeas.aemeasurable hN
  have htI : t ∈ Ioo a b := by simpa [N] using (not_or.mp htN).1
  refine ⟨t, htI, fun x hx hxt ↦ ?_, ht.trans ?_⟩
  · by_contra hcrit
    exact (not_or.mp htN).2 ⟨x, ⟨hx, hcrit⟩, hxt⟩
  · rw [laverage_eq, Measure.restrict_apply_univ, Real.volume_Ioo]
    gcongr
    exact (setLIntegral_le_lintegral (Ioo a b) _).trans_eq
      (TauCeti.totalVariationOn_eq_lintegral_perimeter
        (hu.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)).symm

namespace TauCeti

/-- **Relative smooth approximation in perimeter.** For a null-measurable set `s` and an open set
`Ω`, there are functions `u n` smooth on `Ω` and levels `t n ∈ (0, 1)`, regular for `u n` on `Ω`,
such that the superlevel sets `{u n > t n}` converge to `s` in measure on `Ω` and their perimeters
in `Ω` converge to `P(s; Ω)`, finite or infinite. Neither `s` nor `Ω` needs finite volume. -/
theorem exists_contDiffOn_perimeter_approximation (hs : NullMeasurableSet s μ) (Ω : Opens E) :
    ∃ (u : ℕ → E → ℝ) (t : ℕ → ℝ),
      (∀ n, ContDiffOn ℝ ∞ (u n) Ω ∧ t n ∈ Ioo 0 1 ∧
        ∀ x ∈ Ω, u n x = t n → Surjective (fderiv ℝ (u n) x)) ∧
      Tendsto (fun n ↦ μ (({x | t n < u n x} ∆ s) ∩ Ω)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ perimeter μ Ω {x | t n < u n x}) atTop (𝓝 (perimeter μ Ω s)) := by
  have hsΩ : NullMeasurableSet s (μ.restrict Ω) := hs.mono Measure.restrict_le_self
  have hχ : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ :=
    locallyIntegrableOn_indicator_const hsΩ 1
  obtain ⟨w, hw, hL, hV⟩ := hχ.exists_contDiffOn_strict_approximation
  let δ : ℕ → ℝ := fun k ↦ 1 / (k + 3)
  let ε : ℕ → ℝ := fun k ↦ 1 / (k + 1)
  have hδ (k : ℕ) : 0 < δ k := by positivity
  have hε (k : ℕ) : 0 < ε k := by positivity
  have hδ' (k : ℕ) : δ k < 1 - δ k := by
    have : δ k ≤ 1 / 3 := by
      dsimp [δ]
      gcongr
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith
  -- Choose an approximant whose `L¹(Ω)` error is below `ε k * δ k`, along a sequence of indices
  -- tending to infinity.
  have hidx (k : ℕ) : ∃ m, k ≤ m ∧
      ∫⁻ x in Ω, ‖w m x - s.indicator 1 x‖ₑ ∂μ < ENNReal.ofReal (ε k * δ k) :=
    ((eventually_ge_atTop k).and
      (hL.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (mul_pos (hε k) (hδ k)))))).exists
  choose m hkm hm using hidx
  have hmT : Tendsto m atTop atTop := tendsto_atTop_mono hkm tendsto_id
  choose t ht hreg hP using fun k ↦
    (hw (m k)).exists_mem_Ioo_surjective_fderiv_perimeter_le (μ := μ) (hδ' k)
  have hvol (k : ℕ) :
      μ (({x | t k < w (m k) x} ∆ s) ∩ Ω) ≤ ENNReal.ofReal (ε k) := by
    rw [← Measure.restrict_apply' Ω.isOpen.measurableSet]
    refine ((μ.restrict Ω).measure_symmDiff_setOf_lt_indicator_le
      ((hw (m k)).continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet) hsΩ (hδ k)
      (ht k).1.le (ht k).2.le).trans ?_
    rw [ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.2 (hδ k))) ENNReal.ofReal_ne_top,
      ← ENNReal.ofReal_mul (hε k).le]
    exact (hm k).le
  have hvolconv : Tendsto (fun k ↦ μ (({x | t k < w (m k) x} ∆ s) ∩ Ω)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa [ε] using (ENNReal.tendsto_ofReal
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
      (fun _ ↦ zero_le) hvol
  refine ⟨fun k ↦ w (m k), t, fun k ↦ ⟨hw (m k), ⟨(hδ k).trans (ht k).1,
    (ht k).2.trans (by linarith [hδ k])⟩, hreg k⟩, hvolconv, ?_⟩
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · -- Lower semicontinuity, applied to the open sets `Ω ∩ {w (m k) > t k}`.
    have hcongr (k : ℕ) : perimeter μ Ω {x | t k < w (m k) x} =
        perimeter μ Ω ((Ω : Set E) ∩ {x | t k < w (m k) x}) :=
      perimeter_congr_of_inter_eq (by rw [inter_comm (Ω : Set E), inter_assoc, inter_self])
    simp_rw [hcongr]
    refine perimeter_le_liminf (.of_forall fun k ↦ ?_) hs fun K _ hKΩ ↦ ?_
    · exact ((hw (m k)).continuousOn.isOpen_inter_preimage Ω.isOpen
        isOpen_Ioi).measurableSet.nullMeasurableSet
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvolconv
        (fun _ ↦ zero_le) fun k ↦ measure_mono ?_
      rintro x ⟨hx, hxK⟩
      have hxΩ : x ∈ (Ω : Set E) := hKΩ hxK
      refine ⟨?_, hxΩ⟩
      simpa [mem_symmDiff, hxΩ] using hx
  · have hδconv : Tendsto δ atTop (𝓝 0) := by
      simpa [δ, Function.comp_def, Nat.cast_add] using
        ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 3))
    have hdenom : Tendsto (fun k ↦ ENNReal.ofReal (1 - δ k - δ k)) atTop (𝓝 1) := by
      simpa using ENNReal.tendsto_ofReal
        (((tendsto_const_nhds (x := (1 : ℝ))).sub hδconv).sub hδconv)
    have hVm : Tendsto (fun k ↦ totalVariationOn μ Ω (w (m k))) atTop (𝓝 (perimeter μ Ω s)) := by
      rw [perimeter_def]
      exact hV.comp hmT
    have hbound := ENNReal.Tendsto.div hVm (Or.inr one_ne_zero) hdenom (Or.inl ENNReal.one_ne_top)
    rw [div_one] at hbound
    exact (limsup_le_limsup (.of_forall hP)).trans_eq hbound.limsup_eq

end TauCeti
