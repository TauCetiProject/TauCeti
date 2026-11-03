/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
import TauCeti.Analysis.BoundedVariation.Convex
import TauCeti.Analysis.BoundedVariation.RegularLevel
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Integral.LayerCake

/-!
# Smooth approximation of sets of finite volume in perimeter

A Lebesgue-measurable set of finite volume admits bounded open approximations with smooth
boundary, converging both in symmetric-difference measure and in perimeter on the whole space.
The set need not be bounded, and finite perimeter is not assumed: the perimeter convergence is
extended-valued, so the construction also covers infinite perimeter. Finite volume cannot be
replaced by finite perimeter here, since the complement of a ball has finite perimeter but no
bounded set approximates it in measure.
The approximations are positive regular superlevels of compactly supported smooth functions.
Thus their smoothness is witnessed by defining functions, rather than assumed as a predicate.

The first step is a truncation: cutting a set of finite measure by the closed half-spaces
bounding a large cube does not increase its perimeter
(`TauCeti.perimeter_inter_biInter_halfSpace_le`), so the set is the limit of bounded subsets whose
perimeters converge to its own
(`MeasureTheory.NullMeasurableSet.exists_isBounded_perimeter_approximation`).
A bounded set is then approximated as follows. Mollify the indicator, choose regular levels in
intervals expanding to `(0, 1)`, and use
`ContDiff.exists_mem_Ioo_isCompact_closure_perimeter_le` for perimeter control. The quantitative
threshold estimate `Measure.measure_symmDiff_setOf_lt_indicator_le` controls the volume error
uniformly in each interval. Lower semicontinuity then supplies the reverse perimeter bound.
Null modifications of the original set require no choice of a Borel representative.

## Main results

* `MeasureTheory.NullMeasurableSet.exists_smooth_perimeter_approximation`: approximation of a set
  of finite measure by bounded open sets with smooth boundary, in measure and in perimeter.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.2.2.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 13.
-/

public section

noncomputable section

open MeasureTheory Filter Metric Set TopologicalSpace ContinuousLinearMap
open scoped ENNReal Convolution Topology symmDiff ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {s : Set E}

private theorem exists_regular_superlevel_approximation_of_isBounded (hs : NullMeasurableSet s μ)
    (hb : Bornology.IsBounded s) {δ ε : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) (hε : 0 < ε) :
    ∃ (u : E → ℝ) (t : ℝ), ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ t ∈ Ioo δ (1 - δ) ∧
      (∀ x, u x = t → Function.Surjective (fderiv ℝ u x)) ∧
      IsCompact (closure {x | t < u x}) ∧ frontier {x | t < u x} = {x | u x = t} ∧
      perimeter μ ⊤ {x | t < u x} < ⊤ ∧
      μ ({x | t < u x} ∆ s) ≤ ENNReal.ofReal ε ∧
      perimeter μ ⊤ {x | t < u x} ≤ perimeter μ ⊤ s / ENNReal.ofReal (1 - 2 * δ) := by
  let χ := s.indicator (1 : E → ℝ)
  have hχc : HasCompactSupport χ :=
    HasCompactSupport.of_support_subset_isCompact hb.isCompact_closure
      (support_indicator_subset.trans subset_closure)
  have hχ : Integrable χ μ := by
    exact (integrable_indicator_iff₀ hs).mpr
      (integrableOn_const hb.measure_lt_top.ne)
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / (n + 2), 1 / (n + 1), by positivity, by gcongr; norm_num⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv := tendsto_eLpNorm_normed_convolution_sub ENNReal.one_ne_top hφ
    (memLp_one_iff_integrable.mpr hχ)
  have herr : (0 : ℝ≥0∞) < ENNReal.ofReal ε * ENNReal.ofReal δ := by positivity
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds herr)).exists
  let u := (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] χ
  have hu : ContDiff ℝ ∞ u :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      hχ.locallyIntegrable
  have huc : HasCompactSupport u := (φ n).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hχc
  have hlevels : δ < 1 - δ := by linarith
  obtain ⟨t, ht, hreg, hc, hfront, hP⟩ :=
    hu.exists_mem_Ioo_isCompact_closure_perimeter_le (μ := μ) (Ω := ⊤) huc hδ.le hlevels
  have hfinite : totalVariationOn μ ⊤ u < ⊤ := by
    obtain ⟨K, hK⟩ := hu.lipschitzWith_of_hasCompactSupport huc (by simp)
    exact huc.totalVariationOn_lt_top hK
  refine ⟨u, t, hu, huc, ht, hreg, hc, hfront, ?_, ?_, ?_⟩
  · exact hP.trans_lt (ENNReal.div_lt_top hfinite.ne
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))))
  · refine (μ.measure_symmDiff_setOf_lt_indicator_le hu.continuous.aestronglyMeasurable hs
      hδ ht.1.le ht.2.le).trans ?_
    apply (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))
      ENNReal.ofReal_ne_top).mpr
    simpa only [χ, Pi.sub_apply] using
      (lintegral_enorm_le_eLpNorm_one (f := u - χ)).trans hn.le
  · have hvar : totalVariationOn μ ⊤ u ≤ perimeter μ ⊤ s := by
      rw [perimeter_def]
      exact (φ n).totalVariationOn_normed_convolution_le
        (hχ.locallyIntegrable.locallyIntegrableOn _) (fun _ _ => subset_univ _)
    refine hP.trans ?_
    have hwidth : 1 - δ - δ = 1 - 2 * δ := by ring
    rw [hwidth]
    gcongr

private theorem exists_regular_superlevel_approximation (hs : NullMeasurableSet s μ)
    (hμs : μ s ≠ ⊤) {δ ε : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) (hε : 0 < ε) :
    ∃ (u : E → ℝ) (t : ℝ), ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ t ∈ Ioo δ (1 - δ) ∧
      (∀ x, u x = t → Function.Surjective (fderiv ℝ u x)) ∧
      IsCompact (closure {x | t < u x}) ∧ frontier {x | t < u x} = {x | u x = t} ∧
      perimeter μ ⊤ {x | t < u x} < ⊤ ∧
      μ ({x | t < u x} ∆ s) ≤ ENNReal.ofReal ε ∧
      perimeter μ ⊤ {x | t < u x} ≤ perimeter μ ⊤ s / ENNReal.ofReal (1 - 2 * δ) := by
  -- Cut `s` to a bounded subset `r` with `μ (s \ r) < ε / 2` and `P(r) ≤ P(s)`, then approximate
  -- `r` to within `ε / 2`.
  obtain ⟨r, -, hr, hrlim, -⟩ := hs.exists_isBounded_perimeter_approximation hμs
  obtain ⟨m, hm⟩ :=
    (hrlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hε)))).exists
  obtain ⟨hrs, hrm, hrb, hrP⟩ := hr m
  obtain ⟨u, t, hu, huc, ht, hreg, hc, hfront, hfin, hvol, hP⟩ :=
    exists_regular_superlevel_approximation_of_isBounded hrm hrb hδ hδ' (half_pos hε)
  refine ⟨u, t, hu, huc, ht, hreg, hc, hfront, hfin, ?_, hP.trans (by gcongr)⟩
  calc μ ({x | t < u x} ∆ s) ≤ μ ({x | t < u x} ∆ r m) + μ (r m ∆ s) :=
        measure_symmDiff_le _ _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        add_le_add hvol (by rw [symmDiff_of_le hrs]; exact hm.le)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]

/-- **Smooth approximation of sets of finite volume.** Every null-measurable set of finite
measure is approximated in volume and perimeter by bounded open sets with smooth boundary. The
sets are positive regular superlevels of compactly supported smooth functions and have finite
perimeter; their frontiers are the corresponding regular levels. Perimeters are extended-valued,
including when the original set has infinite perimeter, and the set itself need not be bounded. -/
theorem _root_.MeasureTheory.NullMeasurableSet.exists_smooth_perimeter_approximation
    (hs : NullMeasurableSet s μ) (hμs : μ s ≠ ⊤) :
    ∃ (u : ℕ → E → ℝ) (t : ℕ → ℝ),
      (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n) ∧ t n ∈ Ioo 0 1 ∧
        (∀ x, u n x = t n → Function.Surjective (fderiv ℝ (u n) x)) ∧
        IsCompact (closure {x | t n < u n x}) ∧
        frontier {x | t n < u n x} = {x | u n x = t n} ∧
        perimeter μ ⊤ {x | t n < u n x} < ⊤) ∧
      Tendsto (fun n => μ ({x | t n < u n x} ∆ s)) atTop (𝓝 0) ∧
      Tendsto (fun n => perimeter μ ⊤ {x | t n < u n x}) atTop (𝓝 (perimeter μ ⊤ s)) := by
  let δ : ℕ → ℝ := fun n => 1 / (n + 3)
  let ε : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδ (n : ℕ) : 0 < δ n := by positivity
  have hδ' (n : ℕ) : δ n < 1 / 2 := by
    dsimp [δ]
    apply one_div_lt_one_div_of_lt (by norm_num)
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hε (n : ℕ) : 0 < ε n := by positivity
  choose u t hu huc ht hreg hc hfront hfinite hvol hP using
    fun n => exists_regular_superlevel_approximation hs hμs (hδ n) (hδ' n) (hε n)
  have hvolconv : Tendsto (fun n => μ ({x | t n < u n x} ∆ s)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa [ε] using (ENNReal.tendsto_ofReal
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
      (fun _ => zero_le) hvol
  refine ⟨u, t, fun n => ⟨hu n, huc n, ⟨(hδ n).trans (ht n).1,
    (ht n).2.trans (by linarith [hδ n])⟩, hreg n, hc n, hfront n, hfinite n⟩, hvolconv, ?_⟩
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · refine perimeter_le_liminf
      (.of_forall fun n =>
        (isOpen_lt continuous_const (hu n).continuous).measurableSet.nullMeasurableSet)
      hs fun K _ _ => ?_
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvolconv
      (fun _ => zero_le) (fun n => measure_mono inter_subset_left)
  · have hδconv : Tendsto δ atTop (𝓝 0) := by
      simpa [δ, Function.comp_def, Nat.cast_add] using
        ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 3))
    have hdenom : Tendsto (fun n => ENNReal.ofReal (1 - 2 * δ n)) atTop (𝓝 1) := by
      simpa using ENNReal.tendsto_ofReal
        ((tendsto_const_nhds (x := (1 : ℝ))).sub (hδconv.const_mul 2))
    have hbound := ENNReal.Tendsto.const_div (a := perimeter μ ⊤ s) hdenom
      (Or.inl ENNReal.one_ne_top)
    rw [div_one] at hbound
    exact (limsup_le_limsup (.of_forall hP)).trans_eq hbound.limsup_eq

end TauCeti
