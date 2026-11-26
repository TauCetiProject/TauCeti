/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import TauCeti.Analysis.Calculus.ContDiff.Periodization
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Density of test sections in `L²` of the cylinder

The `L²` classes of the test sections of the cylinder, the `C²` sections of `ℝ × S¹` that vanish
for `|s|` large (`TauCeti.CylinderSobolev.testSection`), form a subspace
`TauCeti.CylinderSobolev.testSectionLp` of `L²(ℝ × [0, 1], W)`, and this subspace is dense
(`TauCeti.CylinderSobolev.dense_testSectionLp`).

An `L²` section is first approximated by a continuous compactly supported map on the plane, cut off
to the open strip `ℝ × (0, 1)`. Its mollification by a smooth bump of radius at most `1` is smooth
and supported in `ℝ × (-1, 2)`, and the periodization `Σₖ h(s, t + k)` of such a map `h`
(`TauCeti.periodizeSnd`) is a test section. On the strip it differs from `h` only by the two
translates `h(s, t ± 1)`, and these are as small in `L²` as the mollification error, since the
cut-off map vanishes there.
-/

public section

noncomputable section

open Filter MeasureTheory Set Function
open scoped ENNReal Topology Convolution

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

variable (W) in
/-- The `L²` classes of the test sections of the cylinder, as a subspace of
`L²(ℝ × [0, 1], W)`: the classes of the `C²` maps of period one in `t` that vanish for `|s|`
large. -/
def testSectionLp : Submodule ℝ (Lp W 2 stripMeasure) where
  carrier := {η | ∃ ξ ∈ testSection W, η =ᵐ[stripMeasure] ξ}
  zero_mem' := ⟨0, (testSection W).zero_mem, Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro η η' ⟨ξ, hξ, h⟩ ⟨ξ', hξ', h'⟩
    exact ⟨ξ + ξ', add_mem hξ hξ', (Lp.coeFn_add η η').trans (h.add h')⟩
  smul_mem' := by
    rintro c η ⟨ξ, hξ, h⟩
    exact ⟨c • ξ, Submodule.smul_mem _ c hξ, (Lp.coeFn_smul c η).trans (h.const_smul c)⟩

/-- Membership in the `L²` classes of test sections. -/
theorem mem_testSectionLp_iff {η : Lp W 2 stripMeasure} :
    η ∈ testSectionLp W ↔ ∃ ξ ∈ testSection W, η =ᵐ[stripMeasure] ξ :=
  Iff.rfl

/-- The `L²` class of a test section lies in `testSectionLp`. -/
theorem toLp_mem_testSectionLp {ξ : ℝ × ℝ → W} (hξ : ξ ∈ testSection W)
    (hm : MemLp ξ 2 stripMeasure) : hm.toLp ξ ∈ testSectionLp W :=
  ⟨ξ, hξ, hm.coeFn_toLp⟩

omit [NormedSpace ℝ W] in
/-- On the strip, the periodization of a map `h` supported in `ℝ × (-1, 2)` differs from a map `g`
supported in `ℝ × (0, 1)` by at most three times the `L²` distance from `h` to `g` on the plane:
the difference is `-(e(s, t + 1) + e(s, t) + e(s, t - 1))` for `e = h - g`, since `g` vanishes at
`(s, t ± 1)` for `t ∈ [0, 1]`. -/
private theorem eLpNorm_sub_periodizeSnd_le {g h : ℝ × ℝ → W}
    (hg : ∀ z, g z ≠ 0 → z.2 ∈ Ioo (0 : ℝ) 1) (hh : ∀ z, h z ≠ 0 → z.2 ∈ Ioo (-1 : ℝ) 2)
    (he : AEStronglyMeasurable (h - g) volume) :
    eLpNorm (g - periodizeSnd h) 2 stripMeasure ≤ 3 * eLpNorm (h - g) 2 volume := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set e := h - g
  have heq : g - periodizeSnd h =ᵐ[stripMeasure]
      -(e ∘ (· + (0, 1)) + e + e ∘ (· + (0, -1))) := by
    filter_upwards [ae_restrict_mem ((MeasurableSet.univ (α := ℝ)).prod measurableSet_Icc)]
      with z hz
    obtain ⟨s, t⟩ := z
    have ht : t ∈ Icc (0 : ℝ) 1 := hz.2
    have hg_add : g (s, t + 1) = 0 := by
      by_contra hne
      exact absurd (hg _ hne).2 (by simp only; linarith [ht.1])
    have hg_sub : g (s, t - 1) = 0 := by
      by_contra hne
      exact absurd (hg _ hne).1 (by simp only; linarith [ht.2])
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply, comp_apply, Prod.mk_add_mk, add_zero,
      e, ← sub_eq_add_neg, periodizeSnd_eq_of_mem_Icc hh ht, hg_add, hg_sub, sub_zero]
    abel
  -- Each of the three terms has `L²` norm on the strip at most that of `e` on the plane.
  have htr (v : ℝ × ℝ) : eLpNorm (e ∘ (· + v)) 2 stripMeasure ≤ eLpNorm e 2 volume := by
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans_eq ?_
    exact eLpNorm_comp_measurePreserving he (measurePreserving_add_right volume v)
  rw [eLpNorm_congr_ae heq, eLpNorm_neg]
  calc eLpNorm (e ∘ (· + (0, 1)) + e + e ∘ (· + (0, -1))) 2 stripMeasure
      ≤ eLpNorm (e ∘ (· + (0, 1))) 2 stripMeasure + eLpNorm e 2 stripMeasure +
          eLpNorm (e ∘ (· + (0, -1))) 2 stripMeasure :=
        (eLpNorm_add_le one_le_two).trans (by gcongr; exact eLpNorm_add_le one_le_two)
    _ ≤ eLpNorm e 2 volume + eLpNorm e 2 volume + eLpNorm e 2 volume :=
        add_le_add (add_le_add (htr _) (eLpNorm_mono_measure _ Measure.restrict_le_self)) (htr _)
    _ = 3 * eLpNorm e 2 volume := by ring

/-- **Mollifying and periodizing.** An `L²` map on the plane supported in a box
`[-n, n] × (0, 1)` is approximated in `L²` of the strip by test sections: for every `δ ≠ 0` some
test section is within `3 δ` of it. -/
private theorem exists_mem_testSection_eLpNorm_sub_le [CompleteSpace W] {g : ℝ × ℝ → W}
    (hg : MemLp g 2 volume) {n : ℝ} (hgn : ∀ z, g z ≠ 0 → |z.1| ≤ n ∧ z.2 ∈ Ioo (0 : ℝ) 1)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ ξ ∈ testSection W, eLpNorm (g - ξ) 2 stripMeasure ≤ 3 * δ := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  -- Mollify `g` by a smooth bump of radius `2 / (k + 2) ≤ 1`, to within `δ` in `L²`.
  let phi : ℕ → ContDiffBump (0 : ℝ × ℝ) := fun k ↦
    ⟨1 / (k + 2), 2 / (k + 2), by positivity, by gcongr; norm_num⟩
  have hphi (k : ℕ) : (phi k).rOut = 2 / ((k : ℝ) + 2) := rfl
  have hphi' : Tendsto (fun k ↦ (phi k).rOut) atTop (𝓝 0) := by
    simp only [hphi]
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  obtain ⟨k, hk⟩ := ((tendsto_eLpNorm_normed_convolution_sub ENNReal.ofNat_ne_top hphi'
    hg).eventually (gt_mem_nhds (pos_iff_ne_zero.2 hδ))).exists
  set h := (phi k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  have hrOut : (phi k).rOut ≤ 1 := by
    rw [hphi, div_le_one (by positivity)]
    linarith [k.cast_nonneg (α := ℝ)]
  -- The mollification is smooth and supported in `(-n - 1, n + 1) × (-1, 2)`.
  have hsupp (z : ℝ × ℝ) (hz : h z ≠ 0) : |z.1| < n + 1 ∧ z.2 ∈ Ioo (-1 : ℝ) 2 := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 (support_convolution_subset _ hz)
    rw [(phi k).support_normed_eq, Metric.mem_ball, dist_zero_right] at ha
    obtain ⟨hb₁, hb₂⟩ := hgn b hb
    have ha₁ := (norm_fst_le a).trans_lt (ha.trans_le hrOut)
    have ha₂ := (norm_snd_le a).trans_lt (ha.trans_le hrOut)
    rw [Real.norm_eq_abs] at ha₁ ha₂
    refine ⟨(abs_add_le _ _).trans_lt (by linarith), ?_, ?_⟩ <;>
      simp only [Prod.snd_add] <;> linarith [abs_lt.1 ha₂, hb₂.1, hb₂.2]
  have hhc : ContDiff ℝ 2 h :=
    (phi k).hasCompactSupport_normed.contDiff_convolution_left _ (phi k).contDiff_normed
      (hg.locallyIntegrable one_le_two)
  -- Its periodization is a test section within `3 δ` of `g`.
  refine ⟨periodizeSnd h, mem_testSection_iff.2 ⟨contDiff_periodizeSnd hhc fun z hz ↦
    (hsupp z hz).2, periodizeSnd_add_one h, n + 1, fun s t hs ↦ ?_⟩, ?_⟩
  · rw [periodizeSnd_apply]
    refine (tsum_congr fun j : ℤ ↦ ?_).trans tsum_zero
    by_contra hne
    exact absurd (hsupp _ hne).1 (by simpa using hs)
  · refine (eLpNorm_sub_periodizeSnd_le (fun z hz ↦ (hgn z hz).2) (fun z hz ↦ (hsupp z hz).2)
      (hhc.continuous.aestronglyMeasurable.sub hg.aestronglyMeasurable)).trans
      (by gcongr)

/-- **Test sections are dense in `L²` of the cylinder.** The `L²` classes of the `C²` maps of
period one in `t` that vanish for `|s|` large are dense in `L²(ℝ × [0, 1], W)`. -/
theorem dense_testSectionLp [CompleteSpace W] :
    Dense (testSectionLp W : Set (Lp W 2 stripMeasure)) := by
  refine Metric.dense_iff.2 fun η r hr ↦ ?_
  set δ : ℝ≥0∞ := ENNReal.ofReal (r / 5)
  have hδ : δ ≠ 0 := by simp [δ, hr]
  -- Extend `η` by zero to the plane and approximate it by a continuous compactly supported map.
  have hP : MeasurableSet (univ ×ˢ Icc (0 : ℝ) 1) :=
    (MeasurableSet.univ (α := ℝ)).prod measurableSet_Icc
  have hf : MemLp ((univ ×ˢ Icc (0 : ℝ) 1).indicator η) 2 volume :=
    (memLp_indicator_iff_restrict hP.nullMeasurableSet).2 (Lp.memLp η)
  obtain ⟨g, hgc, hfg, -, hgm⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top hδ
  obtain ⟨n, hn⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  -- Cut it off to the open strip and approximate the result by a test section.
  set g' := (univ ×ˢ Ioo (0 : ℝ) 1).indicator g
  have hg'n (z : ℝ × ℝ) (hz : g' z ≠ 0) : |z.1| ≤ n ∧ z.2 ∈ Ioo (0 : ℝ) 1 := by
    obtain ⟨h0, h1, hgz⟩ : 0 < z.2 ∧ z.2 < 1 ∧ g z ≠ 0 := by
      simpa [g', indicator_apply_ne_zero] using hz
    refine ⟨?_, h0, h1⟩
    have := hn (subset_tsupport g hgz)
    rw [Metric.mem_closedBall, dist_zero_right] at this
    simpa [Real.norm_eq_abs] using (norm_fst_le z).trans this
  obtain ⟨ξ, hξ, hgξ⟩ := exists_mem_testSection_eLpNorm_sub_le
    (hgm.indicator ((MeasurableSet.univ (α := ℝ)).prod measurableSet_Ioo).nullMeasurableSet)
    hg'n hδ
  refine ⟨(memLp_of_mem_testSection hξ).toLp ξ, ?_, toLp_mem_testSectionLp hξ _⟩
  -- The total error is at most `δ + 3 δ < r`.
  have heq : ⇑η - g' =ᵐ[stripMeasure] (univ ×ˢ Icc (0 : ℝ) 1).indicator η - g := by
    filter_upwards [ae_restrict_mem hP, ae_mem_openStrip] with z hz hz'
    simp [g', indicator_of_mem hz, indicator_of_mem hz']
  have h₁ : eLpNorm (⇑η - g') 2 stripMeasure ≤ δ := by
    rw [eLpNorm_congr_ae heq]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hfg
  have hle : eLpNorm (⇑η - ξ) 2 stripMeasure ≤ 4 * δ := by
    have := eLpNorm_add_le (f := ⇑η - g') (g := g' - ξ) (μ := stripMeasure) one_le_two
    rw [sub_add_sub_cancel] at this
    calc _ ≤ _ := this
      _ ≤ δ + 3 * δ := add_le_add h₁ hgξ
      _ = 4 * δ := by ring
  rw [Metric.mem_ball, dist_comm, Lp.dist_def,
    eLpNorm_congr_ae ((ae_eq_refl _).sub (memLp_of_mem_testSection hξ).coeFn_toLp)]
  have h4 : 4 * δ = ENNReal.ofReal (4 * (r / 5)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp [δ]
  calc (eLpNorm (⇑η - ξ) 2 stripMeasure).toReal ≤ 4 * (r / 5) :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) (hle.trans_eq h4)
    _ < r := by linarith

end TauCeti.CylinderSobolev
