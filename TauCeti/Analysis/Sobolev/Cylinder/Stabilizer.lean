/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.Sobolev.Cylinder.Gluing
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import TauCeti.Analysis.Fredholm.Stabilization
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.Topology.Algebra.Module.Complement
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Stabilizing Fredholm operators on the cylinder by test sections

A Fredholm operator `D` with values in `L²(ℝ × S¹, W)` need not be onto. Its cokernel is
finite-dimensional, and adjoining a finite-dimensional space `S` of sections that complements the
range of `D` makes the stabilized operator `(ξ, σ) ↦ D ξ + σ` onto, without changing its kernel:
since `S` meets the range of `D` only in `0`, that kernel is `ker D × {0}`
(`ContinuousLinearMap.ker_coprod_of_disjoint_range`). This is how the linear gluing of
Cauchy–Riemann and Floer operators handles pieces with cokernel: the stabilized gluing theorem
`TauCeti.CylinderSobolev.exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff`
needs stabilizers whose sections vanish near the ends that are glued, and bounded linear right
inverses of the stabilized pieces.

This file constructs such stabilizers out of test sections, the `C²` sections of the cylinder that
vanish for `|s|` large (`TauCeti.CylinderSobolev.testSection`).

* **Density.** The `L²` classes of test sections (`TauCeti.CylinderSobolev.testSectionLp`) are
  dense in `L²(ℝ × [0, 1], W)` (`TauCeti.CylinderSobolev.dense_testSectionLp`). An `L²` section
  is first approximated by a continuous compactly supported map on the plane, cut off to the open
  strip `ℝ × (0, 1)`. Its mollification by a smooth bump of radius at most `1` is smooth and
  supported in `ℝ × (-1, 2)`, and the periodization `Σₖ h(s, t + k)` of such a map `h` is a test
  section. On the strip it differs from `h` only by the two translates `h(s, t ± 1)`, and these are
  as small in `L²` as the mollification error, since the cut-off map vanishes there.
* **Bounded support.** A finite-dimensional space of classes of test sections has a common bound
  `T` with all its sections vanishing for `|s| > T`
  (`TauCeti.CylinderSobolev.exists_forall_ae_eq_zero_of_le_testSectionLp`).
* **Stabilizers.** A Fredholm operator `D` from a Banach space into `L²` has a stabilizer `S` made
  of test sections, a topological complement of its range, hence finite-dimensional and isomorphic
  to the cokernel of `D`. The sections of `S` vanish for `|s|` large, and the stabilized operator
  has a bounded linear right inverse
  (`ContinuousLinearMap.IsFredholm.exists_le_testSectionLp_isTopCompl`).
* **Gluing Fredholm pieces.** For two first-order operators `D₁`, `D₂` on the cylinder with
  matching ends, Fredholm on `W^{1,2}`, such stabilizers `S₁` and `S₂` stabilize every glued
  operator `D_R` with a long neck, with right inverses of `D_R ⊕ j_R` bounded independently of `R`
  (`exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff_of_isFredholm`).
  No surjectivity of the pieces is assumed.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 3.1
  (stabilizing a Fredholm operator by a finite-dimensional space complementing its range) and
  Chapter 10 (linear gluing).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3.
-/

public section

noncomputable section

open Filter MeasureTheory Set Function
open scoped ENNReal Topology Convolution

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {W : Type*} [NormedAddCommGroup W]

/-! ### Periodization in `t` -/

/-- The periodization `z ↦ Σₖ h(z.1, z.2 + k)` of a map on the plane in the second variable. -/
private def periodizeSnd (h : ℝ × ℝ → W) (z : ℝ × ℝ) : W :=
  ∑' k : ℤ, h (z.1, z.2 + k)

/-- Near a point with second coordinate `t₀`, the periodization of a map supported in
`ℝ × (-1, 2)` is a sum over a fixed finite set of translates. -/
private theorem periodizeSnd_eq_sum {h : ℝ × ℝ → W} (hh : ∀ z, h z ≠ 0 → z.2 ∈ Ioo (-1 : ℝ) 2)
    {t₀ : ℝ} {z : ℝ × ℝ} (hz : |z.2 - t₀| < 1) :
    periodizeSnd h z = ∑ k ∈ Finset.Ioo ⌊-2 - t₀⌋ ⌈3 - t₀⌉, h (z.1, z.2 + k) := by
  refine tsum_eq_sum fun k hk ↦ ?_
  by_contra hne
  obtain ⟨h₁, h₂⟩ := hh _ hne
  obtain ⟨hz₁, hz₂⟩ := abs_lt.1 hz
  have hfl := Int.floor_le (-2 - t₀)
  have hce := Int.le_ceil (3 - t₀)
  refine hk (Finset.mem_Ioo.2 ⟨?_, ?_⟩)
  · exact_mod_cast (show ((⌊-2 - t₀⌋ : ℤ) : ℝ) < k by simp only at h₁; linarith)
  · exact_mod_cast (show (k : ℝ) < ⌈3 - t₀⌉ by simp only at h₂; linarith)

/-- The periodization has period one in the second variable. -/
private theorem periodizeSnd_add_one (h : ℝ × ℝ → W) (s t : ℝ) :
    periodizeSnd h (s, t + 1) = periodizeSnd h (s, t) := by
  have := (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ ↦ h (s, t + k))
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one] at this
  rw [periodizeSnd, periodizeSnd, ← this]
  exact tsum_congr fun k ↦ by rw [add_assoc, add_comm (1 : ℝ)]

/-- On the strip `ℝ × [0, 1]`, the periodization of a map supported in `ℝ × (-1, 2)` only sees the
map and its two translates by `±1` in the second variable. -/
private theorem periodizeSnd_eq_of_mem_Icc {h : ℝ × ℝ → W}
    (hh : ∀ z, h z ≠ 0 → z.2 ∈ Ioo (-1 : ℝ) 2) {s t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    periodizeSnd h (s, t) = h (s, t + 1) + h (s, t) + h (s, t + -1) := by
  rw [periodizeSnd, tsum_eq_sum (s := {1, 0, -1}) fun k hk ↦ ?_]
  · simp [add_assoc]
  by_contra hne
  obtain ⟨h₁, h₂⟩ := hh _ hne
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  rcases (by omega : k ≤ -2 ∨ 2 ≤ k) with hk' | hk'
  · have : (k : ℝ) ≤ -2 := by exact_mod_cast hk'
    simp only at h₁
    linarith [ht.2]
  · have : (2 : ℝ) ≤ k := by exact_mod_cast hk'
    simp only at h₂
    linarith [ht.1]

variable [NormedSpace ℝ W]

/-- The periodization of a smooth map supported in `ℝ × (-1, 2)` is smooth. -/
private theorem contDiff_periodizeSnd {n : WithTop ℕ∞} {h : ℝ × ℝ → W} (hc : ContDiff ℝ n h)
    (hh : ∀ z, h z ≠ 0 → z.2 ∈ Ioo (-1 : ℝ) 2) : ContDiff ℝ n (periodizeSnd h) := by
  refine contDiff_iff_contDiffAt.2 fun z₀ ↦ ?_
  have hev : periodizeSnd h =ᶠ[𝓝 z₀]
      fun z ↦ ∑ k ∈ Finset.Ioo ⌊-2 - z₀.2⌋ ⌈3 - z₀.2⌉, h (z.1, z.2 + k) := by
    filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hz
    exact periodizeSnd_eq_sum hh ((le_max_right _ _).trans_lt hz)
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (ContDiff.sum fun k _ ↦
    hc.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))).contDiffAt

/-! ### Density of test sections in `L²` -/

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
    have hg_sub : g (s, t + -1) = 0 := by
      by_contra hne
      exact absurd (hg _ hne).1 (by simp only; linarith [ht.2])
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply, comp_apply, Prod.mk_add_mk, add_zero,
      e, periodizeSnd_eq_of_mem_Icc hh ht, hg_add, hg_sub, sub_zero]
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
  · refine (tsum_congr fun j : ℤ ↦ ?_).trans tsum_zero
    by_contra hne
    exact absurd (hsupp _ hne).1 (by simpa using hs)
  · refine (eLpNorm_sub_periodizeSnd_le (fun z hz ↦ (hgn z hz).2) (fun z hz ↦ (hsupp z hz).2)
      (hhc.continuous.aestronglyMeasurable.sub hg.aestronglyMeasurable)).trans
      (by gcongr)

/-- Almost every point of the strip lies in the open strip `ℝ × (0, 1)`. -/
private theorem ae_mem_Ioo_snd : ∀ᵐ z ∂stripMeasure, z.2 ∈ Ioo (0 : ℝ) 1 := by
  have hnull (c : ℝ) : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), z.2 ≠ c := by
    have : {z : ℝ × ℝ | ¬z.2 ≠ c} = univ ×ˢ {c} := by ext; simp
    rw [ae_iff, this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  filter_upwards [ae_restrict_mem ((MeasurableSet.univ (α := ℝ)).prod measurableSet_Icc),
    ae_restrict_of_ae (hnull 0), ae_restrict_of_ae (hnull 1)] with z hz h0 h1
  exact ⟨lt_of_le_of_ne hz.2.1 (Ne.symm h0), lt_of_le_of_ne hz.2.2 h1⟩

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
    filter_upwards [ae_restrict_mem hP, ae_mem_Ioo_snd] with z hz hz'
    simp [g', indicator_of_mem hz, indicator_of_mem (show z ∈ univ ×ˢ Ioo (0 : ℝ) 1 from
      ⟨mem_univ _, hz'⟩)]
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

/-! ### Stabilizers made of test sections -/

/-- The `L²` sections vanishing almost everywhere on `|s| > T`. -/
private def vanishingLp (T : ℝ) : Submodule ℝ (Lp W 2 stripMeasure) where
  carrier := {η | ∀ᵐ z ∂stripMeasure, T < |z.1| → η z = 0}
  zero_mem' := by
    rw [mem_ofPred_eq]
    filter_upwards [Lp.coeFn_zero W 2 stripMeasure] with z hz _ using hz
  add_mem' := by
    rintro η η' hη hη'
    rw [mem_ofPred_eq] at hη hη' ⊢
    filter_upwards [Lp.coeFn_add η η', hη, hη'] with z hz h h' hT
    exact hz.trans (by simp [h hT, h' hT])
  smul_mem' := by
    rintro c η hη
    rw [mem_ofPred_eq] at hη ⊢
    filter_upwards [Lp.coeFn_smul c η, hη] with z hz h hT
    exact hz.trans (by simp [h hT])

private theorem mem_vanishingLp_iff {T : ℝ} {η : Lp W 2 stripMeasure} :
    η ∈ vanishingLp T ↔ ∀ᵐ z ∂stripMeasure, T < |z.1| → η z = 0 :=
  Iff.rfl

private theorem vanishingLp_mono {T T' : ℝ} (h : T ≤ T') :
    vanishingLp (W := W) T ≤ vanishingLp T' := fun _ hη ↦ by
  rw [mem_vanishingLp_iff] at hη ⊢
  filter_upwards [hη] with z hz hT using hz (h.trans_lt hT)

/-- **Bounded support of finitely many test sections.** The sections of a finite-dimensional
space of `L²` classes of test sections all vanish for `|s|` beyond a common bound `T`. -/
theorem exists_forall_ae_eq_zero_of_le_testSectionLp {S : Submodule ℝ (Lp W 2 stripMeasure)}
    (hS : S ≤ testSectionLp W) [FiniteDimensional ℝ S] :
    ∃ T : ℝ, ∀ η ∈ S, ∀ᵐ z ∂stripMeasure, T < |z.1| → η z = 0 := by
  have key (η) (hη : η ∈ S) : ∃ T, η ∈ vanishingLp (W := W) T := by
    obtain ⟨ξ, hξ, hηξ⟩ := hS hη
    obtain ⟨-, -, R, hR⟩ := mem_testSection_iff.1 hξ
    refine ⟨R, mem_vanishingLp_iff.2 ?_⟩
    filter_upwards [hηξ] with z hz hT using hz.trans (hR z.1 z.2 hT.le)
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional S).2 inferInstance
  have hts : ∀ η ∈ t, η ∈ S := fun η hη ↦ ht ▸ Submodule.subset_span hη
  obtain ⟨T, hT⟩ : ∃ T, ∀ η ∈ t, η ∈ vanishingLp (W := W) T := by
    clear ht
    classical
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a t ha ih =>
      obtain ⟨T, hT⟩ := ih (fun η hη ↦ hts η (Finset.mem_insert_of_mem hη))
      obtain ⟨R, hR⟩ := key a (hts a (Finset.mem_insert_self a t))
      refine ⟨max T R, fun η hη ↦ ?_⟩
      rcases Finset.mem_insert.1 hη with rfl | hη
      · exact vanishingLp_mono (le_max_right T R) hR
      · exact vanishingLp_mono (le_max_left T R) (hT η hη)
  refine ⟨T, fun η hη ↦ ?_⟩
  rw [← ht] at hη
  exact mem_vanishingLp_iff.1 (Submodule.span_le.2 hT hη)

end TauCeti.CylinderSobolev

namespace ContinuousLinearMap

open TauCeti.CylinderSobolev TauCeti.StripSobolev

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- **Stabilizing a Fredholm operator by test sections.** A Fredholm operator `D` from a Banach
space into `L²(ℝ × [0, 1], W)` has a stabilizer `S` made of `L²` classes of test sections that is
a topological complement of the range of `D`, hence finite-dimensional and isomorphic to the
cokernel of `D`. Its sections all vanish for `|s|` beyond some `T`, and the stabilized operator
`(ξ, σ) ↦ D ξ + σ` has a bounded linear right inverse `Q`. -/
theorem IsFredholm.exists_le_testSectionLp_isTopCompl {D : E →L[ℝ] Lp W 2 stripMeasure}
    (hD : D.IsFredholm) :
    ∃ S ≤ testSectionLp W, S.IsTopCompl D.range ∧ FiniteDimensional ℝ S ∧
      (∃ T : ℝ, ∀ η ∈ S, ∀ᵐ z ∂stripMeasure, T < |z.1| → η z = 0) ∧
      ∃ Q : Lp W 2 stripMeasure →L[ℝ] E × S,
        (D.coprod S.subtypeL).comp Q = ContinuousLinearMap.id ℝ _ := by
  have := hD.finite_coker
  obtain ⟨S, hSD, hS⟩ := Submodule.exists_le_isTopCompl_of_dense hD.isClosed_range
    dense_testSectionLp
  have : FiniteDimensional ℝ S := (D.range.quotientEquivOfIsCompl S hS.isCompl).finiteDimensional
  have hsurj : Surjective (D.coprod S.subtypeL) := by
    apply LinearMap.range_eq_top.mp
    rw [range_coprod, Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
    exact hS.isCompl.sup_eq_top
  obtain ⟨Q, hQ⟩ := ((D.coprod S.subtypeL).exists_rightInverse_iff_closedComplemented_ker
    ((D.coprod S.subtypeL).isQuotientMap hsurj)).2
    (hD.coprod_of_finiteDimensional S.subtypeL).closedComplemented_ker
  exact ⟨S, hSD, hS.symm, this, exists_forall_ae_eq_zero_of_le_testSectionLp hSD, Q,
    ContinuousLinearMap.ext hQ⟩

end ContinuousLinearMap

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- **Linear gluing of Fredholm pieces.** Let `D₁` and `D₂` be first-order operators on the
cylinder with essentially bounded coefficient fields `M₁` and `M₂` whose ends match, Fredholm from
`W^{1,2}` to `L²`. There are stabilizers `S₁` and `S₂` made of `L²` classes of test sections,
topological complements of the ranges of `D₁` and `D₂`, such that for every sufficiently long neck
the glued operator `D_R`, stabilized by the translates `j_R` of `S₁` and `S₂` to the two ends of
the neck (`TauCeti.CylinderSobolev.gluedStabilizer`), has a bounded linear right inverse of norm at
most a constant `C` independent of `R`. -/
theorem exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff_of_isFredholm
    {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W} {M : ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1))
    (hD₁ : ((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).IsFredholm)
    (hD₂ : ((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).IsFredholm) :
    ∃ S₁ S₂ : Submodule ℝ (Lp W 2 stripMeasure), S₁ ≤ testSectionLp W ∧ S₂ ≤ testSectionLp W ∧
      S₁.IsTopCompl ((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).range ∧
      S₂.IsTopCompl ((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).range ∧
      ∃ C R₀ : ℝ, ∀ R ≥ R₀, ∃ Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂),
        (((jetOperator stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
            (H1 V).subtypeL).coprod (gluedStabilizer S₁.subtypeL S₂.subtypeL R)).comp Q =
            ContinuousLinearMap.id ℝ _ ∧
          ‖Q‖ ≤ C := by
  obtain ⟨S₁, hS₁, hc₁, -, ⟨T₁, hT₁⟩, Q₁, hQ₁⟩ := hD₁.exists_le_testSectionLp_isTopCompl
  obtain ⟨S₂, hS₂, hc₂, -, ⟨T₂, hT₂⟩, Q₂, hQ₂⟩ := hD₂.exists_le_testSectionLp_isTopCompl
  obtain ⟨R₀, hR₀⟩ := exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff
    hM₁ hM₂ h₁ h₂ (T := max T₁ T₂)
    (fun σ ↦ by
      filter_upwards [hT₁ σ σ.property] with z hz hT using
        hz ((le_max_left T₁ T₂).trans_lt (hT.trans_le (le_abs_self _))))
    (fun σ ↦ by
      filter_upwards [hT₂ σ σ.property] with z hz hT using
        hz ((le_max_right T₁ T₂).trans_lt (lt_neg_of_lt_neg hT |>.trans_le (neg_le_abs _))))
    hQ₁ hQ₂
  exact ⟨S₁, S₂, hS₁, hS₂, hc₁, hc₂, 4 * (‖Q₁‖ + ‖Q₂‖), R₀, hR₀⟩

end TauCeti.CylinderSobolev
