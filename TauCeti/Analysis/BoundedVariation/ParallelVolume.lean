/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.BoundedVariation.Coarea
import TauCeti.Analysis.Calculus.FDeriv.InfDist
import TauCeti.Topology.MetricSpace.Thickening

/-!
# The volume of parallel sets as an integral of perimeters

Let `μ` be an additive Haar measure on a finite-dimensional real inner product space `E`. For every
set `s` and every radius `r`, the volume of the open shell around the closure of `s` is the
integral of the perimeters of the closed parallel sets of `s`:

`μ(s_r \ closure s) = ∫_0^r P(cthickening t s) dt`,

where `s_r = Metric.thickening r s` is the open `r`-neighbourhood of `s`
(`TauCeti.measure_thickening_sdiff_closure_eq_lintegral_perimeter`). For bounded `s` the closed
neighbourhood has the same shell volume
(`TauCeti.measure_cthickening_sdiff_closure_eq_lintegral_perimeter`). No measurability, finite
perimeter or regularity hypothesis on `s` is needed.

For a compact set `K` the closed neighbourhoods are the outer parallel sets
`K + t • closedBall 0 1`. If the perimeters of these parallel sets are upper semicontinuous at
`t = 0`, that is `limsup_{t → 0⁺} P(K + t • closedBall 0 1) ≤ P(K) < ∞`, then the volume of the
parallel sets has right derivative `P(K)` at `t = 0`
(`IsCompact.hasDerivWithinAt_measureReal_add_smul_closedBall`). This complements
`IsCompact.perimeter_le_of_hasDerivWithinAt`, which bounds `P(K)` by that derivative for every
compact set. Some hypothesis of this kind is needed: a segment in the plane has perimeter zero,
while its parallel perimeters tend to twice its length.

The shell formula is the coarea formula
`LocallyLipschitzOn.lintegral_perimeter_eq_setLIntegral_enorm_fderiv` for the truncated distance
`x ↦ min (infDist x s) r`. Its superlevel sets at levels `0 ≤ t < r` are the complements of the
closed parallel sets, and by Rademacher's theorem its derivative has norm one almost everywhere
on the shell (`TauCeti.norm_fderiv_infDist_eq_one`) and vanishes almost everywhere off it. The
derivative statement is then the fundamental theorem of calculus at a point of continuity.

## Main results

* `TauCeti.measure_thickening_sdiff_closure_eq_lintegral_perimeter`: the open shell volume is
  the integral of the perimeters of the closed parallel sets.
* `TauCeti.measure_cthickening_sdiff_closure_eq_lintegral_perimeter`: the same for the closed
  shell around a bounded set.
* `IsCompact.hasDerivWithinAt_measureReal_add_smul_closedBall`: the right derivative at zero of
  the parallel volume of a compact set is its perimeter, when the parallel perimeters are upper
  semicontinuous at zero.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Section 2.13, for Minkowski content.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.5.
-/

public section

noncomputable section

open MeasureTheory Metric Filter Set TopologicalSpace
open scoped ENNReal Pointwise Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The perimeter of the closed `t`-neighbourhood of a set is measurable in `t`. -/
private theorem measurable_perimeter_cthickening (s : Set E) :
    Measurable fun t => perimeter μ ⊤ (cthickening t s) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [cthickening_empty, perimeter_empty, measurable_const]
  have hfun : (fun t => perimeter μ ⊤ (cthickening t s)) =
      (Iio 0).piecewise (fun _ => perimeter μ ⊤ (closure s))
        (fun t => perimeter μ ⊤ {x | t < infDist x s}) := by
    ext t
    by_cases ht : t < 0
    · rw [piecewise_eq_of_mem _ _ _ ht, cthickening_of_nonpos ht.le]
    · rw [piecewise_eq_of_notMem _ _ _ ht, ← perimeter_compl (s := cthickening t s)]
      congr 1
      ext x
      simp [mem_cthickening_iff_infDist_le hs (not_lt.1 ht)]
  rw [hfun]
  exact measurable_const.piecewise measurableSet_Iio
    (measurable_perimeter_setOf_lt (continuous_infDist_pt s).aemeasurable)

/-- Almost everywhere, the derivative of the truncated distance `x ↦ min (infDist x s) r` has norm
one on the open shell `thickening r s \ closure s` and vanishes off it. -/
private theorem enorm_fderiv_min_infDist_ae_eq {s : Set E} (hs : s.Nonempty) {r : ℝ} :
    (fun x => ‖fderiv ℝ (fun y => min (infDist y s) r) x‖ₑ) =ᵐ[μ]
      (thickening r s \ closure s).indicator 1 := by
  have hlip : LipschitzWith 1 fun y => min (infDist y s) r :=
    (lipschitz_infDist_pt (s := s)).min_const r
  filter_upwards [hlip.ae_differentiableAt (μ := μ)] with x hx
  by_cases hcl : x ∈ closure s
  · -- On the closure the truncated distance attains its minimum.
    have hmin : IsLocalMin (fun y => min (infDist y s) r) x := by
      refine Eventually.of_forall fun y => ?_
      simp only [(mem_closure_iff_infDist_zero hs).1 hcl]
      exact min_le_min_right r infDist_nonneg
    rw [hmin.fderiv_eq_zero, indicator_of_notMem
      (fun h : x ∈ thickening r s \ closure s => h.2 hcl)]
    -- The `ENorm` instance on the derivative is reached through a different instance path than
    -- the one `enorm_zero` is stated for, so the lemma is applied at the explicit type.
    exact (enorm_eq_zero (a := (0 : E →L[ℝ] ℝ))).2 rfl
  by_cases hr : r ≤ infDist x s
  · -- Far from `s` the truncated distance attains its maximum.
    have hmax : IsLocalMax (fun y => min (infDist y s) r) x :=
      Eventually.of_forall fun y => by simp [min_eq_right hr]
    have hth : x ∉ thickening r s := by
      rw [mem_thickening_iff_infDist_lt hs]
      exact not_lt.2 hr
    rw [hmax.fderiv_eq_zero, indicator_of_notMem
      (fun h : x ∈ thickening r s \ closure s => hth h.1)]
    exact (enorm_eq_zero (a := (0 : E →L[ℝ] ℝ))).2 rfl
  -- On the shell the truncated distance is the distance near `x`.
  replace hr := not_le.1 hr
  have hloc : (fun y => min (infDist y s) r) =ᶠ[𝓝 x] (infDist · s) := by
    filter_upwards [(continuous_infDist_pt s).continuousAt.eventually_lt continuousAt_const hr]
      with y hy using min_eq_left hy.le
  have hd : DifferentiableAt ℝ (infDist · s) x := hx.congr_of_eventuallyEq hloc.symm
  have hmem : x ∈ thickening r s \ closure s := ⟨(mem_thickening_iff_infDist_lt hs).2 hr, hcl⟩
  rw [hloc.fderiv_eq, indicator_of_mem hmem, ← ofReal_norm,
    norm_fderiv_infDist_eq_one hs hcl hd]
  simp

/-- **The volume of a parallel shell is the integral of the parallel perimeters.** Against an
additive Haar measure, for every set `s` and every `r`, the volume of the open shell
`thickening r s \ closure s` is the integral over `0 < t < r` of the perimeters of the closed
`t`-neighbourhoods of `s`. -/
theorem measure_thickening_sdiff_closure_eq_lintegral_perimeter (s : Set E) (r : ℝ) :
    μ (thickening r s \ closure s) = ∫⁻ t in Ioo 0 r, perimeter μ ⊤ (cthickening t s) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [thickening_of_nonpos hr, Ioo_eq_empty_of_le hr]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [perimeter_empty]
  set u : E → ℝ := fun y => min (infDist y s) r
  have hlip : LipschitzWith 1 u := (lipschitz_infDist_pt (s := s)).min_const r
  have hcoarea := (hlip.locallyLipschitz.locallyLipschitzOn (s := ((⊤ : Opens E) : Set E))
    ).lintegral_perimeter_eq_setLIntegral_enorm_fderiv (μ := μ)
  -- The superlevel sets of `u` at levels `0 ≤ t < r` are complements of closed parallel sets;
  -- the other levels give the whole space or the empty set.
  have hlevel : (fun t => perimeter μ ⊤ {x | t < u x}) =
      (Ico 0 r).indicator fun t => perimeter μ ⊤ (cthickening t s) := by
    ext t
    by_cases ht : t ∈ Ico 0 r
    · rw [indicator_of_mem ht, ← perimeter_compl (s := cthickening t s)]
      congr 1
      ext x
      simp [u, lt_min_iff, ht.2, mem_cthickening_iff_infDist_le hs ht.1]
    rw [indicator_of_notMem ht]
    rcases not_and_or.1 ht with ht | ht
    · have : {x | t < u x} = univ :=
        eq_univ_of_forall fun x => (not_le.1 ht).trans_le (le_min infDist_nonneg hr.le)
      rw [this, perimeter_univ]
    · have : {x | t < u x} = ∅ :=
        eq_empty_of_forall_notMem fun x hx => ht ((hx : t < u x).trans_le (min_le_right _ _))
      rw [this, perimeter_empty]
  rw [hlevel, lintegral_indicator measurableSet_Ico, Opens.coe_top, Measure.restrict_univ,
    lintegral_congr_ae (enorm_fderiv_min_infDist_ae_eq hs),
    lintegral_indicator_one (isOpen_thickening.measurableSet.diff
      isClosed_closure.measurableSet)] at hcoarea
  rw [← hcoarea]
  exact setLIntegral_congr Ioo_ae_eq_Ico.symm

/-- **The volume of a closed parallel shell is the integral of the parallel perimeters.** Against
an additive Haar measure, for every bounded set `s` and every `r`, the volume of the closed shell
`cthickening r s \ closure s` is the integral over `0 < t < r` of the perimeters of the closed
`t`-neighbourhoods of `s`. In particular the level set `{x | infDist x s = r}` is null. -/
theorem measure_cthickening_sdiff_closure_eq_lintegral_perimeter {s : Set E}
    (hs : Bornology.IsBounded s) (r : ℝ) :
    μ (cthickening r s \ closure s) = ∫⁻ t in Ioo 0 r, perimeter μ ⊤ (cthickening t s) := by
  rcases lt_or_ge r 0 with hr | hr
  · simp [cthickening_of_nonpos hr.le, Ioo_eq_empty_of_le hr.le]
  set f : ℝ → ℝ≥0∞ := fun t => perimeter μ ⊤ (cthickening t s)
  set ν : Measure ℝ := volume.withDensity f
  -- Both sides are limits from the right of the corresponding open-shell quantities.
  have hμ : Tendsto (fun ρ => μ (thickening ρ s \ closure s)) (𝓝[>] r)
      (𝓝 (μ (cthickening r s \ closure s))) := by
    have h := tendsto_measure_biInter_gt (μ := μ) (s := fun ρ => thickening ρ s \ closure s)
      (a := r) (fun ρ _ => (isOpen_thickening.measurableSet.diff
        isClosed_closure.measurableSet).nullMeasurableSet)
      (fun i j _ hij => sdiff_subset_sdiff_left (thickening_mono hij s))
      ⟨r + 1, by linarith, ((hs.thickening).measure_lt_top.trans_le' (measure_mono
        sdiff_subset)).ne⟩
    have hinter : (⋂ ρ > r, thickening ρ s \ closure s) = cthickening r s \ closure s := by
      rw [cthickening_eq_iInter_thickening hr]
      ext x
      simp only [mem_iInter, Set.mem_sdiff]
      exact ⟨fun h => ⟨fun ρ hρ => (h ρ hρ).1, (h (r + 1) (by linarith)).2⟩,
        fun h ρ hρ => ⟨h.1 ρ hρ, h.2⟩⟩
    rwa [hinter] at h
  have hν : Tendsto (fun ρ => ν (Ioo 0 ρ)) (𝓝[>] r) (𝓝 (ν (Ioo 0 r))) := by
    have h := tendsto_measure_biInter_gt (μ := ν) (s := fun ρ => Ioo 0 ρ) (a := r)
      (fun ρ _ => measurableSet_Ioo.nullMeasurableSet)
      (fun i j _ hij => Ioo_subset_Ioo_right hij)
      ⟨r + 1, by linarith, by
        rw [withDensity_apply _ measurableSet_Ioo,
          ← measure_thickening_sdiff_closure_eq_lintegral_perimeter]
        exact ((hs.thickening).measure_lt_top.trans_le' (measure_mono sdiff_subset)).ne⟩
    have hinter : (⋂ ρ > r, Ioo (0 : ℝ) ρ) = Ioc 0 r := by
      ext t
      simp only [mem_iInter, mem_Ioo, mem_Ioc]
      refine ⟨fun h => ⟨(h (r + 1) (by linarith)).1, le_of_forall_gt fun ρ hρ => (h ρ hρ).2⟩,
        fun h ρ hρ => ⟨h.1, h.2.trans_lt hρ⟩⟩
    rwa [hinter, measure_congr (Ioo_ae_eq_Ioc (μ := ν)).symm] at h
  have heq : (fun ρ => μ (thickening ρ s \ closure s)) = fun ρ => ν (Ioo 0 ρ) := by
    ext ρ
    rw [withDensity_apply _ measurableSet_Ioo,
      measure_thickening_sdiff_closure_eq_lintegral_perimeter]
  rw [heq] at hμ
  rw [tendsto_nhds_unique hμ hν, withDensity_apply _ measurableSet_Ioo]

/-- The closed parallel sets of a compact set converge to it in measure, so lower semicontinuity
of the perimeter turns upper semicontinuity of the parallel perimeters at `0` into convergence. -/
private theorem tendsto_perimeter_cthickening {K : Set E} (hK : IsCompact K)
    (hlim : limsup (fun t => perimeter μ ⊤ (cthickening t K)) (𝓝[>] 0) ≤ perimeter μ ⊤ K) :
    Tendsto (fun t => perimeter μ ⊤ (cthickening t K)) (𝓝[>] 0) (𝓝 (perimeter μ ⊤ K)) := by
  have hshell : Tendsto (fun t => μ (cthickening t K \ K)) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_measure_biInter_gt (μ := μ) (s := fun t => cthickening t K \ K) (a := 0)
      (fun t _ => (isClosed_cthickening.measurableSet.diff
        hK.isClosed.measurableSet).nullMeasurableSet)
      (fun i j _ hij => sdiff_subset_sdiff_left (cthickening_mono hij K))
      ⟨1, one_pos, ((hK.cthickening (r := 1)).measure_lt_top.trans_le' (measure_mono
        sdiff_subset)).ne⟩
    have hinter : (⋂ t > (0 : ℝ), cthickening t K \ K) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      simp only [mem_iInter, Set.mem_sdiff] at hx
      refine (hx 1 one_pos).2 ?_
      rw [← hK.isClosed.closure_eq, closure_eq_iInter_cthickening]
      exact mem_iInter₂.2 fun t ht => (hx t ht).1
    rwa [hinter, measure_empty] at h
  refine tendsto_of_le_liminf_of_limsup_le ?_ hlim
  refine perimeter_le_liminf (Eventually.of_forall fun t =>
    isClosed_cthickening.measurableSet.nullMeasurableSet)
    hK.isClosed.measurableSet.nullMeasurableSet fun C _ _ =>
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hshell (fun _ => zero_le)
        fun t => measure_mono ?_
  rw [symmDiff_of_ge (self_subset_cthickening K)]
  exact inter_subset_left

/-- The real volume of a closed parallel set of a compact set is the volume of the set plus the
integral of the parallel perimeters. -/
private theorem measureReal_cthickening_eq_add_integral_perimeter {K : Set E} (hK : IsCompact K)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real (cthickening t K) =
      μ.real K + ∫ τ in 0..t, (perimeter μ ⊤ (cthickening τ K)).toReal := by
  have hf := measurable_perimeter_cthickening (μ := μ) K
  have hfin : μ (cthickening t K) ≠ ∞ := (hK.cthickening (r := t)).measure_lt_top.ne
  have hint : μ (cthickening t K \ K) = ∫⁻ τ in Ioo 0 t, perimeter μ ⊤ (cthickening τ K) := by
    simpa [hK.isClosed.closure_eq] using
      measure_cthickening_sdiff_closure_eq_lintegral_perimeter (μ := μ) hK.isBounded t
  have hlt : ∫⁻ τ in Ioo 0 t, perimeter μ ⊤ (cthickening τ K) ≠ ∞ :=
    hint ▸ measure_ne_top_of_subset sdiff_subset hfin
  rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo,
    integral_toReal hf.aemeasurable (ae_lt_top' hf.aemeasurable hlt), ← hint,
    measureReal_def, measureReal_def, measure_sdiff (self_subset_cthickening K)
      hK.isClosed.measurableSet.nullMeasurableSet
      (measure_ne_top_of_subset (self_subset_cthickening K) hfin),
    ENNReal.toReal_sub_of_le (measure_mono (self_subset_cthickening K)) hfin]
  ring

/-- **The first variation of parallel volume is the perimeter.** Against an additive Haar
measure, let `K` be a compact set of finite perimeter whose outer parallel sets
`K + t • closedBall 0 1` have perimeters upper semicontinuous at `t = 0`:
`limsup_{t → 0⁺} P(K + t • closedBall 0 1) ≤ P(K)`. Then the volume of the outer parallel sets has
right derivative `P(K)` at `t = 0`. -/
theorem _root_.IsCompact.hasDerivWithinAt_measureReal_add_smul_closedBall {K : Set E}
    (hK : IsCompact K) (hP : perimeter μ ⊤ K ≠ ∞)
    (hlim : limsup (fun t : ℝ => perimeter μ ⊤ (K + t • closedBall (0 : E) 1)) (𝓝[>] 0) ≤
      perimeter μ ⊤ K) :
    HasDerivWithinAt (fun t : ℝ => μ.real (K + t • closedBall (0 : E) 1))
      (perimeter μ ⊤ K).toReal (Ici 0) 0 := by
  -- For `t ≥ 0` the outer parallel set is the closed `t`-thickening of `K`.
  have hpar {t : ℝ} (ht : 0 ≤ t) : K + t • closedBall (0 : E) 1 = cthickening t K := by
    rw [smul_unitClosedBall_of_nonneg ht, hK.add_closedBall_zero ht]
  set f : ℝ → ℝ≥0∞ := fun t => perimeter μ ⊤ (cthickening t K)
  have hf0 : f 0 = perimeter μ ⊤ K := by simp [f, hK.isClosed.closure_eq]
  have hlimf : Tendsto f (𝓝[>] 0) (𝓝 (perimeter μ ⊤ K)) := by
    refine tendsto_perimeter_cthickening hK ((limsup_congr ?_).trans_le hlim)
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [hpar (le_of_lt ht)]
  have hg : ContinuousWithinAt (fun t => (f t).toReal) (Ioi 0) 0 := by
    simpa [ContinuousWithinAt, hf0, Function.comp_def] using (ENNReal.tendsto_toReal hP).comp hlimf
  -- By the fundamental theorem of calculus, the integral of the parallel perimeters has right
  -- derivative `P(K)` at `0`.
  have hmeas : StronglyMeasurableAtFilter (fun t => (f t).toReal) (𝓝[>] 0) :=
    (measurable_perimeter_cthickening K).ennreal_toReal.stronglyMeasurable
      |>.stronglyMeasurableAtFilter
  have hderiv := (intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (b := 0)
    (s := Ici 0) (t := Ioi 0) IntervalIntegrable.refl hmeas hg).const_add (μ.real K)
  have hvol {t : ℝ} (ht : t ∈ Ici 0) :
      μ.real (K + t • closedBall (0 : E) 1) = μ.real K + ∫ τ in 0..t, (f τ).toReal := by
    rw [hpar ht]
    exact measureReal_cthickening_eq_add_integral_perimeter hK ht
  exact (hderiv.congr (fun t ht => hvol ht) (hvol self_mem_Ici)).congr_deriv
    (congrArg ENNReal.toReal hf0)

end TauCeti
