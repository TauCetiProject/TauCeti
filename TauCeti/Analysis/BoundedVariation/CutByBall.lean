/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.BoundedVariation.Multiplication
import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Cutting a set by a ball

Let `μ` be an additive Haar measure on a finite-dimensional real inner product space `E`, let `s`
be a null-measurable set, and write `m(ρ) = μ(s ∩ ball x₀ ρ)`. Cutting `s` by the ball
`ball x₀ r` adds at most the growth rate `m'(r)` of the volume of `s` in the ball to its perimeter:
for almost every radius `r`,

`P(s ∩ ball x₀ r) ≤ P(s; ball x₀ r) + m'(r)`

(`TauCeti.ae_perimeter_inter_ball_le`). Neither finite perimeter nor finite measure of `s` is
assumed. Classically, when `E` has positive dimension `n` and `μ` is Lebesgue measure on
`E ≃ ℝⁿ`, polar integration identifies `m'(r)` with the `(n - 1)`-dimensional measure of
`s ∩ sphere x₀ r` for almost every `r`, which turns this into the estimate
`P(s ∩ B_r) ≤ P(s; B_r) + Hⁿ⁻¹(s ∩ ∂B_r)`; for another Haar measure, both `m'(r)` and the
perimeter scale by the normalization constant. That identification is not made here. Combined
with the relative isoperimetric inequality, the estimate gives the differential inequalities for
`m` behind the density estimates of the boundary structure theory of sets of finite perimeter.

The estimate holds at every radius in a form with a lower difference quotient: for every open `U`
containing `closedBall x₀ r`,

`P(s ∩ ball x₀ r) ≤ P(s; U) + liminf_{h → 0⁺} μ(s ∩ (ball x₀ (r + h) \ ball x₀ r)) / h`

(`TauCeti.perimeter_inter_ball_le_add_liminf`), and the lower difference quotient is `m'(r)`
wherever `m` has a right derivative (`TauCeti.perimeter_inter_ball_le_add_of_hasDerivWithinAt`).
The almost-everywhere form follows because `m` and `ρ ↦ P(s; ball x₀ ρ)` are monotone.

The proof multiplies the indicator of `s` by smooth radial cutoffs `ψ`, equal to one on
`closedBall x₀ r` and vanishing off `ball x₀ (r + h)`, whose Lipschitz constant exceeds `1 / h`
(the optimal value when `E` is nontrivial) by an arbitrarily small factor
(`TauCeti.exists_contDiff_cutoff_closedBall_lipschitzWith`). The Leibniz bound
`TauCeti.totalVariationOn_mul_le` controls the variation of `ψ 1_s` by `P(s; U)` plus `1 / h`
times the measure of `s` in the shell where `ψ` varies, and lower semicontinuity of the total
variation passes to the limit `h → 0⁺`.

## Main results

* `TauCeti.perimeter_inter_ball_le_add_liminf`: the estimate at every radius, with the lower
  difference quotient of `m`.
* `TauCeti.perimeter_inter_ball_le_add_of_hasDerivWithinAt`: the estimate at a radius where `m`
  has a right derivative.
* `TauCeti.ae_perimeter_inter_ball_le`: `P(s ∩ ball x₀ r) ≤ P(s; ball x₀ r) + m'(r)` for almost
  every `r`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 15
  (intersections of sets of finite perimeter with balls).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7 (the density estimates at points of the reduced boundary).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Filter Function Set TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {s : Set E} {x₀ : E}
  {r R : ℝ} {ψ : E → ℝ}

/-- **The Leibniz bound for a radial cutoff.** If `ψ` is smooth with values in `[0, 1]`, equal to
one on `closedBall x₀ r`, vanishing off `ball x₀ R` and `K`-Lipschitz, then for every open `U`
containing `closedBall x₀ R` the variation of `ψ 1_s` on the whole space is at most
`P(s; U) + K μ(s ∩ (ball x₀ R \ ball x₀ r))`. -/
private theorem totalVariationOn_top_mul_indicator_le (hψ : ContDiff ℝ ∞ ψ)
    (hψ01 : range ψ ⊆ Icc 0 1) (hψ1 : EqOn ψ 1 (closedBall x₀ r)) (hψR : support ψ ⊆ ball x₀ R)
    {K : ℝ≥0} (hψK : LipschitzWith K ψ) {U : Opens E} (hU : closedBall x₀ R ⊆ U)
    (hs : NullMeasurableSet s μ) :
    totalVariationOn μ ⊤ (ψ * s.indicator 1) ≤
      perimeter μ U s + K * μ (s ∩ (ball x₀ R \ ball x₀ r)) := by
  have hψ0 (x : E) : 0 ≤ ψ x := (hψ01 (mem_range_self x)).1
  have hψle (x : E) : ψ x ≤ 1 := (hψ01 (mem_range_self x)).2
  have hsupp : tsupport ψ ∩ (⊤ : Opens E) ⊆ U :=
    inter_subset_left.trans ((closure_mono hψR).trans (closure_ball_subset_closedBall.trans hU))
  have h1 : LocallyIntegrable (1 : E → ℝ) μ := locallyIntegrable_const 1
  refine (totalVariationOn_mul_le hψ (c := 1) (fun x => abs_le.2 ⟨by linarith [hψ0 x], hψle x⟩)
    hsupp ((h1.indicator₀ hs).locallyIntegrableOn _)).trans ?_
  rw [ENNReal.ofReal_one, one_mul, ← perimeter_def]
  gcongr
  -- The derivative of `ψ` vanishes where `ψ` attains its maximum `1` or its minimum `0`, and is
  -- at most `K` in the shell between.
  have hpt (x : E) : ‖fderiv ℝ ψ x‖ₑ * ‖s.indicator (1 : E → ℝ) x‖ₑ ≤
      (s ∩ (ball x₀ R \ ball x₀ r)).indicator (fun _ => (K : ℝ≥0∞)) x := by
    by_cases hxs : x ∈ s
    swap
    · simp [hxs]
    by_cases hxA : x ∈ ball x₀ R \ ball x₀ r
    · rw [indicator_of_mem (mem_inter hxs hxA), indicator_of_mem hxs, Pi.one_apply, enorm_one,
        mul_one, ← ofReal_norm]
      exact (ENNReal.ofReal_le_ofReal (norm_fderiv_le_of_lipschitz ℝ hψK)).trans_eq
        ENNReal.ofReal_coe_nnreal
    suffices fderiv ℝ ψ x = 0 by simp [this, enorm_eq_nnnorm]
    rw [Set.mem_sdiff, not_and_or, not_not] at hxA
    rcases hxA with hxA | hxA
    · refine IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y => ?_)
      rw [notMem_support.1 fun h => hxA (hψR h)]
      exact hψ0 y
    · refine IsLocalMax.fderiv_eq_zero (Eventually.of_forall fun y => ?_)
      rw [hψ1 (ball_subset_closedBall hxA), Pi.one_apply]
      exact hψle y
  calc ∫⁻ x in (⊤ : Opens E), ‖fderiv ℝ ψ x‖ₑ * ‖s.indicator (1 : E → ℝ) x‖ₑ ∂μ
      ≤ ∫⁻ x, (s ∩ (ball x₀ R \ ball x₀ r)).indicator (fun _ => (K : ℝ≥0∞)) x ∂μ := by
        rw [Opens.coe_top, Measure.restrict_univ]
        exact lintegral_mono hpt
    _ = K * μ (s ∩ (ball x₀ R \ ball x₀ r)) :=
        lintegral_indicator_const₀
          (hs.inter (measurableSet_ball.diff measurableSet_ball).nullMeasurableSet) _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A radial cutoff `ψ` as above differs from one on `s ∩ closedBall x₀ r` and from zero off it
only in the shell `ball x₀ R \ closedBall x₀ r`, and by at most one there. -/
private theorem enorm_mul_indicator_sub_indicator_le (hψ01 : range ψ ⊆ Icc 0 1)
    (hψ1 : EqOn ψ 1 (closedBall x₀ r)) (hψR : support ψ ⊆ ball x₀ R) (x : E) :
    ‖(ψ * s.indicator (1 : E → ℝ)) x - (s ∩ closedBall x₀ r).indicator 1 x‖ₑ ≤
      (ball x₀ R \ closedBall x₀ r).indicator 1 x := by
  by_cases hxr : x ∈ closedBall x₀ r
  · by_cases hxs : x ∈ s <;> simp [hxr, hxs, hψ1 hxr]
  by_cases hxR : x ∈ ball x₀ R
  · rw [indicator_of_mem (mem_sdiff_of_mem hxR hxr),
      indicator_of_notMem fun (h : x ∈ s ∩ closedBall x₀ r) => hxr h.2, sub_zero, Pi.one_apply,
      Pi.mul_apply, ← ofReal_norm, ENNReal.ofReal_le_one, norm_mul]
    refine (mul_le_mul ?_ ?_ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · simpa [abs_of_nonneg (hψ01 (mem_range_self x)).1] using (hψ01 (mem_range_self x)).2
    · by_cases hxs : x ∈ s <;> simp [hxs]
  · simp [notMem_support.1 fun h => hxR (hψR h), hxR, hxr]

/-- The perimeter of `s ∩ closedBall x₀ r`, for a null-measurable `s` and `0 < r`, is at most
`P(s; U) + t * liminf_{h → 0⁺} μ(s ∩ (ball x₀ (r + h) \ ball x₀ r)) / h` for every `t > 1`. -/
private theorem perimeter_inter_closedBall_le_add_mul_liminf (hs : NullMeasurableSet s μ)
    (hr : 0 < r) {U : Opens E} (hU : closedBall x₀ r ⊆ U) {t : ℝ≥0} (ht : 1 < t) :
    perimeter μ ⊤ (s ∩ closedBall x₀ r) ≤ perimeter μ U s +
      t * liminf (fun h => μ (s ∩ (ball x₀ (r + h) \ ball x₀ r)) / ENNReal.ofReal h) (𝓝[>] 0) := by
  -- Cutoffs between `closedBall x₀ r` and `ball x₀ (r + h)` with Lipschitz constant `t / h`.
  have hex (h : ℝ) (hh : 0 < h) : ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
      EqOn ψ 1 (closedBall x₀ r) ∧ support ψ ⊆ ball x₀ (r + h) ∧
      LipschitzWith (t * h.toNNReal⁻¹) ψ := by
    refine exists_contDiff_cutoff_closedBall_lipschitzWith x₀ hr.le (by linarith) ?_
    rw [add_sub_cancel_left, NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hh.le]
    exact (lt_mul_iff_one_lt_left (inv_pos.2 hh)).2 (by exact_mod_cast ht)
  choose! ψ hψs hψ01 hψ1 hψR hψK using hex
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall x₀ r).exists_cthickening_subset_open U.isOpen hU
  rw [cthickening_closedBall hδ.le hr.le] at hδU
  have hshell (h : ℝ) : MeasurableSet (ball x₀ (r + h) \ closedBall x₀ r) :=
    measurableSet_ball.diff measurableSet_closedBall
  -- The shells `ball x₀ (r + h) \ closedBall x₀ r` decrease to the empty set.
  have hshell_lim : Tendsto (fun h => μ (ball x₀ (r + h) \ closedBall x₀ r)) (𝓝[>] 0) (𝓝 0) := by
    have hlim := tendsto_measure_biInter_gt (μ := μ) (a := (0 : ℝ))
      (s := fun h => ball x₀ (r + h) \ closedBall x₀ r) (fun h _ => (hshell h).nullMeasurableSet)
      (fun i j _ hij => sdiff_subset_sdiff_left (ball_subset_ball (by linarith)))
      ⟨1, one_pos, measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne⟩
    have hempty : ⋂ h > (0 : ℝ), ball x₀ (r + h) \ closedBall x₀ r = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      simp only [mem_iInter, Set.mem_sdiff, mem_ball, mem_closedBall] at hx
      exact (hx 1 one_pos).2 (le_of_forall_pos_lt_add fun h hh => (hx h hh).1)
    rwa [hempty, measure_empty] at hlim
  -- Lower semicontinuity of the total variation along `ψ h 1_s → 1_{s ∩ closedBall x₀ r}`.
  have hlsc : perimeter μ ⊤ (s ∩ closedBall x₀ r) ≤
      liminf (fun h => totalVariationOn μ ⊤ (ψ h * s.indicator 1)) (𝓝[>] 0) := by
    have h1 : LocallyIntegrable (1 : E → ℝ) μ := locallyIntegrable_const 1
    rw [perimeter_def]
    refine totalVariationOn_le_liminf ?_ ((h1.indicator₀
      (hs.inter measurableSet_closedBall.nullMeasurableSet)).locallyIntegrableOn _) fun K _ _ => ?_
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact ((h1.indicator₀ hs).continuous_mul (hψs h hh).continuous).locallyIntegrableOn _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hshell_lim
      (.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    calc ∫⁻ x in K, ‖(ψ h * s.indicator (1 : E → ℝ)) x - (s ∩ closedBall x₀ r).indicator 1 x‖ₑ ∂μ
        ≤ ∫⁻ x, (ball x₀ (r + h) \ closedBall x₀ r).indicator 1 x ∂μ :=
          (lintegral_mono fun x => enorm_mul_indicator_sub_indicator_le (hψ01 h hh) (hψ1 h hh)
            (hψR h hh) x).trans (setLIntegral_le_lintegral _ _)
      _ = μ (ball x₀ (r + h) \ closedBall x₀ r) := lintegral_indicator_one (hshell h)
  refine hlsc.trans ?_
  -- The Leibniz bound for each cutoff with `closedBall x₀ (r + h) ⊆ U`.
  have hbound : ∀ᶠ h in 𝓝[>] (0 : ℝ), totalVariationOn μ ⊤ (ψ h * s.indicator 1) ≤
      perimeter μ U s + t * (μ (s ∩ (ball x₀ (r + h) \ ball x₀ r)) / ENNReal.ofReal h) := by
    filter_upwards [Ioc_mem_nhdsGT hδ] with h hh
    refine (totalVariationOn_top_mul_indicator_le (hψs h hh.1) (hψ01 h hh.1) (hψ1 h hh.1)
      (hψR h hh.1) (hψK h hh.1)
      ((closedBall_subset_closedBall (show r + h ≤ δ + r by linarith [hh.2])).trans hδU)
      hs).trans_eq ?_
    rw [ENNReal.coe_mul, ENNReal.coe_inv (by simpa using hh.1), ENNReal.ofNNReal_toNNReal,
      ENNReal.div_eq_inv_mul, mul_assoc]
  refine (liminf_le_liminf hbound).trans_eq ?_
  -- `y ↦ P(s; U) + t * y` is monotone and continuous, so it commutes with `liminf`.
  exact ((Monotone.const_add (mul_right_mono) _).map_liminf_of_continuousAt _
    (continuous_const.add (ENNReal.continuous_const_mul ENNReal.coe_ne_top)).continuousAt).symm

/-- **Cutting by a ball, with a lower difference quotient.** For a null-measurable `s`, a ball
`ball x₀ r` and an open `U` containing `closedBall x₀ r`,

`P(s ∩ ball x₀ r) ≤ P(s; U) + liminf_{h → 0⁺} μ(s ∩ (ball x₀ (r + h) \ ball x₀ r)) / h`.

Neither finite perimeter nor finite measure of `s` is assumed. -/
theorem perimeter_inter_ball_le_add_liminf (hs : NullMeasurableSet s μ) {U : Opens E}
    (hU : closedBall x₀ r ⊆ U) :
    perimeter μ ⊤ (s ∩ ball x₀ r) ≤ perimeter μ U s +
      liminf (fun h => μ (s ∩ (ball x₀ (r + h) \ ball x₀ r)) / ENNReal.ofReal h) (𝓝[>] 0) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, inter_empty, perimeter_empty]
    exact zero_le
  -- The ball and the closed ball differ by a sphere, which is null.
  have hball : s ∩ ball x₀ r =ᵐ[μ.restrict (⊤ : Opens E)] s ∩ closedBall x₀ r := by
    rw [Opens.coe_top, Measure.restrict_univ]
    refine EventuallyEqSet.inter (by rfl) (ae_eq_set.2
      ⟨by rw [sdiff_eq_empty.2 ball_subset_closedBall, measure_empty],
      measure_mono_null (fun x hx => ?_) (Measure.addHaar_sphere_of_ne_zero μ x₀ hr.ne')⟩)
    exact mem_sphere.2 (le_antisymm (mem_closedBall.1 hx.1) (not_lt.1 hx.2))
  rw [perimeter_congr_ae hball]
  set L := liminf (fun h => μ (s ∩ (ball x₀ (r + h) \ ball x₀ r)) / ENNReal.ofReal h) (𝓝[>] 0)
  rcases eq_or_ne L (∞ : ℝ≥0∞) with hL | hL
  · simp [hL]
  -- Let the factor `t > 1` of the Lipschitz constants tend to one.
  have hlim : Tendsto (fun t : ℝ≥0 => perimeter μ U s + t * L) (𝓝[>] 1)
      (𝓝 (perimeter μ U s + L)) := by
    have h : Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) := by
      simpa using (ENNReal.continuous_coe.tendsto 1).mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.add (ENNReal.Tendsto.mul_const h (Or.inr hL))
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht =>
    perimeter_inter_closedBall_le_add_mul_liminf hs hr hU ht)

/-- **Cutting by a ball at a differentiability radius.** For a null-measurable `s` and an open `U`
containing `closedBall x₀ r`, if `m(ρ) = μ(s ∩ ball x₀ ρ)` has right derivative `D` at `r`, then
`P(s ∩ ball x₀ r) ≤ P(s; U) + D`. -/
theorem perimeter_inter_ball_le_add_of_hasDerivWithinAt (hs : NullMeasurableSet s μ)
    {U : Opens E} (hU : closedBall x₀ r ⊆ U) {D : ℝ}
    (hD : HasDerivWithinAt (fun ρ => μ.real (s ∩ ball x₀ ρ)) D (Ioi r) r) :
    perimeter μ ⊤ (s ∩ ball x₀ r) ≤ perimeter μ U s + ENNReal.ofReal D := by
  refine (perimeter_inter_ball_le_add_liminf hs hU).trans_eq ?_
  congr 1
  refine Tendsto.liminf_eq ?_
  -- The quotient is the slope of `m`, written in `ℝ≥0∞`.
  have hshift : Tendsto (fun h => r + h) (𝓝[>] 0) (𝓝[>] r) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun h (hh : 0 < h) =>
      lt_add_of_pos_right r hh⟩
    exact ((continuous_const.add continuous_id).tendsto' 0 r (add_zero r)).mono_left
      nhdsWithin_le_nhds
  have hslope := ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl r)).1 hD).comp hshift
  refine ((ENNReal.continuous_ofReal.tendsto D).comp hslope).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  have hsub : s ∩ ball x₀ r ⊆ s ∩ ball x₀ (r + h) :=
    inter_subset_inter_right _ (ball_subset_ball (by linarith))
  have hfin : μ (s ∩ ball x₀ (r + h)) ≠ (∞ : ℝ≥0∞) :=
    measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne
  rw [Function.comp_apply, Function.comp_apply, slope_def_field, add_sub_cancel_left,
    ENNReal.ofReal_div_of_pos hh, ENNReal.ofReal_sub _ measureReal_nonneg, ofReal_measureReal hfin,
    ofReal_measureReal (measure_ne_top_of_subset hsub hfin), inter_sdiff_distrib_left,
    measure_sdiff hsub (hs.inter measurableSet_ball.nullMeasurableSet)
      (measure_ne_top_of_subset hsub hfin)]

/-- **Cutting by a ball at almost every radius.** For a null-measurable `s` and almost every `r`,

`P(s ∩ ball x₀ r) ≤ P(s; ball x₀ r) + m'(r)`, where `m(ρ) = μ(s ∩ ball x₀ ρ)`.

This holds at every radius where `m` is differentiable and `ρ ↦ P(s; ball x₀ ρ)` is continuous;
both functions are monotone. -/
theorem ae_perimeter_inter_ball_le (hs : NullMeasurableSet s μ) (x₀ : E) :
    ∀ᵐ r, perimeter μ ⊤ (s ∩ ball x₀ r) ≤ perimeter μ ⟨ball x₀ r, isOpen_ball⟩ s +
      ENNReal.ofReal (deriv (fun ρ => μ.real (s ∩ ball x₀ ρ)) r) := by
  have hm : Monotone fun ρ => μ.real (s ∩ ball x₀ ρ) := fun ρ ρ' h =>
    measureReal_mono (inter_subset_inter_right _ (ball_subset_ball h))
      (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)
  have hF : Monotone fun ρ => perimeter μ ⟨ball x₀ ρ, isOpen_ball⟩ s := fun ρ ρ' h =>
    perimeter_mono fun x hx => ball_subset_ball h hx
  filter_upwards [hm.ae_differentiableAt, hF.countable_not_continuousAt.ae_notMem volume]
    with r hdiff hcont
  rw [not_not] at hcont
  -- Cut inside the slightly larger balls `ball x₀ (r + h)` and let `h → 0⁺`.
  have hshift : Tendsto (fun h : ℝ => r + h) (𝓝[>] 0) (𝓝 r) :=
    ((continuous_const.add continuous_id : Continuous fun h : ℝ => r + h).tendsto' 0 r
      (add_zero r)).mono_left nhdsWithin_le_nhds
  have hlim := (hcont.tendsto.comp hshift).add_const
    (ENNReal.ofReal (deriv (fun ρ => μ.real (s ∩ ball x₀ ρ)) r))
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun h (hh : 0 < h) =>
    perimeter_inter_ball_le_add_of_hasDerivWithinAt hs (U := ⟨ball x₀ (r + h), isOpen_ball⟩)
      (closedBall_subset_ball (lt_add_of_pos_right r hh)) hdiff.hasDerivAt.hasDerivWithinAt)

end TauCeti
