/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.CutByBall
public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The derivative of a set of finite perimeter on balls, and the upper density estimate

Let `Ω` be an open set of a finite-dimensional real inner product space `E` and `s` a set of
locally finite perimeter in `Ω`, with `Dχ_s = σ |Dχ_s|` the polar decomposition of the derivative
of its indicator (`TauCeti.polarDensity`, `TauCeti.variationMeasure`). Write
`m(ρ) = μ(s ∩ ball x ρ)`. Whenever `closedBall x r ⊆ Ω`, the vector `Dχ_s (closedBall x r)` is
bounded by the growth rate of `m`:

`‖∫_{closedBall x r} σ d|Dχ_s|‖ ≤ liminf_{h → 0⁺} μ(s ∩ (ball x (r + h) \ ball x r)) / h`

(`TauCeti.enorm_setIntegral_polarDensity_closedBall_le_liminf`), and hence by `m'(r)` at every
radius where `m` has a right derivative and at almost every radius
(`TauCeti.enorm_setIntegral_polarDensity_closedBall_le_of_hasDerivWithinAt`,
`TauCeti.ae_enorm_setIntegral_polarDensity_closedBall_le`). Classically, for Lebesgue measure,
`m'(r)` is the `(n - 1)`-dimensional measure of `s ∩ sphere x r` for almost every `r`, and the
estimate is the bound `|Dχ_s (B_r)| ≤ Hⁿ⁻¹(s ∩ ∂B_r)` coming from the Gauss–Green formula for
`s ∩ B_r`; that identification is not made here. The proof tests `Dχ_s` against `ψ v` for a unit
vector `v` and the smooth radial cutoffs `ψ` of
`TauCeti.exists_contDiff_cutoff_closedBall_lipschitzWith`, whose gradients live in thin shells, as
in the proof of `TauCeti.perimeter_inter_ball_le_add_liminf`.

At a point `x` of the reduced boundary `∂*s` the averages of `σ` over small closed balls are
nearly unit vectors, so `|Dχ_s| (closedBall x r) ≤ t ‖Dχ_s (closedBall x r)‖` for every `t > 1`
and every small `r` (`TauCeti.eventually_variationMeasure_closedBall_le_mul_enorm_setIntegral`).
Against an additive Haar measure the growth rate of `m` is at most that of `ρ ↦ μ (ball x ρ)`,
which gives the **upper density estimate**: for every `t > 1` and every small `r > 0`,

`|Dχ_s| (closedBall x r) ≤ t n μ(ball 0 1) r^(n - 1)`,     `n = dim E`

(`TauCeti.eventually_variationMeasure_closedBall_le`), and the same bound for the relative
perimeter `P(s; ball x r)` (`TauCeti.eventually_perimeter_ball_le`). This is one of the density
estimates at points of the reduced boundary behind De Giorgi's structure theorem. Neither finite
perimeter nor finite measure of `s` is assumed: the estimates at every radius and at the reduced
boundary only use that `s` has locally finite perimeter in `Ω`, and the forms with `m'(r)` also
use that `s` is null-measurable.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 15 (the
  density estimates at points of the reduced boundary).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7 (the density estimates at points of the reduced boundary).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric Function TestFunction LineDeriv Module
open scoped ENNReal NNReal Topology RealInnerProductSpace Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E} {x : E} {r : ℝ}

/-- Testing `Dχ_s` against `ψ v`, for a unit vector `v` and a smooth cutoff `ψ` which is one on
`closedBall x r`, vanishes off `ball x R` and is `K`-Lipschitz, gives at most `K` times the measure
of `s` in the shell `ball x R \ ball x r`. -/
private theorem ofReal_abs_integral_mul_inner_polarDensity_le
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ01 : range ψ ⊆ Icc 0 1)
    (hψ1 : EqOn ψ 1 (closedBall x r)) {R : ℝ} (hψR : support ψ ⊆ ball x R)
    (hRΩ : closedBall x R ⊆ Ω) {K : ℝ≥0} (hψK : LipschitzWith K ψ) {v : E} (hv : ‖v‖ ≤ 1) :
    ENNReal.ofReal |∫ y, ψ y * ⟪v, polarDensity μ Ω (s.indicator 1) y⟫
        ∂variationMeasure μ Ω (s.indicator 1)| ≤ K * μ (s ∩ (ball x R \ ball x r)) := by
  have htsupp : tsupport ψ ⊆ closedBall x R :=
    (closure_mono hψR).trans closure_ball_subset_closedBall
  let φ : 𝓓(Ω, ℝ) := ⟨ψ, hψ, (isCompact_closedBall x R).of_isClosed_subset (isClosed_tsupport ψ)
    htsupp, htsupp.trans hRΩ⟩
  have h := integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hu hfin
    (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) φ)
  have hφ : (φ : E → ℝ) = ψ := rfl
  simp only [divergenceCLM_postcompCLM_toSpanSingleton, postcompCLM_apply, comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, hφ, real_inner_smul_left] at h
  rw [← abs_neg, ← h, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans <|
    (lintegral_mono fun y => ?_).trans (lintegral_indicator_const_le _ _)
  -- The derivative of `ψ` vanishes off the shell, and is at most `K` in the shell.
  have hd : ∂_{v} φ y = fderiv ℝ ψ y v := by
    rw [lineDerivOp_apply]
    exact (hψ.differentiable (by simp) y).lineDeriv_eq_fderiv
  rw [hd]
  by_cases hys : y ∈ s
  swap
  · simp [hys]
  by_cases hyA : y ∈ ball x R \ ball x r
  · rw [indicator_of_mem (mem_inter hys hyA), indicator_of_mem hys, Pi.one_apply, mul_one,
      ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal (((fderiv ℝ ψ y).le_opNorm v).trans ?_)
    exact (mul_le_of_le_one_right (norm_nonneg _) hv).trans (norm_fderiv_le_of_lipschitz ℝ hψK)
  simp [notMem_support.1 fun h => hyA (support_fderiv_subset_ball_sdiff_ball hψ01 hψ1 hψR h)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Pairings of a function `g` on `Ω` with cutoffs `ψ h`, equal to one on `closedBall x r` and
vanishing off `ball x (r + h)`, converge to the integral of `g` over `closedBall x r` as
`h → 0⁺`, provided `g` is integrable on a slightly larger closed ball. -/
private theorem tendsto_integral_mul_of_cutoff {ν : Measure Ω} {g : Ω → ℝ} (hg : Measurable g)
    {δ : ℝ} (hδ : 0 < δ) (hint : IntegrableOn g (((↑) : Ω → E) ⁻¹' closedBall x (r + δ)) ν)
    {ψ : ℝ → E → ℝ} (hψc : ∀ h, 0 < h → Continuous (ψ h))
    (hψ01 : ∀ h, 0 < h → range (ψ h) ⊆ Icc 0 1) (hψ1 : ∀ h, 0 < h → EqOn (ψ h) 1 (closedBall x r))
    (hψR : ∀ h, 0 < h → support (ψ h) ⊆ ball x (r + h)) :
    Tendsto (fun h => ∫ y, ψ h y * g y ∂ν) (𝓝[>] 0)
      (𝓝 (∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r, g y ∂ν)) := by
  have hψ0 (h : ℝ) (hh : 0 < h) (y : E) (hy : y ∉ ball x (r + h)) : ψ h y = 0 :=
    notMem_support.1 fun h' => hy (hψR h hh h')
  rw [← integral_indicator (measurableSet_closedBall.preimage measurable_subtype_coe)]
  refine tendsto_integral_filter_of_dominated_convergence
    ((((↑) : Ω → E) ⁻¹' closedBall x (r + δ)).indicator fun y => ‖g y‖) ?_ ?_
    (IntegrableOn.integrable_indicator hint.norm
      (measurableSet_closedBall.preimage measurable_subtype_coe)) ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact (((hψc h hh).measurable.comp measurable_subtype_coe).mul hg).aestronglyMeasurable
  -- The cutoffs take values in `[0, 1]` and vanish off `closedBall x (r + δ)` once `h ≤ δ`.
  · filter_upwards [Ioc_mem_nhdsGT hδ] with h hh
    refine .of_forall fun y => ?_
    by_cases hy : (y : E) ∈ closedBall x (r + δ)
    · rw [indicator_of_mem (show y ∈ ((↑) : Ω → E) ⁻¹' closedBall x (r + δ) from hy), norm_mul,
        Real.norm_of_nonneg (hψ01 h hh.1 (mem_range_self _)).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hψ01 h hh.1 (mem_range_self _)).2
    · rw [indicator_of_notMem (show y ∉ ((↑) : Ω → E) ⁻¹' closedBall x (r + δ) from hy),
        hψ0 h hh.1 y fun h' => hy (ball_subset_closedBall
          (ball_subset_ball (by linarith [hh.2]) h')), zero_mul, norm_zero]
  -- Pointwise, the cutoffs tend to the indicator of `closedBall x r`.
  · refine .of_forall fun y => ?_
    by_cases hy : (y : E) ∈ closedBall x r
    · rw [indicator_of_mem (show y ∈ ((↑) : Ω → E) ⁻¹' closedBall x r from hy)]
      refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun h hh => ?_)
      simp only [hψ1 h hh hy, Pi.one_apply, one_mul]
    · rw [indicator_of_notMem (show y ∉ ((↑) : Ω → E) ⁻¹' closedBall x r from hy)]
      have hd : r < dist (y : E) x := not_le.1 hy
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hd)] with h hh
      simp only [hψ0 h hh.1 y fun h' => (mem_ball.1 h').not_ge (by linarith [hh.2]), zero_mul]

/-- **The derivative of a set on a closed ball, at every radius.** For a set `s` of locally
finite perimeter in `Ω` and `closedBall x r ⊆ Ω`,

`‖Dχ_s (closedBall x r)‖ ≤ liminf_{h → 0⁺} μ(s ∩ (ball x (r + h) \ ball x r)) / h`,

where `Dχ_s (closedBall x r) = ∫_{closedBall x r} σ d|Dχ_s|`. -/
theorem enorm_setIntegral_polarDensity_closedBall_le_liminf
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hΩ : closedBall x r ⊆ Ω) :
    ‖∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r, polarDensity μ Ω (s.indicator 1) y
        ∂variationMeasure μ Ω (s.indicator 1)‖ₑ ≤
      liminf (fun h => μ (s ∩ (ball x (r + h) \ ball x r)) / ENNReal.ofReal h) (𝓝[>] 0) := by
  rcases lt_or_ge r 0 with hr | hr
  · simp [closedBall_eq_empty.2 hr]
  set ν := variationMeasure μ Ω (s.indicator 1)
  set σ := polarDensity μ Ω (s.indicator 1)
  set w := ∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r, σ y ∂ν
  set L := liminf (fun h => μ (s ∩ (ball x (r + h) \ ball x r)) / ENNReal.ofReal h) (𝓝[>] 0)
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_closedBall x r).exists_cthickening_subset_open Ω.isOpen hΩ
  rw [cthickening_closedBall hδ.le hr] at hδΩ
  -- `σ` is integrable on the compact sets `closedBall x ρ ⊆ Ω`.
  have hint (ρ : ℝ) (hρ : closedBall x ρ ⊆ Ω) :
      IntegrableOn σ (((↑) : Ω → E) ⁻¹' closedBall x ρ) ν :=
    (locallyIntegrable_polarDensity hu hfin).integrableOn_isCompact
      (Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall x ρ)
        (by rwa [Subtype.range_coe]))
  -- The key estimate `|⟪v, w⟫| ≤ t L` for `‖v‖ ≤ 1` and `t > 1`.
  have key (v : E) (hv : ‖v‖ ≤ 1) (t : ℝ≥0) (ht : 1 < t) :
      ENNReal.ofReal |⟪v, w⟫| ≤ t * L := by
    -- Cutoffs between `closedBall x r` and `ball x (r + h)` with Lipschitz constant `t / h`.
    have hex (h : ℝ) (hh : 0 < h) : ∃ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ range ψ ⊆ Icc 0 1 ∧
        EqOn ψ 1 (closedBall x r) ∧ support ψ ⊆ ball x (r + h) ∧
        LipschitzWith (t * h.toNNReal⁻¹) ψ := by
      refine exists_contDiff_cutoff_closedBall_lipschitzWith x hr (by linarith) ?_
      rw [add_sub_cancel_left, NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hh.le]
      exact (lt_mul_iff_one_lt_left (inv_pos.2 hh)).2 (by exact_mod_cast ht)
    choose! ψ hψs hψ01 hψ1 hψR hψK using hex
    -- The pairings with the cutoffs converge to `⟪v, w⟫`.
    have hlim : Tendsto (fun h => ∫ y, ψ h y * ⟪v, σ y⟫ ∂ν) (𝓝[>] 0) (𝓝 ⟪v, w⟫) := by
      rw [← integral_inner (hint r hΩ) v]
      exact tendsto_integral_mul_of_cutoff (Measurable.const_inner measurable_polarDensity) hδ
        ((hint (r + δ) (by rwa [add_comm])).const_inner v) (fun h hh => (hψs h hh).continuous)
        hψ01 hψ1 hψR
    -- Each pairing is bounded by `t` times the difference quotient.
    have hbound : ∀ᶠ h in 𝓝[>] (0 : ℝ), ENNReal.ofReal |∫ y, ψ h y * ⟪v, σ y⟫ ∂ν| ≤
        t * (μ (s ∩ (ball x (r + h) \ ball x r)) / ENNReal.ofReal h) := by
      filter_upwards [Ioc_mem_nhdsGT hδ] with h hh
      refine (ofReal_abs_integral_mul_inner_polarDensity_le hu hfin (hψs h hh.1) (hψ01 h hh.1)
        (hψ1 h hh.1) (hψR h hh.1)
        ((closedBall_subset_closedBall (show r + h ≤ r + δ by linarith [hh.2])).trans
          (by rwa [add_comm])) (hψK h hh.1) hv).trans_eq ?_
      rw [ENNReal.coe_mul, ENNReal.coe_inv (by simpa using hh.1), ENNReal.ofNNReal_toNNReal,
        ENNReal.div_eq_inv_mul, mul_assoc]
    have hT : Tendsto (fun h => ENNReal.ofReal |∫ y, ψ h y * ⟪v, σ y⟫ ∂ν|) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal |⟪v, w⟫|)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp hlim)
    rw [← hT.liminf_eq, ← ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top]
    exact liminf_le_liminf hbound
  -- Let `t → 1`, and test against `v = w / ‖w‖`.
  have key' (v : E) (hv : ‖v‖ ≤ 1) : ENNReal.ofReal |⟪v, w⟫| ≤ L := by
    rcases eq_or_ne L ∞ with hL | hL
    · simp [hL]
    have h : Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) := by
      simpa using (ENNReal.continuous_coe.tendsto 1).mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞) * L) (𝓝[>] 1) (𝓝 L) := by
      simpa using ENNReal.Tendsto.mul_const h (Or.inr hL)
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht => key v hv t ht)
  rcases eq_or_ne w 0 with hw | hw
  · rw [hw, enorm_zero]
    exact zero_le
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h := key' (‖w‖⁻¹ • w) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw'.ne'])
  rwa [real_inner_smul_left, real_inner_self_eq_norm_sq, sq, ← mul_assoc,
    inv_mul_cancel₀ hw'.ne', one_mul, abs_norm, ofReal_norm] at h

/-- **The derivative of a set on a closed ball, at a differentiability radius.** For a
null-measurable set `s` of locally finite perimeter in `Ω` and `closedBall x r ⊆ Ω`, if
`m(ρ) = μ(s ∩ ball x ρ)` has right derivative `D` at `r`, then `‖Dχ_s (closedBall x r)‖ ≤ D`. -/
theorem enorm_setIntegral_polarDensity_closedBall_le_of_hasDerivWithinAt [μ.IsAddHaarMeasure]
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hs : NullMeasurableSet s μ) (hΩ : closedBall x r ⊆ Ω) {D : ℝ}
    (hD : HasDerivWithinAt (fun ρ => μ.real (s ∩ ball x ρ)) D (Ioi r) r) :
    ‖∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r, polarDensity μ Ω (s.indicator 1) y
        ∂variationMeasure μ Ω (s.indicator 1)‖ₑ ≤ ENNReal.ofReal D := by
  rw [← (tendsto_measure_inter_ball_sdiff_ball_div_of_hasDerivWithinAt hs hD).liminf_eq]
  exact enorm_setIntegral_polarDensity_closedBall_le_liminf hu hfin hΩ

/-- **The derivative of a set on a closed ball, at almost every radius.** For a null-measurable
set `s` of locally finite perimeter in `Ω` and almost every `r` with `closedBall x r ⊆ Ω`,
`‖Dχ_s (closedBall x r)‖ ≤ m'(r)`, where `m(ρ) = μ(s ∩ ball x ρ)`. -/
theorem ae_enorm_setIntegral_polarDensity_closedBall_le [μ.IsAddHaarMeasure]
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hs : NullMeasurableSet s μ) (x : E) :
    ∀ᵐ r, closedBall x r ⊆ Ω →
      ‖∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r, polarDensity μ Ω (s.indicator 1) y
          ∂variationMeasure μ Ω (s.indicator 1)‖ₑ ≤
        ENNReal.ofReal (deriv (fun ρ => μ.real (s ∩ ball x ρ)) r) := by
  have hm : Monotone fun ρ => μ.real (s ∩ ball x ρ) := fun ρ ρ' h =>
    measureReal_mono (inter_subset_inter_right _ (ball_subset_ball h))
      (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)
  filter_upwards [hm.ae_differentiableAt] with r hdiff hΩ
  exact enorm_setIntegral_polarDensity_closedBall_le_of_hasDerivWithinAt hu hfin hs hΩ
    hdiff.hasDerivAt.hasDerivWithinAt

/-- At a point `x` of the reduced boundary, for every `t > 1` and every small `r`, the perimeter
measure of `closedBall x r` is at most `t ‖Dχ_s (closedBall x r)‖`. -/
theorem eventually_variationMeasure_closedBall_le_mul_enorm_setIntegral
    (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0} (ht : 1 < t) :
    ∀ᶠ r in 𝓝[>] 0, variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) ≤
      t * ‖∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r, polarDensity μ Ω (s.indicator 1) y
        ∂variationMeasure μ Ω (s.indicator 1)‖ₑ := by
  set ν := variationMeasure μ Ω (s.indicator 1)
  obtain ⟨ε, hε, hεΩ⟩ :=
    nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  -- The averages tend to the unit vector `-ν_s x`, so their norms eventually exceed `t⁻¹`.
  have havg : ∀ᶠ r in 𝓝[>] (0 : ℝ), (t : ℝ)⁻¹ < ‖⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
      polarDensity μ Ω (s.indicator 1) y ∂ν‖ := by
    refine (tendsto_setAverage_polarDensity hx).norm.eventually_const_lt ?_
    rw [norm_neg, norm_outerNormal hx]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast ht)
  filter_upwards [havg, Ioc_mem_nhdsGT hε] with r hr hrε
  set S := ((↑) : Ω → E) ⁻¹' closedBall x r
  have hS : IsCompact S := Topology.IsInducing.subtypeVal.isCompact_preimage'
    (isCompact_closedBall x r) (by
      rw [Subtype.range_coe]
      exact (closedBall_subset_closedBall hrε.2).trans hεΩ)
  have hS0 : ν.real S ≠ 0 := by
    rw [measureReal_ne_zero_iff hS.measure_lt_top.ne]
    exact variationMeasure_preimage_closedBall_ne_zero hx hrε.1
  rw [setAverage_eq, norm_smul, norm_inv, Real.norm_of_nonneg measureReal_nonneg,
    lt_inv_mul_iff₀ (lt_of_le_of_ne measureReal_nonneg hS0.symm)] at hr
  rw [← ofReal_measureReal hS.measure_lt_top.ne, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul NNReal.zero_le_coe]
  refine ENNReal.ofReal_le_ofReal ?_
  have ht0 : (0 : ℝ) < t := zero_lt_one.trans (by exact_mod_cast ht)
  exact ((mul_inv_lt_iff₀ ht0).1 hr).le.trans_eq (mul_comm _ _)

/-- **The upper density estimate at the reduced boundary.** Against an additive Haar measure, at a
point `x` of the reduced boundary of `s` in `Ω`, for every `t > 1` and every small `r > 0`,

`|Dχ_s| (closedBall x r) ≤ t n μ(ball 0 1) r^(n - 1)`,    `n = dim E`. -/
theorem eventually_variationMeasure_closedBall_le [μ.IsAddHaarMeasure]
    (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0} (ht : 1 < t) :
    ∀ᶠ r in 𝓝[>] 0, variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) ≤
      t * ENNReal.ofReal (finrank ℝ E * r ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  obtain ⟨ε, hε, hεΩ⟩ :=
    nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [eventually_variationMeasure_closedBall_le_mul_enorm_setIntegral hx ht,
    Ioc_mem_nhdsGT hε] with r hr hrε
  refine hr.trans (mul_le_mul_right ((enorm_setIntegral_polarDensity_closedBall_le_liminf hu hfin
    ((closedBall_subset_closedBall hrε.2).trans hεΩ)).trans ?_) _)
  -- The growth rate of the measure of `s` in the balls is at most that of the balls.
  have hD : HasDerivWithinAt (fun ρ => μ.real (univ ∩ ball x ρ))
      (finrank ℝ E * r ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) (Ioi r) r := by
    simpa only [univ_inter] using (Measure.hasDerivAt_measureReal_ball μ x hrε.1).hasDerivWithinAt
  rw [← (tendsto_measure_inter_ball_sdiff_ball_div_of_hasDerivWithinAt nullMeasurableSet_univ
    hD).liminf_eq]
  exact liminf_le_liminf (.of_forall fun h => by gcongr; exact subset_univ s)

/-- **The upper density estimate for the relative perimeter.** Against an additive Haar measure,
at a point `x` of the reduced boundary of `s` in `Ω`, for every `t > 1` and every small `r > 0`,

`P(s; ball x r) ≤ t n μ(ball 0 1) r^(n - 1)`,    `n = dim E`. -/
theorem eventually_perimeter_ball_le [μ.IsAddHaarMeasure] (hx : x ∈ reducedBoundary μ Ω s)
    {t : ℝ≥0} (ht : 1 < t) :
    ∀ᶠ r in 𝓝[>] 0, perimeter μ ⟨ball x r, isOpen_ball⟩ s ≤
      t * ENNReal.ofReal (finrank ℝ E * r ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  obtain ⟨ε, hε, hεΩ⟩ :=
    nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [eventually_variationMeasure_closedBall_le hx ht, Ioc_mem_nhdsGT hε]
    with r hr hrε
  have hball : ball x r ⊆ closedBall x r := ball_subset_closedBall
  rw [perimeter_def, ← variationMeasure_preimage_coe hu hfin
    (U := ⟨ball x r, isOpen_ball⟩)
    fun y hy => hεΩ (closedBall_subset_closedBall hrε.2 (hball hy))]
  exact (measure_mono (preimage_mono hball)).trans hr

end TauCeti
