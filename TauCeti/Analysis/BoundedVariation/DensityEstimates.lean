/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.CutByBall
public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import TauCeti.Analysis.BoundedVariation.RelativeIsoperimetric
import TauCeti.Analysis.BoundedVariation.Sobolev
import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
import TauCeti.Analysis.Calculus.PowerGrowth
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.Topology.Instances.ENNReal

/-!
# The derivative of a set of finite perimeter on balls, and the density estimates

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
perimeter `P(s; ball x r)` (`TauCeti.eventually_perimeter_ball_le`).

In dimension `n ≥ 2` there are matching **lower density estimates**. Let `p = n / (n - 1)` and let
`C` be the constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the Sobolev inequality.
At a point `x` of `∂*s`, for every small `r > 0`,

`(r / (3 n C)) ^ n ≤ μ(s ∩ ball x r)`,   `(r / (3 n C)) ^ n ≤ μ(ball x r \ s)`

(`TauCeti.eventually_le_measure_inter_ball`, `TauCeti.eventually_le_measure_ball_sdiff`), and
the relative isoperimetric inequality turns these into the lower bound
`(r / (3 n C)) ^ (n - 1) ≤ 2 ^ (n + 1) μ(ball 0 1) ^ (-1/n) P(s; ball x r)`
(`TauCeti.eventually_le_perimeter_ball`). For the first, cutting `s` by `ball x r` costs at most
`m'(r)` in perimeter (`TauCeti.ae_perimeter_inter_ball_le`), and the perimeter of `s` inside the
ball is at most `2 m'(r)` by the estimate above, so the Sobolev inequality for `s ∩ ball x r`
(`TauCeti.measure_rpow_le_perimeter`) gives the differential inequality
`m ^ (1 - 1/n) ≤ 3 C m'` at almost every small radius. Since `m` is monotone and positive on
`(0, r)` (`TauCeti.measure_inter_ball_ne_zero`), it integrates to `r / n ≤ 3 C m(r) ^ (1/n)`
(`TauCeti.mul_sub_le_mul_rpow_sub_rpow_of_rpow_le_mul_deriv`). The second follows by applying the
first to the complement, which has the same reduced boundary.

These are the density estimates at points of the reduced boundary behind De Giorgi's structure
theorem: the volume of `s` and of its complement and the perimeter of `s` in `ball x r` are all
comparable to the corresponding powers of `r`. Neither finite perimeter nor finite measure of `s`
is assumed: the estimates at every radius and at the reduced boundary only use that `s` has
locally finite perimeter in `Ω`, and the forms with `m'(r)` also use that `s` is null-measurable
and that `μ` is finite on compact sets. The lower density estimates need no measurability
hypothesis, since a point of the reduced boundary forces `s` to be null-measurable in `Ω`. Only
the upper and lower density estimates use that `μ` is an additive Haar measure.

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
  have hφ : (φ : E → ℝ) = ψ := coe_mk
  simp only [divergenceCLM_postcompCLM_toSpanSingleton, postcompCLM_apply, comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, hφ, real_inner_smul_left] at h
  rw [← abs_neg, ← h, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans <|
    (lintegral_mono fun y => ?_).trans (lintegral_indicator_const_le _ _)
  have hd : ∂_{v} φ y = fderiv ℝ ψ y v := by
    rw [lineDerivOp_apply]
    exact (hψ.differentiable (by simp) y).lineDeriv_eq_fderiv
  rw [hd, enorm_mul]
  refine le_trans ?_ (enorm_fderiv_mul_indicator_le_indicator hψ01 hψ1 hψR hψK s y)
  gcongr
  exact (fderiv ℝ ψ y).le_opENorm_of_le (by simpa [← ofReal_norm] using hv) |>.trans_eq (mul_one _)

/-- Testing `Dχ_s (closedBall x r)` against a vector `v` with `‖v‖ ≤ 1` gives at most `t` times
the lower difference quotient of `m(ρ) = μ(s ∩ ball x ρ)` at `r`, for every `t > 1`. -/
private theorem ofReal_abs_inner_setIntegral_polarDensity_le_mul_liminf
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hr : 0 ≤ r) (hΩ : closedBall x r ⊆ Ω) {v : E} (hv : ‖v‖ ≤ 1) {t : ℝ≥0} (ht : 1 < t) :
    ENNReal.ofReal |⟪v, ∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        polarDensity μ Ω (s.indicator 1) y ∂variationMeasure μ Ω (s.indicator 1)⟫| ≤
      t * liminf (fun h => μ (s ∩ (ball x (r + h) \ ball x r)) / ENNReal.ofReal h) (𝓝[>] 0) := by
  set ν := variationMeasure μ Ω (s.indicator 1)
  set σ := polarDensity μ Ω (s.indicator 1)
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_closedBall x r).exists_cthickening_subset_open Ω.isOpen hΩ
  rw [cthickening_closedBall hδ.le hr] at hδΩ
  -- `σ` is integrable on the compact sets `closedBall x ρ ⊆ Ω`.
  have hint (ρ : ℝ) (hρ : closedBall x ρ ⊆ Ω) :
      IntegrableOn σ (((↑) : Ω → E) ⁻¹' closedBall x ρ) ν :=
    (locallyIntegrable_polarDensity hu hfin).integrableOn_isCompact
      (Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall x ρ)
        (by rwa [Subtype.range_coe]))
  -- Cutoffs between `closedBall x r` and `ball x (r + h)` with Lipschitz constant `t / h`.
  choose! ψ hψs hψ01 hψ1 hψR hψK using fun h (hh : 0 < h) =>
    exists_contDiff_cutoff_closedBall_lipschitzWith_mul_inv x hr hh ht
  -- The pairings with the cutoffs converge to `⟪v, Dχ_s (closedBall x r)⟫`.
  have hlim : Tendsto (fun h => ∫ y, ψ h y * ⟪v, σ y⟫ ∂ν) (𝓝[>] 0)
      (𝓝 ⟪v, ∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r, σ y ∂ν⟫) := by
    rw [← integral_inner (hint r hΩ) v]
    simpa only [smul_eq_mul] using tendsto_integral_smul_of_cutoff (g := fun y => ⟪v, σ y⟫)
      measurable_subtype_coe (measurable_polarDensity.const_inner.aestronglyMeasurable) hδ
      ((hint (r + δ) (by rwa [add_comm])).const_inner v)
      (fun h hh => (hψs h hh).continuous.measurable) hψ01 hψ1 hψR
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
  rw [← (((ENNReal.continuous_ofReal.tendsto _).comp
      ((continuous_abs.tendsto _).comp hlim))).liminf_eq,
    ← ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top]
  exact liminf_le_liminf hbound

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
  set w := ∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r, polarDensity μ Ω (s.indicator 1) y
    ∂variationMeasure μ Ω (s.indicator 1)
  -- Let `t → 1`, and test against `v = w / ‖w‖`.
  have key (v : E) (hv : ‖v‖ ≤ 1) : ENNReal.ofReal |⟪v, w⟫| ≤
      liminf (fun h => μ (s ∩ (ball x (r + h) \ ball x r)) / ENNReal.ofReal h) (𝓝[>] 0) := by
    simpa using ENNReal.le_add_of_forall_one_lt_le_add_mul (b := 0) fun t ht => by
      simpa using ofReal_abs_inner_setIntegral_polarDensity_le_mul_liminf hu hfin hr hΩ hv ht
  rcases eq_or_ne w 0 with hw | hw
  · rw [hw, enorm_zero]
    exact zero_le
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h := key (‖w‖⁻¹ • w) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw'.ne'])
  have hinner : ⟪‖w‖⁻¹ • w, w⟫ = ‖w‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  rwa [hinner, abs_norm, ofReal_norm] at h

/-- **The derivative of a set on a closed ball, at a differentiability radius.** For a measure `μ`
finite on compact sets, a null-measurable set `s` of locally finite perimeter in `Ω` and
`closedBall x r ⊆ Ω`, if `m(ρ) = μ(s ∩ ball x ρ)` has right derivative `D` at `r`, then
`‖Dχ_s (closedBall x r)‖ ≤ D`. -/
theorem enorm_setIntegral_polarDensity_closedBall_le_of_hasDerivWithinAt
    [IsFiniteMeasureOnCompacts μ]
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hs : NullMeasurableSet s μ) (hΩ : closedBall x r ⊆ Ω) {D : ℝ}
    (hD : HasDerivWithinAt (fun ρ => μ.real (s ∩ ball x ρ)) D (Ioi r) r) :
    ‖∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r, polarDensity μ Ω (s.indicator 1) y
        ∂variationMeasure μ Ω (s.indicator 1)‖ₑ ≤ ENNReal.ofReal D := by
  rw [← (tendsto_measure_inter_ball_sdiff_ball_div_of_hasDerivWithinAt hs hD).liminf_eq]
  exact enorm_setIntegral_polarDensity_closedBall_le_liminf hu hfin hΩ

/-- **The derivative of a set on a closed ball, at almost every radius.** For a measure `μ` finite
on compact sets, a null-measurable set `s` of locally finite perimeter in `Ω` and almost every `r`
with `closedBall x r ⊆ Ω`,
`‖Dχ_s (closedBall x r)‖ ≤ m'(r)`, where `m(ρ) = μ(s ∩ ball x ρ)`. -/
theorem ae_enorm_setIntegral_polarDensity_closedBall_le [IsFiniteMeasureOnCompacts μ]
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hs : NullMeasurableSet s μ) (x : E) :
    ∀ᵐ r, closedBall x r ⊆ Ω →
      ‖∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r, polarDensity μ Ω (s.indicator 1) y
          ∂variationMeasure μ Ω (s.indicator 1)‖ₑ ≤
        ENNReal.ofReal (deriv (fun ρ => μ.real (s ∩ ball x ρ)) r) := by
  filter_upwards [(monotone_measureReal_inter_ball μ s x).ae_differentiableAt] with r hdiff hΩ
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

/-! ### The lower density estimates -/

section LowerDensity

variable [μ.IsAddHaarMeasure] {p : ℝ≥0}

/-- At a point `x` of the reduced boundary of a null-measurable set `s`, the measure
`m(ρ) = μ(s ∩ ball x ρ)` satisfies `m ^ (1/p) ≤ 3 C m'` at almost every small radius, where
`1/p = 1 - 1/n` and `C` is the constant of the Sobolev inequality. Cutting `s` by `ball x r` costs
at most `m'(r)` in perimeter, and the perimeter of `s` in `ball x r` is at most `2 m'(r)` by the
estimate at the reduced boundary. -/
private theorem exists_ae_measureReal_inter_ball_rpow_le_mul_deriv (hs : NullMeasurableSet s μ)
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (hx : x ∈ reducedBoundary μ Ω s) :
    ∃ δ > 0, ∀ᵐ r, r ∈ Ioo 0 δ → μ.real (s ∩ ball x r) ^ (p : ℝ)⁻¹ ≤
      3 * eLpNormLESNormFDerivOneConst μ p * deriv (fun ρ => μ.real (s ∩ ball x ρ)) r := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  obtain ⟨ε, hε, hεΩ⟩ :=
    nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  obtain ⟨δ, hδ, hδε⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    ((eventually_variationMeasure_closedBall_le_mul_enorm_setIntegral hx (t := 2)
      one_lt_two).and (Ioc_mem_nhdsGT hε))
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [ae_perimeter_inter_ball_le hs x,
    ae_enorm_setIntegral_polarDensity_closedBall_le hu hfin hs x] with r hcut hD hr
  obtain ⟨hvar, hrε⟩ := hδε hr
  have hΩr : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hrε.2).trans hεΩ
  set D := deriv (fun ρ => μ.real (s ∩ ball x ρ)) r
  set C := eLpNormLESNormFDerivOneConst μ p
  have hD0 : 0 ≤ D := (monotone_measureReal_inter_ball μ s x).deriv_nonneg
  have hm : μ (s ∩ ball x r) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne
  -- The perimeter of `s` in `ball x r` is at most `2 m'(r)`.
  have hP : perimeter μ ⟨ball x r, isOpen_ball⟩ s ≤ 2 * ENNReal.ofReal D := by
    rw [perimeter_def, ← variationMeasure_preimage_coe hu hfin (U := ⟨ball x r, isOpen_ball⟩)
      (ball_subset_closedBall.trans hΩr)]
    exact (measure_mono (preimage_mono ball_subset_closedBall)).trans
      (hvar.trans (mul_le_mul_right (hD hΩr) _))
  -- The Sobolev inequality for `s ∩ ball x r`, after cutting `s` by the ball.
  have h := (measure_rpow_le_perimeter (hs.inter measurableSet_ball.nullMeasurableSet) hm hp).trans
    (mul_le_mul_right (hcut.trans (add_le_add_left hP _)) _)
  rw [← ofReal_measureReal hm, ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg (by positivity),
    show (C : ℝ≥0∞) * (2 * ENNReal.ofReal D + ENNReal.ofReal D) = ENNReal.ofReal (3 * C * D) by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
      ring,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h

/-- **The lower volume density estimate at the reduced boundary.** Let `E` have dimension `n ≥ 2`,
let `p = n / (n - 1)` and let `C` be the constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p`
of the Sobolev inequality. At a point `x` of the reduced boundary of `s` in `Ω`, for every small
`r > 0`,

`(r / (3 n C)) ^ n ≤ μ(s ∩ ball x r)`. -/
theorem eventually_le_measure_inter_ball (hp : NNReal.HolderConjugate (finrank ℝ E) p)
    (hx : x ∈ reducedBoundary μ Ω s) :
    ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal ((r / (3 * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p)) ^
      finrank ℝ E) ≤ μ (s ∩ ball x r) := by
  set n := finrank ℝ E
  set C := eLpNormLESNormFDerivOneConst μ p
  have hn : (1 : ℝ) < n := by exact_mod_cast hp.lt
  have hn' : (0 : ℝ) < n := zero_lt_one.trans hn
  have hn0 : n ≠ 0 := Nat.cast_ne_zero.1 hn'.ne'
  -- Replace `s` by the null-measurable set `t = s ∩ Ω`, which agrees with `s` on `Ω`.
  set t := s ∩ (Ω : Set E)
  have ht : NullMeasurableSet t μ :=
    (nullMeasurableSet_restrict Ω.isOpen.measurableSet.nullMeasurableSet).1
      (nullMeasurableSet_restrict_of_mem_reducedBoundary hx)
  have hst : s =ᵐ[μ.restrict Ω] t := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
    simp [t, hy]
  have hxt : x ∈ reducedBoundary μ Ω t := by rwa [← reducedBoundary_congr_ae hst]
  obtain ⟨δ, hδ, hδm⟩ := exists_ae_measureReal_inter_ball_rpow_le_mul_deriv ht hp hxt
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hε)] with r hr
  have hts : t ∩ ball x r = s ∩ ball x r := by
    rw [inter_right_comm, inter_eq_left]
    exact inter_subset_right.trans ((ball_subset_ball (hr.2.le.trans (min_le_right _ _))).trans hεΩ)
  set m := fun ρ => μ.real (t ∩ ball x ρ)
  -- The differential inequality `m ^ (1 - 1/n) ≤ 3 C m'` integrates to `r / n ≤ 3 C m(r) ^ (1/n)`.
  have hgrowth := mul_sub_le_mul_rpow_sub_rpow_of_rpow_le_mul_deriv (f := m) (β := (n : ℝ)⁻¹)
    (K := 3 * C) hr.1.le
    ((monotone_measureReal_inter_ball μ t x).monotoneOn _) measureReal_nonneg
    (fun ρ hρ => ENNReal.toReal_pos (measure_inter_ball_ne_zero hxt hρ.1)
      (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne))
    (inv_pos.2 hn') (by positivity) (hδm.mono fun ρ h hρ => by
      rw [show 1 - (n : ℝ)⁻¹ = (p : ℝ)⁻¹ by simpa using hp.coe.one_sub_inv]
      exact h ⟨hρ.1, hρ.2.trans (hr.2.trans_le (min_le_left _ _))⟩)
  simp only [m, ball_zero, inter_empty, measureReal_empty, sub_zero,
    Real.zero_rpow (inv_pos.2 hn').ne'] at hgrowth
  have hroot : r / (3 * n * C) ≤ μ.real (t ∩ ball x r) ^ (n : ℝ)⁻¹ := by
    rcases eq_or_ne (C : ℝ) 0 with hC | hC
    · rw [hC, mul_zero, div_zero]
      positivity
    rw [div_le_iff₀ (mul_pos (mul_pos three_pos hn') (lt_of_le_of_ne C.coe_nonneg hC.symm))]
    have := mul_le_mul_of_nonneg_left hgrowth hn'.le
    rw [← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul] at this
    linarith
  rw [← hts, ← ofReal_measureReal (measure_ne_top_of_subset inter_subset_right
    measure_ball_lt_top.ne), ← Real.rpow_inv_natCast_pow measureReal_nonneg hn0]
  exact ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (div_nonneg hr.1.le (by positivity)) hroot n)

/-- **The lower volume density estimate for the complement.** In the setting of
`TauCeti.eventually_le_measure_inter_ball`, at a point `x` of the reduced boundary of `s` in `Ω`,
for every small `r > 0`,

`(r / (3 n C)) ^ n ≤ μ(ball x r \ s)`. -/
theorem eventually_le_measure_ball_sdiff (hp : NNReal.HolderConjugate (finrank ℝ E) p)
    (hx : x ∈ reducedBoundary μ Ω s) :
    ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal ((r / (3 * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p)) ^
      finrank ℝ E) ≤ μ (ball x r \ s) := by
  simpa only [sdiff_eq_compl_inter] using
    eventually_le_measure_inter_ball (s := sᶜ) hp (by rwa [reducedBoundary_compl])

/-- **The lower perimeter density estimate at the reduced boundary.** Let `E` have dimension
`n ≥ 2`, let `p = n / (n - 1)`, let `C` be the constant
`MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the Sobolev inequality and let
`ω = μ(ball 0 1)`. At a point `x` of the reduced boundary of `s` in `Ω`, for every small `r > 0`,

`(r / (3 n C)) ^ (n - 1) ≤ 2 ^ (n + 1) ω ^ (-1/n) P(s; ball x r)`.

Together with `TauCeti.eventually_perimeter_ball_le`, the relative perimeter `P(s; ball x r)` is
comparable to `r ^ (n - 1)` at every point of the reduced boundary. -/
theorem eventually_le_perimeter_ball (hp : NNReal.HolderConjugate (finrank ℝ E) p)
    (hx : x ∈ reducedBoundary μ Ω s) :
    ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal ((r / (3 * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p)) ^
      (finrank ℝ E - 1)) ≤ ENNReal.ofReal (2 ^ (finrank ℝ E + 1) /
        μ.real (ball 0 1) ^ (finrank ℝ E : ℝ)⁻¹) * perimeter μ ⟨ball x r, isOpen_ball⟩ s := by
  set n := finrank ℝ E
  have hn : 2 ≤ n := by
    have : (1 : ℝ) < n := by exact_mod_cast hp.lt
    exact_mod_cast this
  have hs := nullMeasurableSet_restrict_of_mem_reducedBoundary hx
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [eventually_le_measure_inter_ball hp hx, eventually_le_measure_ball_sdiff hp hx,
    Ioo_mem_nhdsGT hε] with r h1 h2 hr
  set a := r / (3 * n * eLpNormLESNormFDerivOneConst μ p)
  have ha : 0 ≤ a := div_nonneg hr.1.le (by positivity)
  have hexp : 0 ≤ 1 - (n : ℝ)⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ (by exact_mod_cast
    (one_le_two.trans hn)))
  refine Eq.trans_le ?_ ((ENNReal.rpow_le_rpow (le_min h1 h2) hexp).trans
    (min_measure_inter_measure_sdiff_rpow_le_perimeter hn
      (hs.mono (Measure.restrict_mono ((ball_subset_ball hr.2.le).trans hεΩ) le_rfl))
      (Ω := ⟨ball x r, isOpen_ball⟩) subset_rfl))
  rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg ha n) hexp, ← Real.rpow_natCast a n,
    ← Real.rpow_mul ha, ← Real.rpow_natCast a (n - 1), Nat.cast_sub (one_le_two.trans hn),
    Nat.cast_one, mul_sub, mul_one, mul_inv_cancel₀ (by positivity)]

end LowerDensity

end TauCeti
