/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.DensityEstimates
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
import TauCeti.Analysis.BoundedVariation.Compactness
import TauCeti.Analysis.BoundedVariation.Dilation
import TauCeti.Analysis.BoundedVariation.HalfSpace
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Distribution.TestFunction.Dilation
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.Analysis.Normed.Module.Ball
import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Blow-ups at points of the reduced boundary

Let `Ω` be an open set of a finite-dimensional real inner product space `E`, let `s` be a set
whose reduced boundary `∂*s` in `Ω` contains `x`, and let `ν = ν_s x` be the outer normal there.
The **blow-ups** of `s` at `x` are the sets `s_{x,r} = (s - x) / r`, written here as the
preimages `(fun y => x + r • y) ⁻¹' s`. This file shows that, as `r → 0⁺`, the blow-ups are
relatively compact for local convergence in measure, that every limit has locally finite perimeter
and fills a definite proportion of every ball around the origin together with its complement, and
that the distributional derivative of `χ_{s_{x,r}}` points in the direction `-ν` up to an error that
vanishes in the limit. In dimension at least two these combine into the **blow-up theorem** of De
Giorgi's structure theorem: the blow-ups converge locally in measure to the half-space
`{y | ⟪y, ν⟫ < 0}`, and consequently `s` has density one half at `x`.

* The scaling identities `TauCeti.perimeter_ball_zero_preimage_add_smul` and
  `MeasureTheory.Measure.addHaar_preimage_add_smul_inter_ball`, proved with the other dilation
  results, give `P(s_{x,r}; ball 0 R) = r^(1-n) P(s; ball x (r R))` and
  `μ(s_{x,r} ∩ ball 0 ρ) = r^(-n) μ(s ∩ ball x (r ρ))` against an additive Haar measure, where
  `n = dim E`. They transport the estimates below between `s` and its blow-ups.
* `TauCeti.eventually_perimeter_ball_zero_preimage_add_smul_le`: by the upper density estimate
  `TauCeti.eventually_perimeter_ball_le`, for every `t > 1` and `R > 0`,
  `P(s_{x,r}; ball 0 R) ≤ t n μ(ball 0 1) R^(n-1)` for every small `r > 0`.
* `TauCeti.exists_subseq_tendsto_measure_symmDiff_inter_preimage_add_smul`: **compactness of the
  blow-ups.** Along every sequence `r i → 0⁺`, a subsequence of the blow-ups converges locally in
  measure to a measurable set. This is the compactness theorem for sets of locally finite
  perimeter (`TauCeti.exists_subseq_tendsto_measure_symmDiff_inter_of_perimeter_le`), applied
  after cutting `s` by a small ball of finite perimeter (`TauCeti.ae_perimeter_inter_ball_le`), so
  that the perimeter bounds hold for every term of the sequence and not only for small radii.
* `TauCeti.perimeter_ball_zero_le_of_tendsto_measure_symmDiff_inter`: by lower semicontinuity
  (`TauCeti.perimeter_le_liminf`), a blow-up limit `F` satisfies
  `P(F; ball 0 R) ≤ t n μ(ball 0 1) R^(n-1)`, so it has locally finite perimeter in `E`.
* `TauCeti.ofReal_pow_le_mul_measure_inter_ball_of_tendsto_measure_symmDiff_inter` and
  `TauCeti.ofReal_pow_le_mul_measure_ball_sdiff_of_tendsto_measure_symmDiff_inter`: in dimension
  `n ≥ 2`, the lower density estimates at the reduced boundary pass to the limit, so that
  `ρ ^ n ≤ K ^ n μ(F ∩ ball 0 ρ)` and `ρ ^ n ≤ K ^ n μ(ball 0 ρ \ F)` for every `ρ > 0`, with the
  constant `K` of `TauCeti.eventually_ofReal_pow_le_mul_measure_inter_ball`. Neither `F` nor its
  complement is null near the origin.

* `TauCeti.eventually_neg_le_integral_divergenceCLM_mul_indicator_preimage`: against an additive
  Haar measure, for every test vector field `φ` on `E` with `⟪φ, ν⟫ ≥ 0` pointwise,
  `liminf_{r → 0⁺} ∫_{s_{x,r}} div φ ≥ 0`. Changing variables, the pairing is
  `r^(1-n) ∫ ⟪φ((y - x) / r), ν_s y⟫ d|Dχ_s|(y)`, `n = dim E`. Replacing `ν_s` by `ν` gives a
  nonnegative quantity, and the error is controlled by the concentration of the normal
  (`TauCeti.eventually_setIntegral_norm_outerNormal_sub_le`) together with the upper density
  estimate `|Dχ_s| (closedBall x ρ) ≤ C ρ^(n-1)`
  (`TauCeti.eventually_variationMeasure_closedBall_le`).
* `TauCeti.integral_divergenceCLM_mul_indicator_nonneg_of_tendsto_measure_symmDiff_inter`:
  consequently, if the blow-ups along a sequence of radii `r i → 0⁺` converge locally in measure
  to a set `F`, then `∫_F div φ ≥ 0` for every such `φ`. This is the distributional form of
  `Dχ_F = -ν m` for a positive measure `m`, that is, of the blow-up limit having constant outer
  normal `ν`.

* `TauCeti.ae_eq_setOf_inner_lt_of_tendsto_measure_symmDiff_inter`: in dimension `n ≥ 2`, every
  such blow-up limit agrees almost everywhere with `{y | ⟪y, ν⟫ < 0}`. A set with constant
  distributional normal `ν` is `∅`, the whole space or a half-space `{y | ⟪y, ν⟫ < c}`
  (`TauCeti.ae_eq_setOf_inner_lt_of_forall_integral_divergenceCLM_mul_indicator_nonneg`), and the
  lower density estimates for the limit and its complement exclude every case but `c = 0`.
* `TauCeti.tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter`: **the blow-up
  theorem.** In dimension `n ≥ 2`, `μ((s_{x,r} ∆ {y | ⟪y, ν⟫ < 0}) ∩ K) → 0` as `r → 0⁺` for
  every compact `K`. Every sequence of radii has a subsequence along which the blow-ups converge,
  and the limit is always the same half-space.
* `TauCeti.hasDensityAt_of_mem_reducedBoundary`: in dimension `n ≥ 2`, `s` has density one half at
  every point of its reduced boundary, the density of the half-space at the origin.

* `TauCeti.limsup_perimeter_ball_zero_preimage_add_smul_le_of_tendsto_measure_symmDiff_inter`: if
  the blow-ups converge locally in measure to `F`, then for `0 < R < R'`,
  `limsup P(s_{x,r i}; ball 0 R) ≤ P(F; ball 0 R')`. A cutoff multiple `φ` of `ν` equal to `ν` on
  `ball 0 R` has `P(s_{x,r}; ball 0 R) ≤ ∫_{s_{x,r}} div φ + o(1)` by the concentration of the
  normal, and the right side converges to `∫_F div φ ≤ P(F; ball 0 R')`.
* `TauCeti.tendsto_perimeter_ball_zero_preimage_add_smul`: in dimension `n ≥ 2`, the perimeters
  of the blow-ups converge to that of the half-space,
  `P(s_{x,r}; ball 0 R) → P({y | ⟪y, ν⟫ < 0}; ball 0 R)` for every `R > 0`. Lower semicontinuity
  gives the lower bound, and the upper bound follows from the previous item, since the perimeter
  of the half-space in `ball 0 (t R)` is `t ^ (n - 1)` times that in `ball 0 R`.
* `TauCeti.tendsto_perimeter_ball_div_ofReal_pow` and
  `TauCeti.tendsto_variationMeasure_closedBall_div_ofReal_pow`: equivalently,
  `P(s; ball x r) / r ^ (n - 1) → P({y | ⟪y, ν⟫ < 0}; ball 0 1)`, and the same holds for the
  perimeter measure of `closedBall x r`. This is the density of the perimeter measure at points of
  the reduced boundary. For Lebesgue measure the limit is the volume `ω_{n-1}` of the unit ball of
  `ℝ^(n-1)`.

No finite perimeter or measurability of `s` is assumed: a point of the reduced boundary forces
`s` to have locally finite perimeter in `Ω`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 15
  (blow-ups at points of the reduced boundary).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.2 (blow-up of the reduced boundary, and its Corollary 1 on the density of the perimeter).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric TestFunction Module
open scoped ENNReal NNReal Topology RealInnerProductSpace Distributions symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E} {x : E}

/-! ### The blow-up pairing -/

/-- Replacing the outer normal `ν_s` by `ν = ν_s x` in the pairing of `Dχ_s` with a bounded field
`ψ` that vanishes off `S` and satisfies `⟪ψ, ν⟫ ≥ 0` costs at most `M ∫_S ‖ν_s - ν‖ d|Dχ_s|`. -/
private theorem neg_mul_setIntegral_le_integral_inner_outerNormal
    {ψ : 𝓓(Ω, E)} {S : Set Ω} (hSm : MeasurableSet S)
    (hSfin : variationMeasure μ Ω (s.indicator 1) S ≠ ∞) {M : ℝ} (hM : ∀ y, ‖ψ y‖ ≤ M)
    (hψν : ∀ y, 0 ≤ ⟪ψ y, outerNormal μ Ω s x⟫) (hψS : ∀ y : Ω, y ∉ S → ψ y = 0) :
    -(M * ∫ y in S, ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖
        ∂variationMeasure μ Ω (s.indicator 1)) ≤
      ∫ y, ⟪ψ y, outerNormal μ Ω s y⟫ ∂variationMeasure μ Ω (s.indicator 1) := by
  set ν := outerNormal μ Ω s x
  have hg : IntegrableOn (fun y : Ω => -(M * ‖outerNormal μ Ω s y - ν‖)) S
      (variationMeasure μ Ω (s.indicator 1)) :=
    (((integrableOn_outerNormal hSfin).sub (integrableOn_const hSfin)).norm.const_mul M).neg
  rw [← integral_const_mul, ← integral_neg, ← integral_indicator hSm]
  refine integral_mono (hg.integrable_indicator hSm) ?_ fun y => ?_
  · refine (integrable_inner_polarDensity ψ.continuous ψ.hasCompactSupport
      ψ.tsupport_subset).neg.congr ?_
    filter_upwards [ae_outerNormal_eq] with y hy
    simp [hy, inner_neg_right]
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy]
    -- `⟪ψ, ν_s⟫ = ⟪ψ, ν⟫ + ⟪ψ, ν_s - ν⟫ ≥ -‖ψ‖ ‖ν_s - ν‖`.
    have h1 := neg_abs_le ⟪ψ y, outerNormal μ Ω s y - ν⟫
    have h2 := abs_real_inner_le_norm (ψ y) (outerNormal μ Ω s y - ν)
    rw [inner_sub_right] at h1 h2
    nlinarith [mul_le_mul_of_nonneg_right (hM y) (norm_nonneg (outerNormal μ Ω s y - ν)), hψν y]
  · simp [indicator_of_notMem hy, hψS y hy]

variable [μ.IsAddHaarMeasure]

/-- **Change of variables for the blow-up pairing.** If `ψ = φ((· - x) / r)` is a test vector
field on `Ω`, then `∫_{s_{x,r}} div φ dμ = r^(1-n) ∫ ⟪ψ, ν_s⟫ d|Dχ_s|`, and the integrand on the
left is integrable. -/
private theorem integrable_and_integral_divergenceCLM_mul_indicator_preimage
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (φ : 𝓓((⊤ : Opens E), E)) {ψ : 𝓓(Ω, E)} {r : ℝ} (hr : 0 < r)
    (hψ : ∀ y, divergenceCLM ψ y = r⁻¹ * divergenceCLM φ (r⁻¹ • (y - x))) :
    Integrable (fun y => divergenceCLM φ y * ((fun y => x + r • y) ⁻¹' s).indicator 1 y) μ ∧
      ∫ y, divergenceCLM φ y * ((fun y => x + r • y) ⁻¹' s).indicator 1 y ∂μ =
        r / r ^ finrank ℝ E *
          ∫ y, ⟪ψ y, outerNormal μ Ω s y⟫ ∂variationMeasure μ Ω (s.indicator 1) := by
  set k : E → ℝ := fun w => divergenceCLM ψ w * s.indicator 1 w
  have hk : Integrable k μ := by
    simpa only [smul_eq_mul] using TestFunction.integrable_smul (divergenceCLM ψ) hu
  have hpt (y : E) : divergenceCLM φ y * ((fun y => x + r • y) ⁻¹' s).indicator 1 y =
      r * k (x + r • y) := by
    simp only [k, hψ, add_sub_cancel_left, inv_smul_smul₀ hr.ne']
    by_cases hy : x + r • y ∈ s
    · simp [hy, hr.ne']
    · simp [hy]
  have hGG : ∫ w, k w ∂μ =
      ∫ y, ⟪ψ y, outerNormal μ Ω s y⟫ ∂variationMeasure μ Ω (s.indicator 1) := by
    simpa only [k, divergenceCLM_apply] using
      integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal hu hfin
        (ψ.contDiff.of_le (by simp)) ψ.hasCompactSupport ψ.tsupport_subset
  simp_rw [hpt]
  refine ⟨((hk.comp_add_left x).comp_smul hr.ne').const_mul r, ?_⟩
  rw [integral_const_mul, μ.integral_comp_smul (fun z => k (x + z)), integral_add_left_eq_self, hGG,
    abs_of_pos (by positivity), smul_eq_mul, ← mul_assoc, div_eq_mul_inv]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If `ψ = φ((· - x) / r)` for some `r > 0` and the support of `φ` lies in `closedBall 0 R'`, then
`ψ` vanishes off `closedBall x (R' * r)`. -/
private theorem eq_zero_of_notMem_closedBall_of_eq_comp {φ : 𝓓((⊤ : Opens E), E)} {ψ : 𝓓(Ω, E)}
    {r R' : ℝ} (hr : 0 < r) (hψ : ∀ y, ψ y = φ (r⁻¹ • (y - x)))
    (hφ : tsupport φ ⊆ closedBall 0 R') {y : E} (hy : y ∉ closedBall x (R' * r)) : ψ y = 0 := by
  rw [hψ]
  refine image_eq_zero_of_notMem_tsupport fun h => hy ?_
  rw [mul_comm]
  exact (inv_smul_sub_mem_closedBall_zero_iff hr).1 (hφ h)

/-- **The rescaled concentration of the outer normal.** Let `μ` be an additive Haar measure, let
`x` be a point of the reduced boundary of `s` in `Ω`, with outer normal `ν = ν_s x`, and let
`R' > 0`. For every `ε > 0` and every small `r > 0`, the perimeter measure of
`S = closedBall x (R' * r)` is finite and

`r / r ^ n * ∫_S ‖ν_s - ν‖ d|Dχ_s| ≤ ε`,     `n = dim E`. -/
private theorem eventually_div_pow_mul_setIntegral_norm_outerNormal_sub_le
    (hx : x ∈ reducedBoundary μ Ω s) {R' : ℝ} (hR' : 0 < R') {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x (R' * r)) ≠ ∞ ∧
        r / r ^ finrank ℝ E * ∫ y in ((↑) : Ω → E) ⁻¹' closedBall x (R' * r),
          ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖ ∂variationMeasure μ Ω (s.indicator 1) ≤
          ε := by
  set n := finrank ℝ E
  -- `E` is nontrivial, since it contains the unit vector `ν_s x`.
  have hν1 : ‖outerNormal μ Ω s x‖ = 1 := norm_outerNormal hx
  have : Nontrivial E := ⟨⟨outerNormal μ Ω s x, 0, fun h => by simp [h] at hν1⟩⟩
  set ω := μ.real (ball 0 1)
  set A := 4 * n * ω * R' ^ (n - 1) with hAdef
  set η := ε / (A + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  filter_upwards [eventually_nhdsGT_zero_mul_left hR'
      ((eventually_setIntegral_norm_outerNormal_sub_le hx hη).and
      (eventually_variationMeasure_closedBall_le hx (t := 2) (by norm_num))),
    self_mem_nhdsWithin] with r ⟨⟨_, h1⟩, h2⟩ (hr : 0 < r)
  set lam := variationMeasure μ Ω (s.indicator 1)
  set S := ((↑) : Ω → E) ⁻¹' closedBall x (R' * r)
  -- The perimeter measure of `S` is bounded by the upper density estimate.
  refine ⟨ne_top_of_le_ne_top (by finiteness) h2, ?_⟩
  have hlamS : lam.real S ≤ 2 * (n * (R' * r) ^ (n - 1) * ω) := by
    have h := ENNReal.toReal_mono (by finiteness) h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  have hrn : r / r ^ n * (R' * r) ^ (n - 1) = R' ^ (n - 1) := by
    have hn0 : n ≠ 0 := finrank_pos.ne'
    rw [mul_pow, ← pow_sub_one_mul hn0 r]
    field_simp
  have hsplit : r / r ^ n * (2 * η * (2 * (n * (R' * r) ^ (n - 1) * ω))) =
      4 * n * ω * η * (r / r ^ n * (R' * r) ^ (n - 1)) := by
    ring
  calc r / r ^ n * ∫ y in S, ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖ ∂lam
      ≤ r / r ^ n * (2 * η * (2 * (n * (R' * r) ^ (n - 1) * ω))) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hlamS (by positivity)))
          (by positivity)
    _ = A * η := by
        rw [hsplit, hrn, hAdef]
        ring
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- **The blow-ups at a point of the reduced boundary have normal `ν`, asymptotically.** Against an
additive Haar measure, let `x` be a point of the reduced boundary of `s` in `Ω`, with outer normal
`ν = ν_s x`. For every test vector field `φ` on `E` with `⟪φ, ν⟫ ≥ 0` pointwise and every
`ε > 0`, the blow-ups `s_{x,r} = (fun y => x + r • y) ⁻¹' s` satisfy, for every small `r > 0`,

`-ε ≤ ∫_{s_{x,r}} div φ dμ`. -/
theorem eventually_neg_le_integral_divergenceCLM_mul_indicator_preimage
    (hx : x ∈ reducedBoundary μ Ω s) (φ : 𝓓((⊤ : Opens E), E))
    (hφ : ∀ y, 0 ≤ ⟪φ y, outerNormal μ Ω s x⟫) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      -ε ≤ ∫ y, divergenceCLM φ y * ((fun y => x + r • y) ⁻¹' s).indicator 1 y ∂μ := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  -- Bounds on `φ` and on its support.
  obtain ⟨M, hM⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  set M' := max M 0
  set R' := max R 1
  have hM' : 0 ≤ M' := le_max_right _ _
  have hR' : 0 < R' := lt_max_of_lt_right one_pos
  have hη : 0 < ε / (M' + 1) := div_pos hε (by positivity)
  filter_upwards [eventually_div_pow_mul_setIntegral_norm_outerNormal_sub_le hx hR' hη,
    eventually_forall_tsupport_add_smul_mem (reducedBoundary_subset hx) φ,
    self_mem_nhdsWithin] with r ⟨hSfin, herr⟩ hΩ (hr : 0 < r)
  obtain ⟨ψ, hψ, hdiv⟩ := TestFunction.exists_eq_comp φ hr.ne' hΩ
  rw [(integrable_and_integral_divergenceCLM_mul_indicator_preimage hu hfin φ hr hdiv).2]
  -- Replacing `ν_s` by `ν` in the pairing costs at most `M' ∫_S ‖ν_s - ν‖ d|Dχ_s|`.
  have hlow := neg_mul_setIntegral_le_integral_inner_outerNormal
    (isClosed_closedBall.preimage continuous_subtype_val).measurableSet hSfin (M := M')
    (fun y => by rw [hψ]; exact (hM _).trans (le_max_left _ _)) (fun y => by rw [hψ]; exact hφ _)
    fun y hy => eq_zero_of_notMem_closedBall_of_eq_comp hr hψ
      (hR.trans (closedBall_subset_closedBall (le_max_left _ _))) hy
  have hscaled := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ r / r ^ finrank ℝ E)
  have herr' := mul_le_mul_of_nonneg_left herr hM'
  have hM'ε : M' * (ε / (M' + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- If the blow-ups `(fun y => x + r i • y) ⁻¹' s` at a point of the reduced boundary converge
locally in measure to a null-measurable set `F`, then their pairings with the divergence of every
test vector field `φ` on `E` converge: `∫_{s_{x,r i}} div φ dμ → ∫_F div φ dμ`. -/
private theorem tendsto_integral_divergenceCLM_mul_indicator_of_tendsto_measure_symmDiff_inter
    (hx : x ∈ reducedBoundary μ Ω s) {ι : Type*} {l : Filter ι} {r : ι → ℝ}
    (hr : Tendsto r l (𝓝[>] 0)) {F : Set E} (hF : NullMeasurableSet F μ)
    (hconv : ∀ K, IsCompact K →
      Tendsto (fun i => μ ((((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ K)) l (𝓝 0))
    (φ : 𝓓((⊤ : Opens E), E)) :
    Tendsto (fun i => ∫ y, divergenceCLM φ y * ((fun y => x + r i • y) ⁻¹' s).indicator 1 y ∂μ)
      l (𝓝 (∫ y, divergenceCLM φ y * F.indicator 1 y ∂μ)) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  set g := divergenceCLM φ
  set S : ι → Set E := fun i => (fun y => x + r i • y) ⁻¹' s
  have hint : ∀ᶠ i in l, Integrable (fun y => g y * (S i).indicator 1 y) μ := by
    filter_upwards [hr.eventually (eventually_forall_tsupport_add_smul_mem
      (reducedBoundary_subset hx) φ), hr.eventually self_mem_nhdsWithin] with i hΩ (hri : 0 < r i)
    obtain ⟨ψ, -, hdiv⟩ := TestFunction.exists_eq_comp φ hri.ne' hΩ
    exact (integrable_and_integral_divergenceCLM_mul_indicator_preimage hu hfin φ hri hdiv).1
  have hJ : Integrable (fun y => g y * F.indicator 1 y) μ := by
    refine (g.integrable_smul
      (locallyIntegrableOn_indicator_const (hF.mono Measure.restrict_le_self) 1)).congr
      (.of_forall fun y => ?_)
    simp [Pi.one_def]
  -- The pairings converge, since `|∫ g (χ_{S i} - χ_F)| ≤ C μ ((S i ∆ F) ∩ tsupport g)`.
  obtain ⟨C, hC⟩ := g.hasCompactSupport.exists_bound_of_continuous g.continuous
  rw [tendsto_iff_edist_tendsto_0]
  have hK := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ)
    (hconv _ g.hasCompactSupport.isCompact) (.inr enorm_ne_top)
  rw [mul_zero] at hK
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK
    (.of_forall fun _ => zero_le) (hint.mono fun i hi => ?_)
  rw [edist_eq_enorm_sub, ← integral_sub hi hJ]
  refine (enorm_integral_le_lintegral_enorm _).trans <|
    ((lintegral_mono fun y => ?_).trans_eq (lintegral_const_mul' _ _ enorm_ne_top)).trans
      (mul_le_mul_right (lintegral_indicator_one_le _) _)
  rw [← mul_sub, enorm_mul]
  by_cases hy : y ∈ tsupport g
  · have hgy : ‖g y‖ₑ ≤ ‖C‖ₑ := enorm_le_iff_norm_le.2 ((hC y).trans (le_abs_self C))
    by_cases h₁ : x + r i • y ∈ s <;> by_cases h₂ : y ∈ F <;>
      simp [S, mem_symmDiff, h₁, h₂, hy, hgy]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **Blow-up limits at the reduced boundary have outer normal `ν`.** Against an additive Haar
measure, let `x` be a point of the reduced boundary of `s` in `Ω`, with outer normal `ν = ν_s x`.
If the blow-ups `(fun y => x + r i • y) ⁻¹' s`, along radii `r i → 0⁺`, converge locally in
measure to a null-measurable set `F`, then

`0 ≤ ∫_F div φ dμ`

for every test vector field `φ` on `E` with `⟪φ, ν⟫ ≥ 0` pointwise. -/
theorem integral_divergenceCLM_mul_indicator_nonneg_of_tendsto_measure_symmDiff_inter
    (hx : x ∈ reducedBoundary μ Ω s) {ι : Type*} {l : Filter ι} [l.NeBot] {r : ι → ℝ}
    (hr : Tendsto r l (𝓝[>] 0)) {F : Set E} (hF : NullMeasurableSet F μ)
    (hconv : ∀ K, IsCompact K →
      Tendsto (fun i => μ ((((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ K)) l (𝓝 0))
    (φ : 𝓓((⊤ : Opens E), E)) (hφ : ∀ y, 0 ≤ ⟪φ y, outerNormal μ Ω s x⟫) :
    0 ≤ ∫ y, divergenceCLM φ y * F.indicator 1 y ∂μ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [← neg_le_iff_add_nonneg]
  exact ge_of_tendsto
    (tendsto_integral_divergenceCLM_mul_indicator_of_tendsto_measure_symmDiff_inter hx hr hF hconv
      φ)
    (hr.eventually (eventually_neg_le_integral_divergenceCLM_mul_indicator_preimage hx φ hφ hε))

/-! ### Perimeter and volume of the blow-ups -/

/-- The upper density bound `P(s; ball x (r R)) ≤ t n ω (r R) ^ (n - 1)` passes to the blow-up
`s_{x,r}` as `P(s_{x,r}; ball 0 R) ≤ t n ω R ^ (n - 1)`, in positive dimension `n`. -/
private theorem perimeter_ball_zero_preimage_add_smul_le_of_le [Nontrivial E] {s' : Set E}
    {t : ℝ≥0} {r : ℝ} (hr : 0 < r) {R : ℝ}
    (h : perimeter μ ⟨ball x (r * R), isOpen_ball⟩ s' ≤
      t * ENNReal.ofReal (finrank ℝ E * (r * R) ^ (finrank ℝ E - 1) * μ.real (ball 0 1))) :
    perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s') ≤
      t * ENNReal.ofReal (finrank ℝ E * R ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
  rw [perimeter_ball_zero_preimage_add_smul hr]
  refine (mul_le_mul_right h _).trans_eq ?_
  obtain ⟨m, hm⟩ : ∃ m, finrank ℝ E = m + 1 := ⟨_, (Nat.sub_add_cancel finrank_pos).symm⟩
  rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [hm, Nat.add_sub_cancel, mul_pow, pow_succ]
  field_simp

/-- The upper density estimate at a point of the reduced boundary, on every ball of small radius
contained in `Ω`. -/
private theorem exists_forall_perimeter_ball_le (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0}
    (ht : 1 < t) : ∃ ρ₀ > 0, ball x ρ₀ ⊆ Ω ∧ ∀ ρ ∈ Ioo 0 ρ₀,
      perimeter μ ⟨ball x ρ, isOpen_ball⟩ s ≤
        t * ENNReal.ofReal (finrank ℝ E * ρ ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  obtain ⟨ρ₀, hρ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (eventually_perimeter_ball_le hx ht)
  exact ⟨min ρ₀ ε, lt_min hρ₀ hε, (ball_subset_ball (min_le_right _ _)).trans hεΩ,
    fun ρ hρ => hsub ⟨hρ.1, hρ.2.trans_le (min_le_left _ _)⟩⟩

/-- **The blow-ups at a point of the reduced boundary have locally bounded perimeter.** Against an
additive Haar measure, let `x` be a point of the reduced boundary of `s` in `Ω`. For every `t > 1`
and `R > 0`, the blow-ups `s_{x,r} = (fun y => x + r • y) ⁻¹' s` satisfy, for every small `r > 0`,

`P(s_{x,r}; ball 0 R) ≤ t n μ(ball 0 1) R ^ (n - 1)`,     `n = dim E`. -/
theorem eventually_perimeter_ball_zero_preimage_add_smul_le (hx : x ∈ reducedBoundary μ Ω s)
    {t : ℝ≥0} (ht : 1 < t) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s) ≤
      t * ENNReal.ofReal (finrank ℝ E * R ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
  have hν1 : ‖outerNormal μ Ω s x‖ = 1 := norm_outerNormal hx
  have : Nontrivial E := ⟨⟨outerNormal μ Ω s x, 0, fun h => by simp [h] at hν1⟩⟩
  obtain ⟨ρ₀, hρ₀, -, hP⟩ := exists_forall_perimeter_ball_le hx ht
  filter_upwards [Ioo_mem_nhdsGT (div_pos hρ₀ hR)] with r hr
  exact perimeter_ball_zero_preimage_add_smul_le_of_le hr.1
    (hP _ ⟨mul_pos hr.1 hR, (lt_div_iff₀ hR).1 hr.2⟩)

/-! ### Compactness of the blow-ups -/

/-- The compactness of the blow-ups along a sequence of positive radii. -/
private theorem exists_subseq_tendsto_measure_symmDiff_inter_preimage_add_smul_of_pos
    (hx : x ∈ reducedBoundary μ Ω s) {r : ℕ → ℝ} (hpos : ∀ i, 0 < r i)
    (hr : Tendsto r atTop (𝓝 0)) :
    ∃ F, MeasurableSet F ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ K, IsCompact K →
      Tendsto (fun j => μ ((((fun y => x + r (φ j) • y) ⁻¹' s) ∆ F) ∩ K)) atTop (𝓝 0) := by
  have hν1 : ‖outerNormal μ Ω s x‖ = 1 := norm_outerNormal hx
  have : Nontrivial E := ⟨⟨outerNormal μ Ω s x, 0, fun h => by simp [h] at hν1⟩⟩
  obtain ⟨ρ₀, hρ₀, hρ₀Ω, hP⟩ := exists_forall_perimeter_ball_le hx (t := 2) one_lt_two
  have hsΩ : NullMeasurableSet (s ∩ Ω) μ := nullMeasurableSet_inter_of_mem_reducedBoundary hx
  -- `s ∩ Ω` agrees with `s` on the balls `ball x ρ`, `ρ ≤ ρ₀`.
  have hagree {ρ : ℝ} (hρ : ρ ≤ ρ₀) {a : Set E} (ha : a ⊆ ball x ρ) : s ∩ Ω ∩ a = s ∩ a := by
    rw [inter_assoc, inter_eq_right.2 (ha.trans ((ball_subset_ball hρ).trans hρ₀Ω))]
  -- Cut `s ∩ Ω` by a ball `ball x ρ`, `ρ < ρ₀`, to a set `s'` of finite perimeter.
  obtain ⟨ρ, hρ, hcut⟩ : ∃ ρ ∈ Ioo 0 ρ₀, perimeter μ ⊤ (s ∩ Ω ∩ ball x ρ) ≤
      perimeter μ ⟨ball x ρ, isOpen_ball⟩ (s ∩ Ω) +
        ENNReal.ofReal (deriv (fun ρ' => μ.real (s ∩ Ω ∩ ball x ρ')) ρ) := by
    have : (ae (volume.restrict (Ioo (0 : ℝ) ρ₀))).NeBot :=
      ae_restrict_neBot.2 (by simp [hρ₀])
    exact ((ae_restrict_mem measurableSet_Ioo).and
      (ae_restrict_of_ae (ae_perimeter_inter_ball_le hsΩ x))).exists
  set s' := s ∩ Ω ∩ ball x ρ
  have hs' : NullMeasurableSet s' μ := hsΩ.inter measurableSet_ball.nullMeasurableSet
  have hagree' {a : Set E} (ha : a ⊆ ball x ρ) : s' ∩ a = s ∩ a := by
    rw [inter_assoc, inter_eq_right.2 ha, hagree hρ.2.le ha]
  have hfin : perimeter μ ⊤ s' ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨?_, ENNReal.ofReal_ne_top⟩) hcut
    rw [perimeter_congr_of_inter_eq (hagree hρ.2.le subset_rfl)]
    exact ne_top_of_le_ne_top (by finiteness) (hP ρ hρ)
  -- The blow-ups of `s'` have locally bounded perimeter, uniformly along the sequence.
  have hbound (R : ℝ) (hR : 0 < R) : ∃ M : ℝ≥0, ∀ i,
      perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r i • y) ⁻¹' s') ≤ M := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hr.eventually (gt_mem_nhds (div_pos hρ.1 hR)))
    set A := (2 : ℝ≥0) * ENNReal.ofReal (finrank ℝ E * R ^ (finrank ℝ E - 1) * μ.real (ball 0 1))
    set B := ∑ i ∈ Finset.range N,
      perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r i • y) ⁻¹' s')
    have hB : B ≠ ∞ := by
      refine ENNReal.sum_ne_top.2 fun i _ => ?_
      rw [perimeter_ball_zero_preimage_add_smul (hpos i)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top hfin (perimeter_mono le_top))
    refine ⟨(A + B).toNNReal, fun i => ?_⟩
    rw [ENNReal.coe_toNNReal (ENNReal.add_ne_top.2 ⟨by finiteness, hB⟩)]
    rcases lt_or_ge i N with hi | hi
    · exact (Finset.single_le_sum (f := fun j => perimeter μ ⟨ball 0 R, isOpen_ball⟩
        ((fun y => x + r j • y) ⁻¹' s')) (fun j _ => zero_le) (Finset.mem_range.2 hi)).trans
          le_add_self
    · refine le_add_right ?_
      have hrR : r i * R < ρ := (lt_div_iff₀ hR).1 (hN i hi)
      refine perimeter_ball_zero_preimage_add_smul_le_of_le (hpos i) ?_
      rw [perimeter_congr_of_inter_eq (hagree' (ball_subset_ball hrR.le))]
      exact hP _ ⟨mul_pos (hpos i) hR, hrR.trans hρ.2⟩
  obtain ⟨F, hF, φ, hφ, hconv⟩ := exists_subseq_tendsto_measure_symmDiff_inter_of_perimeter_le
    (Ω := ⊤) (s := fun i => (fun y => x + r i • y) ⁻¹' s')
    (fun i => hs'.preimage (μ.quasiMeasurePreserving_add_smul x (hpos i).ne')) fun K hK _ => by
      obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball 0
      obtain ⟨M, hM⟩ := hbound (max R 1) (lt_max_of_lt_right one_pos)
      exact ⟨⟨ball 0 (max R 1), isOpen_ball⟩, hKR.trans (ball_subset_ball (le_max_left _ _)),
        le_top, M, hM⟩
  -- The blow-ups of `s` and `s'` agree on every bounded set, for small radii.
  refine ⟨F, hF, φ, hφ, fun K hK => ?_⟩
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball 0
  set R' := max R 1
  have hR' : 0 < R' := lt_max_of_lt_right one_pos
  refine (hconv K hK (subset_univ _)).congr' ?_
  filter_upwards [(hr.comp hφ.tendsto_atTop).eventually (gt_mem_nhds (div_pos hρ.1 hR'))]
    with j hj
  have hrR : r (φ j) * R' < ρ := (lt_div_iff₀ hR').1 hj
  exact congrArg μ <| preimage_add_smul_symmDiff_inter_eq (hpos _)
    (hagree' (ball_subset_ball hrR.le)) (hKR.trans (ball_subset_ball (le_max_left _ _)))

/-- **Compactness of the blow-ups at a point of the reduced boundary.** Against an additive Haar
measure, let `x` be a point of the reduced boundary of `s` in `Ω`. Along every sequence of radii
`r i → 0⁺`, a subsequence of the blow-ups `(fun y => x + r i • y) ⁻¹' s` converges locally in
measure to a measurable set `F`: `μ ((s_{x, r (φ j)} ∆ F) ∩ K) → 0` for every compact `K`.

The blow-ups have locally bounded perimeter
(`TauCeti.eventually_perimeter_ball_zero_preimage_add_smul_le`), so this is an instance of the
compactness theorem for sets of locally finite perimeter
(`TauCeti.exists_subseq_tendsto_measure_symmDiff_inter_of_perimeter_le`). -/
theorem exists_subseq_tendsto_measure_symmDiff_inter_preimage_add_smul
    (hx : x ∈ reducedBoundary μ Ω s) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝[>] 0)) :
    ∃ F, MeasurableSet F ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ K, IsCompact K →
      Tendsto (fun j => μ ((((fun y => x + r (φ j) • y) ⁻¹' s) ∆ F) ∩ K)) atTop (𝓝 0) := by
  -- Drop the finitely many nonpositive radii.
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hr.eventually self_mem_nhdsWithin)
  obtain ⟨F, hF, φ, hφ, hconv⟩ :=
    exists_subseq_tendsto_measure_symmDiff_inter_preimage_add_smul_of_pos hx
      (r := fun i => r (i + N)) (fun i => hN _ (Nat.le_add_left N i))
      ((hr.mono_right nhdsWithin_le_nhds).comp (tendsto_add_atTop_nat N))
  exact ⟨F, hF, fun j => φ j + N, fun i j hij => Nat.add_lt_add_right (hφ hij) N, hconv⟩

/-! ### Blow-up limits -/

/-- **Lower semicontinuity of the perimeter along blow-ups.** If the blow-ups
`(fun y => x + r i • y) ⁻¹' s` at a point of the reduced boundary converge locally in measure to a
null-measurable set `F`, then for every `R > 0`,

`P(F; ball 0 R) ≤ liminf P(s_{x,r i}; ball 0 R)`. -/
private theorem perimeter_ball_zero_le_liminf_of_tendsto_measure_symmDiff_inter
    (hx : x ∈ reducedBoundary μ Ω s) {ι : Type*} {l : Filter ι} {r : ι → ℝ}
    (hr : Tendsto r l (𝓝[>] 0)) {F : Set E} (hF : NullMeasurableSet F μ)
    (hconv : ∀ K, IsCompact K →
      Tendsto (fun i => μ ((((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ K)) l (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    perimeter μ ⟨ball 0 R, isOpen_ball⟩ F ≤
      liminf (fun i => perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r i • y) ⁻¹' s)) l := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  have hsΩ : NullMeasurableSet (s ∩ Ω) μ := nullMeasurableSet_inter_of_mem_reducedBoundary hx
  -- For small radii, the blow-ups of `s` and of the null-measurable set `s ∩ Ω` agree on
  -- `ball 0 R`.
  have hagree : ∀ᶠ i in l, 0 < r i ∧ s ∩ Ω ∩ ball x (r i * R) = s ∩ ball x (r i * R) := by
    filter_upwards [hr.eventually (Ioo_mem_nhdsGT (div_pos hε hR))] with i hi
    refine ⟨hi.1, ?_⟩
    rw [inter_assoc, inter_eq_right.2
      ((ball_subset_ball ((lt_div_iff₀ hR).1 hi.2).le).trans hεΩ)]
  calc perimeter μ ⟨ball 0 R, isOpen_ball⟩ F
      ≤ liminf (fun i => perimeter μ ⟨ball 0 R, isOpen_ball⟩
          ((fun y => x + r i • y) ⁻¹' (s ∩ Ω))) l :=
        perimeter_le_liminf ((hr.eventually self_mem_nhdsWithin).mono fun i hi =>
          hsΩ.preimage (μ.quasiMeasurePreserving_add_smul x (ne_of_gt hi))) hF fun K hK hKR =>
            (hconv K hK).congr' (hagree.mono fun i hi =>
              congrArg μ (preimage_add_smul_symmDiff_inter_eq hi.1 hi.2.symm hKR))
    _ = _ :=
        liminf_congr (hagree.mono fun i hi => perimeter_congr_of_inter_eq
          (Ω := ⟨ball 0 R, isOpen_ball⟩) (preimage_add_smul_inter_ball_eq hi.1 hi.2))

/-- **Blow-up limits have locally bounded perimeter.** Against an additive Haar measure, let `x` be
a point of the reduced boundary of `s` in `Ω`. If the blow-ups `(fun y => x + r i • y) ⁻¹' s`, along
radii `r i → 0⁺`, converge locally in measure to a null-measurable set `F`, then for every `t > 1`
and `R > 0`,

`P(F; ball 0 R) ≤ t n μ(ball 0 1) R ^ (n - 1)`,     `n = dim E`.

In particular `F` has locally finite perimeter in `E`. -/
theorem perimeter_ball_zero_le_of_tendsto_measure_symmDiff_inter
    (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0} (ht : 1 < t) {ι : Type*} {l : Filter ι}
    [l.NeBot] {r : ι → ℝ} (hr : Tendsto r l (𝓝[>] 0)) {F : Set E} (hF : NullMeasurableSet F μ)
    (hconv : ∀ K, IsCompact K →
      Tendsto (fun i => μ ((((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ K)) l (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    perimeter μ ⟨ball 0 R, isOpen_ball⟩ F ≤
      t * ENNReal.ofReal (finrank ℝ E * R ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) :=
  (perimeter_ball_zero_le_liminf_of_tendsto_measure_symmDiff_inter hx hr hF hconv hR).trans
    (liminf_le_of_frequently_le' (hr.eventually
      (eventually_perimeter_ball_zero_preimage_add_smul_le hx ht hR)).frequently)

/-- **Blow-up limits fill a definite proportion of every ball centred at the origin.** Let `E` have
dimension `n ≥ 2`, let `p = n / (n - 1)` and let `μ` be an additive Haar measure. Let `x` be a point
of the reduced boundary of `s` in `Ω`. If the blow-ups `(fun y => x + r i • y) ⁻¹' s`, along radii
`r i → 0⁺`, converge locally in measure to `F`, then for every `t > 1` and `ρ > 0`,

`ρ ^ n ≤ ((1 + t) n C) ^ n μ(F ∩ ball 0 ρ)`,

where `C` is the constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the
Gagliardo–Nirenberg–Sobolev inequality. This is the lower density estimate
`TauCeti.eventually_ofReal_pow_le_mul_measure_inter_ball` passed to the limit. -/
theorem ofReal_pow_le_mul_measure_inter_ball_of_tendsto_measure_symmDiff_inter {p : ℝ≥0}
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0}
    (ht : 1 < t) {ι : Type*} {l : Filter ι} [l.NeBot] {r : ι → ℝ} (hr : Tendsto r l (𝓝[>] 0))
    {F : Set E} (hconv : ∀ K, IsCompact K →
      Tendsto (fun i => μ ((((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ K)) l (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (ρ ^ finrank ℝ E) ≤
      ((1 + t) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p : ℝ≥0) ^ finrank ℝ E *
        μ (F ∩ ball 0 ρ) := by
  set c : ℝ≥0∞ := ((1 + t) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p : ℝ≥0) ^ finrank ℝ E
  have hc : c ≠ ∞ := by finiteness
  obtain ⟨ρ₀, hρ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_ofReal_pow_le_mul_measure_inter_ball hp hx ht)
  -- The rescaled lower density estimate holds for the blow-ups with small radii, and passes to
  -- the limit since `μ(s_{x,r} ∩ ball 0 ρ) ≤ μ(F ∩ ball 0 ρ) + μ((s_{x,r} ∆ F) ∩ closedBall 0 ρ)`.
  have hlim := ENNReal.Tendsto.const_mul (a := c)
    ((hconv _ (isCompact_closedBall 0 ρ)).const_add (μ (F ∩ ball 0 ρ))) (.inr hc)
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [hr.eventually (Ioo_mem_nhdsGT (div_pos hρ₀ hρ))] with i hi
  have hri : 0 < r i := hi.1
  have hsub' : (fun y => x + r i • y) ⁻¹' s ∩ ball 0 ρ ⊆
      F ∩ ball 0 ρ ∪ (((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ closedBall 0 ρ := by
    rintro y ⟨hys, hyρ⟩
    by_cases hyF : y ∈ F
    · exact .inl ⟨hyF, hyρ⟩
    · exact .inr ⟨.inl ⟨hys, hyF⟩, ball_subset_closedBall hyρ⟩
  calc ENNReal.ofReal (ρ ^ finrank ℝ E)
      = ENNReal.ofReal ((r i ^ finrank ℝ E)⁻¹) * ENNReal.ofReal ((r i * ρ) ^ finrank ℝ E) := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_pow, inv_mul_cancel_left₀ (by positivity)]
    _ ≤ ENNReal.ofReal ((r i ^ finrank ℝ E)⁻¹) * (c * μ (s ∩ ball x (r i * ρ))) :=
        mul_le_mul_right (hsub ⟨mul_pos hri hρ, (lt_div_iff₀ hρ).1 hi.2⟩) _
    _ = c * μ ((fun y => x + r i • y) ⁻¹' s ∩ ball 0 ρ) := by
        rw [Measure.addHaar_preimage_add_smul_inter_ball μ x hri.ne', abs_of_pos hri,
          abs_of_pos (by positivity), mul_left_comm]
    _ ≤ c * (μ (F ∩ ball 0 ρ) + μ ((((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ closedBall 0 ρ)) :=
        mul_le_mul_right ((measure_mono hsub').trans (measure_union_le _ _)) _

/-- **The complement of a blow-up limit fills a definite proportion of every ball centred at the
origin.** Under the hypotheses of
`TauCeti.ofReal_pow_le_mul_measure_inter_ball_of_tendsto_measure_symmDiff_inter`, for every `t > 1`
and `ρ > 0`,

`ρ ^ n ≤ ((1 + t) n C) ^ n μ(ball 0 ρ \ F)`. -/
theorem ofReal_pow_le_mul_measure_ball_sdiff_of_tendsto_measure_symmDiff_inter {p : ℝ≥0}
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0}
    (ht : 1 < t) {ι : Type*} {l : Filter ι} [l.NeBot] {r : ι → ℝ} (hr : Tendsto r l (𝓝[>] 0))
    {F : Set E} (hconv : ∀ K, IsCompact K →
      Tendsto (fun i => μ ((((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ K)) l (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (ρ ^ finrank ℝ E) ≤
      ((1 + t) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p : ℝ≥0) ^ finrank ℝ E *
        μ (ball 0 ρ \ F) := by
  -- The blow-ups of the complement converge to the complement of `F`.
  rw [sdiff_eq, inter_comm]
  refine ofReal_pow_le_mul_measure_inter_ball_of_tendsto_measure_symmDiff_inter hp
    (s := sᶜ) (by rwa [reducedBoundary_compl]) ht hr (fun K hK => ?_) hρ
  simpa only [preimage_compl, compl_symmDiff_compl] using hconv K hK

/-! ### The blow-up theorem -/

/-- In dimension at least two, a blow-up limit and its complement both charge every ball centred at
the origin. -/
private theorem measure_inter_ball_ne_zero_and_measure_ball_sdiff_ne_zero_of_tendsto
    (hn : 2 ≤ finrank ℝ E) (hx : x ∈ reducedBoundary μ Ω s) {ι : Type*} {l : Filter ι} [l.NeBot]
    {r : ι → ℝ} (hr : Tendsto r l (𝓝[>] 0)) {F : Set E}
    (hconv : ∀ K, IsCompact K →
      Tendsto (fun i => μ ((((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ K)) l (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) :
    μ (F ∩ ball 0 ρ) ≠ 0 ∧ μ (ball 0 ρ \ F) ≠ 0 := by
  have hp : NNReal.HolderConjugate (finrank ℝ E) (NNReal.conjExponent (finrank ℝ E)) :=
    .conjExponent (by exact_mod_cast hn)
  have hpos : ENNReal.ofReal (ρ ^ finrank ℝ E) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (pow_pos hρ _)).ne'
  refine ⟨fun h0 => hpos ?_, fun h0 => hpos ?_⟩
  · have h := ofReal_pow_le_mul_measure_inter_ball_of_tendsto_measure_symmDiff_inter hp hx
      one_lt_two hr hconv hρ
    rwa [h0, mul_zero, nonpos_iff_eq_zero] at h
  · have h := ofReal_pow_le_mul_measure_ball_sdiff_of_tendsto_measure_symmDiff_inter hp hx
      one_lt_two hr hconv hρ
    rwa [h0, mul_zero, nonpos_iff_eq_zero] at h

/-- **Blow-up limits are half-spaces.** Let `E` have dimension `n ≥ 2`, let `μ` be an additive Haar
measure, and let `x` be a point of the reduced boundary of `s` in `Ω`, with outer normal
`ν = ν_s x`. If the blow-ups `(fun y => x + r i • y) ⁻¹' s`, along radii `r i → 0⁺`, converge
locally in measure to a null-measurable set `F`, then `F` agrees almost everywhere with the
half-space `{y | ⟪y, ν⟫ < 0}`. -/
theorem ae_eq_setOf_inner_lt_of_tendsto_measure_symmDiff_inter
    (hn : 2 ≤ finrank ℝ E) (hx : x ∈ reducedBoundary μ Ω s) {ι : Type*} {l : Filter ι}
    [l.NeBot] {r : ι → ℝ} (hr : Tendsto r l (𝓝[>] 0)) {F : Set E} (hF : NullMeasurableSet F μ)
    (hconv : ∀ K, IsCompact K →
      Tendsto (fun i => μ ((((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ K)) l (𝓝 0)) :
    F =ᵐ[μ] {y | ⟪y, outerNormal μ Ω s x⟫ < 0} := by
  set ν := outerNormal μ Ω s x
  have hle (y : E) : |⟪y, ν⟫| ≤ ‖y‖ := by
    simpa [ν, norm_outerNormal hx] using abs_real_inner_le_norm y ν
  have hpos {ρ : ℝ} (hρ : 0 < ρ) :=
    measure_inter_ball_ne_zero_and_measure_ball_sdiff_ne_zero_of_tendsto hn hx hr hconv hρ
  -- The limit has constant normal `ν`, so it is `∅`, `univ` or a half-space `{⟪y, ν⟫ < c}`; the
  -- lower density estimates leave only the half-space with `c = 0`.
  rcases ae_eq_setOf_inner_lt_of_forall_integral_divergenceCLM_mul_indicator_nonneg hF
    (integral_divergenceCLM_mul_indicator_nonneg_of_tendsto_measure_symmDiff_inter hx hr hF
      hconv) with h | h | ⟨c, h⟩
  · refine absurd ?_ (hpos one_pos).1
    simpa using measure_congr (EventuallyEqSet.inter h (.refl _ (ball (0 : E) 1)))
  · refine absurd ?_ (hpos one_pos).2
    simpa using measure_congr (EventuallyEqSet.diff (.refl _ (ball (0 : E) 1)) h)
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · -- The ball of radius `-c` misses the half-space.
    refine absurd ?_ (hpos (neg_pos.2 hc)).1
    rw [measure_congr (EventuallyEqSet.inter h .rfl)]
    refine measure_mono_null (fun y ⟨hyH, hyρ⟩ => ?_) measure_empty
    rw [mem_ball_zero_iff] at hyρ
    have := neg_abs_le ⟪y, ν⟫
    exact absurd hyH (by simp only [mem_ofPred_eq, not_lt]; linarith [hle y])
  · exact h
  · -- The ball of radius `c` lies in the half-space.
    refine absurd ?_ (hpos hc).2
    rw [measure_congr (EventuallyEqSet.diff .rfl h)]
    refine measure_mono_null (fun y ⟨hyρ, hyH⟩ => hyH ?_) measure_empty
    rw [mem_ball_zero_iff] at hyρ
    exact (le_abs_self _).trans_lt ((hle y).trans_lt hyρ)

/-- **The blow-up theorem.** Let `E` have dimension `n ≥ 2`, let `μ` be an additive Haar measure,
and let `x` be a point of the reduced boundary of `s` in `Ω`, with outer normal `ν = ν_s x`. As
`r → 0⁺`, the blow-ups `(fun y => x + r • y) ⁻¹' s` converge locally in measure to the half-space
`{y | ⟪y, ν⟫ < 0}`: for every compact set `K`,

`μ((s_{x,r} ∆ {y | ⟪y, ν⟫ < 0}) ∩ K) → 0`. -/
theorem tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter
    (hn : 2 ≤ finrank ℝ E) (hx : x ∈ reducedBoundary μ Ω s) {K : Set E} (hK : IsCompact K) :
    Tendsto
      (fun r : ℝ => μ ((((fun y => x + r • y) ⁻¹' s) ∆ {y | ⟪y, outerNormal μ Ω s x⟫ < 0}) ∩ K))
      (𝓝[>] 0) (𝓝 0) := by
  -- Every sequence of radii has a subsequence along which the blow-ups converge, and the limit is
  -- the half-space.
  refine tendsto_of_subseq_tendsto fun r hr => ?_
  obtain ⟨F, hFm, φ, hφ, hconv⟩ :=
    exists_subseq_tendsto_measure_symmDiff_inter_preimage_add_smul hx hr
  have hH := ae_eq_setOf_inner_lt_of_tendsto_measure_symmDiff_inter hn hx
    (hr.comp hφ.tendsto_atTop) hFm.nullMeasurableSet hconv
  exact ⟨φ, (hconv K hK).congr fun j =>
    measure_congr (EventuallyEqSet.inter (EventuallyEqSet.symmDiff .rfl hH) .rfl)⟩

/-- **Points of the reduced boundary have density one half.** Let `E` have dimension `n ≥ 2` and
let `μ` be an additive Haar measure. At every point `x` of the reduced boundary of `s` in `Ω`,

`μ(s ∩ closedBall x r) / μ(closedBall x r) → 1 / 2`     as `r → 0⁺`. -/
theorem hasDensityAt_of_mem_reducedBoundary (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary μ Ω s) : HasDensityAt μ s x (1 / 2) := by
  set ν := outerNormal μ Ω s x
  have hν : ν ≠ 0 := norm_ne_zero_iff.1 (by simp [ν, norm_outerNormal hx])
  set H := {y : E | ⟪y, ν⟫ < 0}
  set B := closedBall (0 : E) 1
  set S : ℝ → Set E := fun r => (fun y => x + r • y) ⁻¹' s
  have hB : μ B ≠ 0 := (measure_closedBall_pos μ 0 one_pos).ne'
  have hB' : μ B ≠ ∞ := measure_closedBall_lt_top.ne
  have hHB : μ (H ∩ B) ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
  have hΔ : Tendsto (fun r => μ ((S r ∆ H) ∩ B)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx (isCompact_closedBall 0 1)
  -- The volumes of the blow-ups in the unit ball converge to that of the half-ball.
  have hlim : Tendsto (fun r => μ (S r ∩ B)) (𝓝[>] 0) (𝓝 (μ (H ∩ B))) := by
    have hle (a b : Set E) : μ a ≤ μ (a ∆ b) + μ b :=
      (measure_mono (le_symmDiff_sup_right a b)).trans (measure_union_le _ _)
    have hlow := ENNReal.Tendsto.sub tendsto_const_nhds hΔ (.inl hHB)
    have hup := hΔ.add_const (μ (H ∩ B))
    rw [tsub_zero] at hlow
    rw [zero_add] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun r => ?_) fun r => ?_
    · rw [tsub_le_iff_right, add_comm, symmDiff_comm, inter_symmDiff_distrib_right]
      exact hle _ _
    · rw [inter_symmDiff_distrib_right]
      exact hle _ _
  have hval : μ (H ∩ B) / μ B = 1 / 2 := by
    rw [μ.addHaar_setOf_inner_lt_inter_closedBall hν (inner_zero_left _), ENNReal.div_right_comm,
      ENNReal.div_self hB hB']
  -- Rescaling by `r` turns the density ratio of `s` at `x` into that of `S r` in the unit ball.
  rw [hasDensityAt_iff, ← hval]
  refine (ENNReal.Tendsto.div_const hlim (.inr hB)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hc : ENNReal.ofReal (r ^ finrank ℝ E) * ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  rw [Measure.addHaar_closedBall' μ x hr.le,
    Measure.addHaar_preimage_add_smul_inter_closedBall μ x hr.ne', abs_of_pos hr, mul_one,
    ← ENNReal.mul_div_mul_left _ _ (left_ne_zero_of_mul_eq_one hc) ENNReal.ofReal_ne_top]
  rw [← mul_assoc, hc, one_mul]

/-! ### Convergence of the perimeter of the blow-ups -/

/-- The key estimate for the upper bound on the perimeter of the blow-ups. Let `x` be a point of
the reduced boundary of `s` in `Ω`, with outer normal `ν`, let `0 < R` and let `φ` be a test
vector field with `‖φ‖ ≤ 1` and `⟪φ, ν⟫ ≥ 0` pointwise that equals `ν` on `ball 0 R` and has
support in `closedBall 0 R'`, `R ≤ R'`. Then for every `ε > 0` and every small `r > 0`,

`P(s_{x,r}; ball 0 R) ≤ ∫_{s_{x,r}} div φ dμ + ε`. -/
private theorem eventually_perimeter_ball_zero_preimage_add_smul_le_integral
    (hx : x ∈ reducedBoundary μ Ω s) {R R' : ℝ} (hR : 0 < R) (hRR' : R ≤ R')
    (φ : 𝓓((⊤ : Opens E), E)) (hφ1 : ∀ y, ‖φ y‖ ≤ 1)
    (hφ0 : ∀ y, 0 ≤ ⟪φ y, outerNormal μ Ω s x⟫)
    (hφR : ∀ y ∈ ball (0 : E) R, φ y = outerNormal μ Ω s x)
    (hφR' : tsupport φ ⊆ closedBall 0 R') {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s) ≤
      ENNReal.ofReal
        (∫ y, divergenceCLM φ y * ((fun y => x + r • y) ⁻¹' s).indicator 1 y ∂μ + ε) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [eventually_div_pow_mul_setIntegral_norm_outerNormal_sub_le hx
      (hR.trans_le hRR') hε,
    eventually_forall_tsupport_add_smul_mem (reducedBoundary_subset hx) φ,
    Ioo_mem_nhdsGT (div_pos hδ hR)] with r ⟨hSfin, herr⟩ hΩ hr
  have hr0 : 0 < r := hr.1
  have hballΩ : ball x (r * R) ⊆ Ω := (ball_subset_ball ((lt_div_iff₀ hR).1 hr.2).le).trans hδΩ
  obtain ⟨ψ, hψ, hdiv⟩ := TestFunction.exists_eq_comp φ hr0.ne' hΩ
  rw [(integrable_and_integral_divergenceCLM_mul_indicator_preimage hu hfin φ hr0 hdiv).2,
    perimeter_ball_zero_preimage_add_smul hr0, perimeter_def,
    ← variationMeasure_preimage_coe hu hfin (U := ⟨ball x (r * R), isOpen_ball⟩) hballΩ,
    Opens.coe_mk]
  set lam := variationMeasure μ Ω (s.indicator 1)
  set ν := outerNormal μ Ω s x
  set n := finrank ℝ E
  set B := ((↑) : Ω → E) ⁻¹' ball x (r * R)
  set S := ((↑) : Ω → E) ⁻¹' closedBall x (R' * r)
  -- The rescaled field `ψ` equals `ν` on `B` and vanishes off `S`.
  have hψB (y : Ω) (hy : y ∈ B) : ψ y = ν := by
    rw [hψ]
    refine hφR _ ?_
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr0.le),
      inv_mul_lt_iff₀ hr0, ← dist_eq_norm]
    exact hy
  have hBm : MeasurableSet B := (isOpen_ball.preimage continuous_subtype_val).measurableSet
  have hBS : B ⊆ S := fun y hy => by
    have hy' : dist (y : E) x < r * R := hy
    have : r * R ≤ R' * r := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hRR' hr0.le
    exact le_of_lt (hy'.trans_le this)
  have hBfin : lam B ≠ ∞ := ne_top_of_le_ne_top hSfin (measure_mono hBS)
  have hmain : lam.real B ≤ ∫ y, ⟪ψ y, outerNormal μ Ω s y⟫ ∂lam +
      ∫ y in S, ‖outerNormal μ Ω s y - ν‖ ∂lam :=
    variationMeasure_real_le_integral_inner_outerNormal_add (norm_outerNormal hx) hBm
    (isClosed_closedBall.preimage continuous_subtype_val).measurableSet hBS hSfin
    (ψ.continuous.comp continuous_subtype_val).aestronglyMeasurable
    (fun y _ => by rw [hψ]; exact hφ1 _) (fun y _ => by rw [hψ]; exact hφ0 _) hψB
    (fun y hy => eq_zero_of_notMem_closedBall_of_eq_comp hr0 hψ hφR' hy)
  rw [← ofReal_measureReal hBfin, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ r / r ^ n)
  rw [mul_add] at this
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- For `R < R'`, some test vector field on `E` is a multiple `a • ν`, `0 ≤ a ≤ 1`, of `ν` at
every point, equals `ν` on `ball 0 R` and has support in `ball 0 R'`. -/
private theorem exists_testFunction_eq_smul (ν : E) {R R' : ℝ} (hRR' : R < R') :
    ∃ φ : 𝓓((⊤ : Opens E), E), (∀ y, ∃ a ∈ Icc (0 : ℝ) 1, φ y = a • ν) ∧
      (∀ y ∈ ball (0 : E) R, φ y = ν) ∧ tsupport φ ⊆ ball 0 R' := by
  obtain ⟨χ, hχ1, hχ01⟩ := exists_eventually_eq_one (n := ⊤)
    (Ω := ⟨ball (0 : E) R', isOpen_ball⟩) (isCompact_closedBall 0 R)
    (closedBall_subset_ball hRR')
  refine ⟨⟨fun y => χ y • ν, χ.contDiff.smul contDiff_const, χ.hasCompactSupport.smul_right,
    by simp⟩, fun y => ⟨χ y, hχ01 y, rfl⟩, fun y hy => ?_,
    (tsupport_smul_subset_left _ _).trans χ.tsupport_subset⟩
  simp [hχ1.self_of_nhdsSet y (ball_subset_closedBall hy)]

/-- **An upper bound for the perimeter of the blow-ups.** Against an additive Haar measure, let `x`
be a point of the reduced boundary of `s` in `Ω`. If the blow-ups `(fun y => x + r i • y) ⁻¹' s`,
along radii `r i → 0⁺`, converge locally in measure to a null-measurable set `F`, then for
`0 < R < R'`,

`limsup P(s_{x,r i}; ball 0 R) ≤ P(F; ball 0 R')`. -/
theorem limsup_perimeter_ball_zero_preimage_add_smul_le_of_tendsto_measure_symmDiff_inter
    (hx : x ∈ reducedBoundary μ Ω s) {ι : Type*} {l : Filter ι} [l.NeBot] {r : ι → ℝ}
    (hr : Tendsto r l (𝓝[>] 0)) {F : Set E} (hF : NullMeasurableSet F μ)
    (hconv : ∀ K, IsCompact K →
      Tendsto (fun i => μ ((((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ K)) l (𝓝 0))
    {R R' : ℝ} (hR : 0 < R) (hRR' : R < R') :
    limsup (fun i => perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r i • y) ⁻¹' s)) l ≤
      perimeter μ ⟨ball 0 R', isOpen_ball⟩ F := by
  set ν := outerNormal μ Ω s x
  have hν1 : ‖ν‖ = 1 := norm_outerNormal hx
  -- Test with a cutoff multiple `φ` of `ν` that equals `ν` on `ball 0 R`.
  obtain ⟨φ, hφ, hφR, hsupp⟩ := exists_testFunction_eq_smul ν hRR'
  have hφ1 (y : E) : ‖φ y‖ ≤ 1 := by
    obtain ⟨a, ⟨ha0, ha1⟩, h⟩ := hφ y
    rwa [h, norm_smul, hν1, mul_one, Real.norm_of_nonneg ha0]
  have hφ0 (y : E) : 0 ≤ ⟪φ y, ν⟫ := by
    obtain ⟨a, ⟨ha0, -⟩, h⟩ := hφ y
    rw [h, real_inner_smul_left, real_inner_self_eq_norm_sq, hν1]
    positivity
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  calc limsup (fun i => perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r i • y) ⁻¹' s)) l
      ≤ limsup (fun i => ENNReal.ofReal
          (∫ y, divergenceCLM φ y * ((fun y => x + r i • y) ⁻¹' s).indicator 1 y ∂μ + ε)) l :=
        limsup_le_limsup (hr.eventually
          (eventually_perimeter_ball_zero_preimage_add_smul_le_integral hx hR hRR'.le φ hφ1 hφ0
            hφR (hsupp.trans ball_subset_closedBall) (NNReal.coe_pos.2 hε)))
    _ = ENNReal.ofReal (∫ y, divergenceCLM φ y * F.indicator 1 y ∂μ + ε) :=
        ((ENNReal.continuous_ofReal.tendsto _).comp
          ((tendsto_integral_divergenceCLM_mul_indicator_of_tendsto_measure_symmDiff_inter
            hx hr hF hconv φ).add_const _)).limsup_eq
    _ ≤ ENNReal.ofReal (∫ y, divergenceCLM φ y * F.indicator 1 y ∂μ) + ε := by
        refine ENNReal.ofReal_add_le.trans_eq ?_
        rw [ENNReal.ofReal_coe_nnreal]
    -- The pairing with `F` is at most its perimeter in `ball 0 R'`.
    _ ≤ perimeter μ ⟨ball 0 R', isOpen_ball⟩ F + ε := by
        gcongr
        rw [perimeter_def]
        exact ofReal_integral_le_totalVariationOn_of_tsupport_subset
          (Ω' := ⟨ball 0 R', isOpen_ball⟩) φ hφ1 hsupp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- If `a ≤ t ^ k b` for every `t > 1`, then `a ≤ b`. -/
private theorem le_of_forall_one_lt_le_ofReal_pow_mul {a b : ℝ≥0∞} {k : ℕ}
    (h : ∀ t : ℝ, 1 < t → a ≤ ENNReal.ofReal (t ^ k) * b) : a ≤ b := by
  have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ k)) (𝓝[>] 1) (𝓝 1) := by
    simpa [Function.comp_def] using
      ((ENNReal.continuous_ofReal.comp (continuous_pow _)).tendsto 1).mono_left
        nhdsWithin_le_nhds
  exact ge_of_tendsto (by simpa using ENNReal.Tendsto.mul_const h1 (.inl one_ne_zero))
    (eventually_nhdsWithin_of_forall h)

/-- **The perimeter of the blow-ups converges to that of the half-space.** Let `E` have dimension
`n ≥ 2`, let `μ` be an additive Haar measure, and let `x` be a point of the reduced boundary of `s`
in `Ω`, with outer normal `ν = ν_s x`. For every `R > 0`, as `r → 0⁺`,

`P(s_{x,r}; ball 0 R) → P({y | ⟪y, ν⟫ < 0}; ball 0 R)`. -/
theorem tendsto_perimeter_ball_zero_preimage_add_smul (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary μ Ω s) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ => perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s))
      (𝓝[>] 0)
      (𝓝 (perimeter μ ⟨ball 0 R, isOpen_ball⟩ {y | ⟪y, outerNormal μ Ω s x⟫ < 0})) := by
  set H := {y : E | ⟪y, outerNormal μ Ω s x⟫ < 0}
  have hHm : NullMeasurableSet H μ :=
    (measurableSet_lt (by fun_prop) measurable_const).nullMeasurableSet
  have hconv (K : Set E) (hK : IsCompact K) :=
    tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx hK
  refine tendsto_of_le_liminf_of_limsup_le
    (perimeter_ball_zero_le_liminf_of_tendsto_measure_symmDiff_inter hx tendsto_id hHm hconv hR) ?_
  -- The upper bound `P(H; ball 0 (t R)) = t ^ (n - 1) P(H; ball 0 R)` for every `t > 1`.
  refine le_of_forall_one_lt_le_ofReal_pow_mul (k := finrank ℝ E - 1) fun t ht => ?_
  rw [← perimeter_ball_zero_mul_setOf_inner_lt _ (by linarith) R]
  exact limsup_perimeter_ball_zero_preimage_add_smul_le_of_tendsto_measure_symmDiff_inter hx
    tendsto_id hHm hconv hR (by nlinarith)

/-- **The density of the perimeter at the reduced boundary.** Let `E` have dimension `n ≥ 2`, let
`μ` be an additive Haar measure, and let `x` be a point of the reduced boundary of `s` in `Ω`, with
outer normal `ν = ν_s x`. As `r → 0⁺`,

`P(s; ball x r) / r ^ (n - 1) → P({y | ⟪y, ν⟫ < 0}; ball 0 1)`,

the perimeter of the half-space in the unit ball. For Lebesgue measure this constant is the volume
`ω_{n-1}` of the unit ball of `ℝ^(n-1)`, by the computation of the perimeter of a half-space in
`TauCeti.Analysis.BoundedVariation.Hyperplane`. -/
theorem tendsto_perimeter_ball_div_ofReal_pow (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary μ Ω s) :
    Tendsto (fun r : ℝ => perimeter μ ⟨ball x r, isOpen_ball⟩ s /
        ENNReal.ofReal r ^ (finrank ℝ E - 1)) (𝓝[>] 0)
      (𝓝 (perimeter μ ⟨ball 0 1, isOpen_ball⟩ {y | ⟪y, outerNormal μ Ω s x⟫ < 0})) := by
  refine (tendsto_perimeter_ball_zero_preimage_add_smul hn hx one_pos).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  -- `r / r ^ n = (r ^ (n - 1))⁻¹`.
  have hc : ENNReal.ofReal (r / r ^ finrank ℝ E) = (ENNReal.ofReal r ^ (finrank ℝ E - 1))⁻¹ := by
    rw [← pow_sub_one_mul (by omega) r, div_mul_cancel_right₀ hr.ne',
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow hr.le]
  rw [perimeter_ball_zero_preimage_add_smul hr, mul_one, hc, ENNReal.div_eq_inv_mul]

/-- **The density of the perimeter measure on closed balls.** Under the hypotheses of
`TauCeti.tendsto_perimeter_ball_div_ofReal_pow`, the perimeter measure `|Dχ_s|` on `Ω` satisfies,
as `r → 0⁺`,

`|Dχ_s| (closedBall x r) / r ^ (n - 1) → P({y | ⟪y, ν⟫ < 0}; ball 0 1)`. -/
theorem tendsto_variationMeasure_closedBall_div_ofReal_pow (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary μ Ω s) :
    Tendsto (fun r : ℝ => variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) /
        ENNReal.ofReal r ^ (finrank ℝ E - 1)) (𝓝[>] 0)
      (𝓝 (perimeter μ ⟨ball 0 1, isOpen_ball⟩ {y | ⟪y, outerNormal μ Ω s x⟫ < 0})) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  set k := finrank ℝ E - 1
  set g : ℝ → ℝ≥0∞ := fun r => perimeter μ ⟨ball x r, isOpen_ball⟩ s / ENNReal.ofReal r ^ k
  have hg := tendsto_perimeter_ball_div_ofReal_pow hn hx
  -- On balls inside `Ω`, the perimeter is the perimeter measure of the ball.
  have hP {ρ : ℝ} (hρ : ρ ≤ δ) : perimeter μ ⟨ball x ρ, isOpen_ball⟩ s =
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' ball x ρ) := by
    rw [perimeter_def, ← variationMeasure_preimage_coe hu hfin (U := ⟨ball x ρ, isOpen_ball⟩)
      ((ball_subset_ball hρ).trans hδΩ), Opens.coe_mk]
  refine tendsto_of_le_liminf_of_limsup_le (hg.liminf_eq.symm.trans_le (liminf_le_liminf ?_)) ?_
  · -- Lower bound: `ball x r ⊆ closedBall x r`.
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    rw [hP hr.2.le]
    gcongr
    exact preimage_mono ball_subset_closedBall
  -- Upper bound: `closedBall x r ⊆ ball x (t * r)`, and `g (t * r) → P(H; ball 0 1)`.
  refine le_of_forall_one_lt_le_ofReal_pow_mul (k := k) fun t ht => ?_
  have hgt : Tendsto (fun r => ENNReal.ofReal (t ^ k) * g (t * r)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (t ^ k) *
        perimeter μ ⟨ball 0 1, isOpen_ball⟩ {y | ⟪y, outerNormal μ Ω s x⟫ < 0})) :=
    ENNReal.Tendsto.const_mul
      (hg.comp (tendsto_comap.mono_left (comap_mulLeft_nhdsGT_zero (by linarith)).ge))
      (.inr ENNReal.ofReal_ne_top)
  refine (limsup_le_limsup ?_).trans_eq hgt.limsup_eq
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ (by linarith : (0 : ℝ) < t))] with r hr
  have hr0 : 0 < r := hr.1
  have htr : t * r ≤ δ := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < t)).1 hr.2
    linarith
  have ht0 : (0 : ℝ) ≤ t := by linarith
  simp only [g]
  rw [ENNReal.ofReal_pow ht0, ENNReal.ofReal_mul ht0, mul_pow, ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (pow_ne_zero k (ENNReal.ofReal_pos.2 (by linarith : 0 < t)).ne')
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), hP htr]
  gcongr
  -- `closedBall x r ⊆ ball x (t * r)`.
  nlinarith

end TauCeti
