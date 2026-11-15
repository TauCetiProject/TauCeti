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
import TauCeti.Analysis.BoundedVariation.Hyperplane
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Distribution.TestFunction.Dilation
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Analysis.Distribution.TestFunction.Integral
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
`{y | ⟪y, ν⟫ < 0}`, and consequently `s` has density one half at `x`. The perimeters of the
blow-ups in the unit ball converge to that of the half-space, which gives the density of the
perimeter measure `|Dχ_s|` at `x`.

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

* `TauCeti.tendsto_variationMeasure_closedBall_div` and `TauCeti.tendsto_perimeter_ball_div`:
  **the density of the perimeter measure.** In dimension `n ≥ 2`,
  `|Dχ_s|(closedBall x r) / r ^ (n - 1)` and `P(s; ball x r) / r ^ (n - 1)` tend to the perimeter
  `P({y | ⟪y, ν⟫ < 0}; ball 0 1)` of the limiting half-space in the unit ball. The lower bound is
  lower semicontinuity of the perimeter along the blow-ups. For the upper bound, `|Dχ_s|` of a
  ball is tested against `θ((· - x) / r) ν` for a bump `θ`; replacing `ν_s` by `ν` costs little by
  the concentration of the normal, and the rescaled pairings converge to those of the half-space.
* `TauCeti.tendsto_variationMeasure_closedBall_div_volume_closedBall`: for Lebesgue measure the
  limit is the volume `ω_{n-1}` of the unit ball of `ℝ^(n-1)`
  (`TauCeti.perimeter_ball_setOf_inner_lt`), so
  `|Dχ_s|(closedBall x r) / (ω_{n-1} r ^ (n - 1)) → 1`: the perimeter measure has density one
  with respect to the normalized Hausdorff measure `μHE[n - 1]` at every point of the reduced
  boundary. This is the density statement from which De Giorgi's structure theorem identifies
  `|Dχ_s|` with `μHE[n - 1]` on `∂*s`.

No finite perimeter or measurability of `s` is assumed: a point of the reduced boundary forces
`s` to have locally finite perimeter in `Ω`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 15
  (blow-ups at points of the reduced boundary).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.2 (blow-up of the reduced boundary, and Corollary 1 there for the density of the perimeter
  measure).
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 15.5 (the
  convergence of the perimeter measures of the blow-ups).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric TestFunction Module
open scoped ENNReal NNReal Topology RealInnerProductSpace Distributions symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E} {x : E}

/-! ### The blow-up pairing -/

/-- Replacing a vector `v` by the outer normal `ν_s` in the pairing of `Dχ_s` with a field `ψ`
bounded by `M` that vanishes off `S` costs at most `M ∫_S ‖ν_s - v‖ d|Dχ_s|`. -/
private theorem integral_inner_sub_mul_setIntegral_le_integral_inner_outerNormal
    {ψ : 𝓓(Ω, E)} {S : Set Ω} (hSm : MeasurableSet S)
    (hSfin : variationMeasure μ Ω (s.indicator 1) S ≠ ∞) {M : ℝ} (hM : ∀ y, ‖ψ y‖ ≤ M)
    (hψS : ∀ y : Ω, y ∉ S → ψ y = 0) (v : E) :
    ∫ y, ⟪ψ y, v⟫ ∂variationMeasure μ Ω (s.indicator 1) -
        M * ∫ y in S, ‖outerNormal μ Ω s y - v‖ ∂variationMeasure μ Ω (s.indicator 1) ≤
      ∫ y, ⟪ψ y, outerNormal μ Ω s y⟫ ∂variationMeasure μ Ω (s.indicator 1) := by
  have hg : IntegrableOn (fun y : Ω => M * ‖outerNormal μ Ω s y - v‖) S
      (variationMeasure μ Ω (s.indicator 1)) :=
    ((integrableOn_outerNormal hSfin).sub (integrableOn_const hSfin)).norm.const_mul M
  have := Ω.isOpen.locallyCompactSpace
  have hv := ψ.integrable_inner_subtype
    (locallyIntegrable_const (μ := variationMeasure μ Ω (s.indicator 1)) v)
  rw [← integral_const_mul, ← integral_indicator hSm,
    ← integral_sub hv (hg.integrable_indicator hSm)]
  refine integral_mono (hv.sub (hg.integrable_indicator hSm)) ?_ fun y => ?_
  · refine (integrable_inner_polarDensity ψ.continuous ψ.hasCompactSupport
      ψ.tsupport_subset).neg.congr ?_
    filter_upwards [ae_outerNormal_eq] with y hy
    simp [hy, inner_neg_right]
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy]
    -- `⟪ψ, v⟫ - ⟪ψ, ν_s⟫ = ⟪ψ, v - ν_s⟫ ≤ ‖ψ‖ ‖ν_s - v‖`.
    have h := real_inner_le_norm (ψ y) (v - outerNormal μ Ω s y)
    rw [inner_sub_right, norm_sub_rev] at h
    nlinarith [mul_le_mul_of_nonneg_right (hM y) (norm_nonneg (outerNormal μ Ω s y - v))]
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

/-- **The blow-up pairing against the limiting normal.** Against an additive Haar measure, let `x`
be a point of the reduced boundary of `s` in `Ω`, with outer normal `ν = ν_s x`. For every test
vector field `φ` on `E` and every `ε > 0`, for every small `r > 0` the field
`⟪φ((· - x) / r), ν⟫` is `|Dχ_s|`-integrable and

`r^(1-n) ∫ ⟪φ((y - x) / r), ν⟫ d|Dχ_s|(y) - ε ≤ ∫_{s_{x,r}} div φ dμ`,    `n = dim E`.

Changing variables, the right side is `r^(1-n) ∫ ⟪φ((y - x) / r), ν_s y⟫ d|Dχ_s|(y)`. Replacing
`ν_s` by `ν` costs an error controlled by the concentration of the normal together with the upper
density estimate. -/
private theorem eventually_integrable_and_integral_inner_sub_le_integral_divergenceCLM
    (hx : x ∈ reducedBoundary μ Ω s) (φ : 𝓓((⊤ : Opens E), E)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      Integrable (fun y : Ω => ⟪φ (r⁻¹ • ((y : E) - x)), outerNormal μ Ω s x⟫)
          (variationMeasure μ Ω (s.indicator 1)) ∧
        r / r ^ finrank ℝ E * ∫ y : Ω, ⟪φ (r⁻¹ • ((y : E) - x)), outerNormal μ Ω s x⟫
            ∂variationMeasure μ Ω (s.indicator 1) - ε ≤
          ∫ y, divergenceCLM φ y * ((fun y => x + r • y) ⁻¹' s).indicator 1 y ∂μ := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  set lam := variationMeasure μ Ω (s.indicator 1)
  set ν := outerNormal μ Ω s x
  set n := finrank ℝ E
  -- `E` is nontrivial, since it contains the unit vector `ν`.
  have hν1 : ‖ν‖ = 1 := norm_outerNormal hx
  have : Nontrivial E := ⟨⟨ν, 0, fun h => by simp [h] at hν1⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel finrank_pos).symm⟩
  -- Bounds on `φ` and on its support.
  obtain ⟨M, hM⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  set M' := max M 0
  set R' := max R 1
  have hR' : 0 < R' := lt_max_of_lt_right one_pos
  set ω := μ.real (ball 0 1)
  set A := 4 * M' * n * ω * R' ^ m with hAdef
  set η := ε / (A + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hRr : Tendsto (fun r => R' * r) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_const.mul continuous_id).tendsto' 0 0
      (mul_zero R')).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => mul_pos hR' hr⟩
  filter_upwards [hRr.eventually ((eventually_setIntegral_norm_outerNormal_sub_le hx hη).and
      (eventually_variationMeasure_closedBall_le hx (t := 2) (by norm_num))),
    eventually_forall_tsupport_add_smul_mem (reducedBoundary_subset hx) φ,
    self_mem_nhdsWithin] with r ⟨⟨_, h1⟩, h2⟩ hΩ (hr : 0 < r)
  set S := ((↑) : Ω → E) ⁻¹' closedBall x (R' * r)
  obtain ⟨ψ, hψ, hdiv⟩ := TestFunction.exists_eq_comp φ hr.ne' hΩ
  simp_rw [← hψ]
  rw [(integrable_and_integral_divergenceCLM_mul_indicator_preimage hu hfin φ hr hdiv).2]
  have := Ω.isOpen.locallyCompactSpace
  refine ⟨ψ.integrable_inner_subtype (locallyIntegrable_const (μ := lam) ν), ?_⟩
  -- The field `ψ` vanishes off `S`.
  have hψS (y : Ω) (hy : y ∉ S) : ψ y = 0 := by
    rw [hψ]
    refine image_eq_zero_of_notMem_tsupport fun h => hy ?_
    rw [mem_preimage, mul_comm, ← inv_smul_sub_mem_closedBall_zero_iff hr]
    exact closedBall_subset_closedBall (le_max_left _ _) (hR h)
  have hSm : MeasurableSet S := (isClosed_closedBall.preimage continuous_subtype_val).measurableSet
  -- The perimeter measure of `S` is bounded by the upper density estimate.
  have hSfin : lam S ≠ ∞ := ne_top_of_le_ne_top (by finiteness) h2
  have hlamS : lam.real S ≤ 2 * (n * (R' * r) ^ (n - 1) * ω) := by
    have h := ENNReal.toReal_mono (by finiteness) h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  -- Replacing `ν` by `ν_s` in the pairing costs at most `M' ∫_S ‖ν_s - ν‖ d|Dχ_s|`.
  have hlow := integral_inner_sub_mul_setIntegral_le_integral_inner_outerNormal hSm hSfin
    (M := M') (fun y => by rw [hψ]; exact (hM _).trans (le_max_left _ _)) hψS ν
  have hrn : r / r ^ n * (R' * r) ^ (n - 1) = R' ^ m := by
    rw [hm, Nat.add_sub_cancel, pow_succ, mul_pow]
    field_simp
  have herr : r / r ^ n * (M' * ∫ y in S, ‖outerNormal μ Ω s y - ν‖ ∂lam) ≤ ε :=
    calc _ ≤ r / r ^ n * (M' * (2 * η * (2 * (n * (R' * r) ^ (n - 1) * ω)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h1.trans ?_)
            (le_max_right _ _)) (by positivity)
          exact mul_le_mul_of_nonneg_left hlamS (by positivity)
      _ = A * η := by
          rw [show r / r ^ n * (M' * (2 * η * (2 * (n * (R' * r) ^ (n - 1) * ω))))
              = 4 * M' * n * ω * η * (r / r ^ n * (R' * r) ^ (n - 1)) by ring, hrn, hAdef]
          ring
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  have h := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ r / r ^ n)
  rw [mul_sub] at h
  linarith

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
  filter_upwards [eventually_integrable_and_integral_inner_sub_le_integral_divergenceCLM hx φ hε,
    self_mem_nhdsWithin] with r ⟨_, h⟩ (hr : 0 < r)
  have h0 := mul_nonneg (by positivity : 0 ≤ r / r ^ finrank ℝ E)
    (integral_nonneg (μ := variationMeasure μ Ω (s.indicator 1)) fun y : Ω =>
      hφ (r⁻¹ • ((y : E) - x)))
  linarith

/-- If the blow-ups `(fun y => x + r i • y) ⁻¹' s` at a point of the reduced boundary, along radii
`r i → 0⁺`, converge locally in measure to a null-measurable set `F`, then their pairings with the
divergence of every test vector field converge to that of `F`. -/
private theorem tendsto_integral_divergenceCLM_mul_indicator_preimage
    (hx : x ∈ reducedBoundary μ Ω s) {ι : Type*} {l : Filter ι} {r : ι → ℝ}
    (hr : Tendsto r l (𝓝[>] 0)) {F : Set E} (hF : NullMeasurableSet F μ)
    (hconv : ∀ K, IsCompact K →
      Tendsto (fun i => μ ((((fun y => x + r i • y) ⁻¹' s) ∆ F) ∩ K)) l (𝓝 0))
    (φ : 𝓓((⊤ : Opens E), E)) :
    Tendsto (fun i => ∫ y, divergenceCLM φ y * ((fun y => x + r i • y) ⁻¹' s).indicator 1 y ∂μ) l
      (𝓝 (∫ y, divergenceCLM φ y * F.indicator 1 y ∂μ)) := by
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
    (hconv _ g.hasCompactSupport.isCompact) (.inr eNorm_ne_top)
  rw [mul_zero] at hK
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK
    (.of_forall fun _ => zero_le) (hint.mono fun i hi => ?_)
  rw [eDist_eq_eNorm_sub, ← integral_sub hi hJ]
  refine (eNorm_integral_le_lintegral_eNorm _).trans <|
    ((lintegral_mono fun y => ?_).trans_eq (lintegral_const_mul' _ _ eNorm_ne_top)).trans
      (mul_le_mul_right (lintegral_indicator_one_le _) _)
  rw [← mul_sub, eNorm_mul]
  by_cases hy : y ∈ tsupport g
  · have hgy : ‖g y‖ₑ ≤ ‖C‖ₑ := eNorm_le_iff_norm_le.2 ((hC y).trans (le_abs_self C))
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
  exact ge_of_tendsto (tendsto_integral_divergenceCLM_mul_indicator_preimage hx hr hF hconv φ)
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

/-- **Lower semicontinuity of the perimeter along the blow-ups.** If the blow-ups
`(fun y => x + r i • y) ⁻¹' s` at a point of the reduced boundary, along radii `r i → 0⁺`, converge
locally in measure to a null-measurable set `F`, then for every `R > 0`,

`P(F; ball 0 R) ≤ liminf_i P(s_{x, r i}; ball 0 R)`. -/
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
    _ = _ := liminf_congr (hagree.mono fun i hi =>
        perimeter_congr_of_inter_eq (Ω := ⟨ball 0 R, isOpen_ball⟩)
          (preimage_add_smul_inter_ball_eq hi.1 hi.2))

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
  (perimeter_ball_zero_le_liminf_of_tendsto_measure_symmDiff_inter hx hr hF hconv hR).trans <|
    liminf_le_of_frequently_le' (hr.eventually
      (eventually_perimeter_ball_zero_preimage_add_smul_le hx ht hR)).frequently

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

/-! ### The density of the perimeter measure at the reduced boundary -/

/-- The lower bound in the density of the perimeter: by lower semicontinuity of the perimeter
along the blow-ups, which converge to the half-space `{y | ⟪y, ν⟫ < 0}`,

`P({y | ⟪y, ν⟫ < 0}; ball 0 1) ≤ liminf_{r → 0⁺} P(s; ball x r) / r ^ (n - 1)`. -/
private theorem perimeter_ball_setOf_inner_lt_le_liminf (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary μ Ω s) :
    perimeter μ ⟨ball 0 1, isOpen_ball⟩ {y | ⟪y, outerNormal μ Ω s x⟫ < 0} ≤
      liminf (fun r => perimeter μ ⟨ball x r, isOpen_ball⟩ s /
        ENNReal.ofReal (r ^ (finrank ℝ E - 1))) (𝓝[>] 0) :=
  (perimeter_ball_zero_le_liminf_of_tendsto_measure_symmDiff_inter hx (r := fun r => r)
    tendsto_id (measurableSet_lt (by fun_prop) measurable_const).nullMeasurableSet
    (fun _ hK => tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx hK)
    one_pos).trans_eq (liminf_congr (eventually_nhdsWithin_of_forall fun _ hr => by
      rw [perimeter_ball_zero_preimage_add_smul_eq_div hr, mul_one]))

/-- **The perimeter measure of small balls is bounded by the blow-up pairings.** Let `φ` be a test
vector field on `E` with `⟪φ, ν⟫ ≥ 1` on `closedBall 0 1` and `⟪φ, ν⟫ ≥ 0` elsewhere, where
`ν = ν_s x`. For every `ε > 0` and every small `r > 0`,

`|Dχ_s|(closedBall x r) / r ^ (n - 1) ≤ ∫_{s_{x,r}} div φ dμ + ε`.

The left side is at most `r ^ (1 - n) ∫ ⟪φ((· - x) / r), ν⟫ d|Dχ_s|`, which is close to the
rescaled pairing on the right. -/
private theorem eventually_variationMeasure_closedBall_div_le_integral_divergenceCLM_mul_indicator
    (hx : x ∈ reducedBoundary μ Ω s) (φ : 𝓓((⊤ : Opens E), E))
    (hφν : ∀ y, (closedBall (0 : E) 1).indicator 1 y ≤ ⟪φ y, outerNormal μ Ω s x⟫)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) /
          ENNReal.ofReal (r ^ (finrank ℝ E - 1)) ≤
        ENNReal.ofReal
          (∫ y, divergenceCLM φ y * ((fun y => x + r • y) ⁻¹' s).indicator 1 y ∂μ + ε) := by
  set lam := variationMeasure μ Ω (s.indicator 1)
  set n := finrank ℝ E
  -- `E` is nontrivial, since it contains the unit vector `ν_s x`.
  have hν1 : ‖outerNormal μ Ω s x‖ = 1 := norm_outerNormal hx
  have : Nontrivial E := ⟨⟨outerNormal μ Ω s x, 0, fun h => by simp [h] at hν1⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel finrank_pos).symm⟩
  have hnm : n - 1 = m := by omega
  filter_upwards [eventually_integrable_and_integral_inner_sub_le_integral_divergenceCLM hx φ hε,
    eventually_variationMeasure_closedBall_le hx (t := 2) (by norm_num),
    self_mem_nhdsWithin] with r ⟨hint, h⟩ h2 (hr : 0 < r)
  set S₁ := ((↑) : Ω → E) ⁻¹' closedBall x r
  have hS₁m : MeasurableSet S₁ :=
    (isClosed_closedBall.preimage continuous_subtype_val).measurableSet
  have hS₁fin : lam S₁ ≠ ∞ := ne_top_of_le_ne_top (by finiteness) h2
  -- `|Dχ_s|(S₁) ≤ ∫ ⟪φ((· - x) / r), ν⟫ d|Dχ_s|`, since `y ∈ S₁` exactly when
  -- `(y - x) / r ∈ closedBall 0 1`.
  have hS₁ : lam.real S₁ ≤ ∫ y : Ω, ⟪φ (r⁻¹ • ((y : E) - x)), outerNormal μ Ω s x⟫ ∂lam := by
    rw [← integral_indicator_one hS₁m]
    refine integral_mono ((integrableOn_const hS₁fin).integrable_indicator hS₁m) hint
      fun y => (le_of_eq ?_).trans (hφν _)
    have hS₁eq : S₁ = (fun y : Ω => r⁻¹ • ((y : E) - x)) ⁻¹' closedBall 0 1 := by
      ext z
      simp only [S₁, mem_preimage, inv_smul_sub_mem_closedBall_zero_iff hr, mul_one]
    rw [hS₁eq]
    exact indicator_comp_right (fun y : Ω => r⁻¹ • ((y : E) - x)) (g := 1)
  have hr' : r / r ^ n * r ^ m = 1 := by
    rw [hm, pow_succ]
    field_simp
  rw [← ofReal_measureReal hS₁fin, ← ENNReal.ofReal_div_of_pos (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hnm, div_le_iff₀ (by positivity)]
  calc lam.real S₁ ≤ ∫ y : Ω, ⟪φ (r⁻¹ • ((y : E) - x)), outerNormal μ Ω s x⟫ ∂lam := hS₁
    _ = r / r ^ n * (∫ y : Ω, ⟪φ (r⁻¹ • ((y : E) - x)), outerNormal μ Ω s x⟫ ∂lam) * r ^ m := by
        rw [mul_right_comm, hr', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- The upper bound in the density of the perimeter measure, for every `ρ > 1`:

`limsup_{r → 0⁺} |Dχ_s|(closedBall x r) / r ^ (n - 1) ≤ P({y | ⟪y, ν⟫ < 0}; ball 0 ρ)`.

Test with `θ ν`, for a bump `θ` equal to one on `closedBall 0 1` and supported in `ball 0 ρ`: the
blow-up pairings `∫_{s_{x,r}} div (θ ν)` converge to `∫_H div (θ ν) ≤ P(H; ball 0 ρ)`. -/
private theorem limsup_variationMeasure_closedBall_div_le (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary μ Ω s) {ρ : ℝ} (hρ : 1 < ρ) :
    limsup (fun r => variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) /
        ENNReal.ofReal (r ^ (finrank ℝ E - 1))) (𝓝[>] 0) ≤
      perimeter μ ⟨ball 0 ρ, isOpen_ball⟩ {y | ⟪y, outerNormal μ Ω s x⟫ < 0} := by
  set ν := outerNormal μ Ω s x
  set H := {y : E | ⟪y, ν⟫ < 0}
  have hν1 : ‖ν‖ = 1 := norm_outerNormal hx
  -- The test field `φ = θ ν`, where the bump `θ` is one on `closedBall 0 1` and vanishes off
  -- `ball 0 ρ'` for some `ρ' ∈ (1, ρ)`.
  obtain ⟨ρ', hρ', hρ'ρ⟩ := exists_between hρ
  let θ : ContDiffBump (0 : E) := ⟨1, ρ', one_pos, hρ'⟩
  let φ : 𝓓((⊤ : Opens E), E) :=
    ⟨fun y => θ y • ν, θ.contDiff.smul contDiff_const, θ.hasCompactSupport.smul_right, by simp⟩
  have hφ (y : E) : φ y = θ y • ν := by simp only [φ, coe_mk]
  have hφ1 (y : E) : ‖φ y‖ ≤ 1 := by
    rw [hφ, norm_smul, hν1, mul_one, Real.norm_of_nonneg θ.nonneg]
    exact θ.le_one
  have hφν (y : E) : (closedBall (0 : E) 1).indicator 1 y ≤ ⟪φ y, ν⟫ := by
    rw [hφ, real_inner_smul_left, real_inner_self_eq_norm_sq, hν1, one_pow, mul_one]
    by_cases hy : y ∈ closedBall (0 : E) 1
    · rw [indicator_of_mem hy, Pi.one_apply]
      exact (θ.one_of_mem_closedBall hy).ge
    · rw [indicator_of_notMem hy]
      exact θ.nonneg
  have hφS : tsupport φ ⊆ ball 0 ρ := by
    have hcoe : (φ : E → E) = fun y => θ y • ν := funext hφ
    rw [hcoe]
    exact (tsupport_smul_subset_left _ _).trans (θ.tsupport_eq.trans_subset
      (closedBall_subset_ball hρ'ρ))
  -- The blow-up pairings converge to `∫_H div φ ≤ P(H; ball 0 ρ)`.
  set J := ∫ y, divergenceCLM φ y * H.indicator 1 y ∂μ
  have hlim := tendsto_integral_divergenceCLM_mul_indicator_preimage hx (r := fun r => r)
    tendsto_id (measurableSet_lt (by fun_prop) measurable_const).nullMeasurableSet
    (fun _ hK => tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx hK) φ
  have hpair : ENNReal.ofReal J ≤ perimeter μ ⟨ball 0 ρ, isOpen_ball⟩ H := by
    rw [perimeter_def]
    exact ofReal_integral_le_totalVariationOn_of_tsupport_subset φ hφ1 hφS
  -- Let `r → 0⁺` in the bound by the pairings plus `ε`, and then `ε → 0⁺`.
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  calc _ ≤ limsup (fun r => ENNReal.ofReal (∫ y, divergenceCLM φ y *
          ((fun y => x + r • y) ⁻¹' s).indicator 1 y ∂μ + ε)) (𝓝[>] 0) :=
        limsup_le_limsup
          (eventually_variationMeasure_closedBall_div_le_integral_divergenceCLM_mul_indicator hx
            φ hφν (by exact_mod_cast hε))
    _ = ENNReal.ofReal (J + ε) :=
        ((ENNReal.continuous_ofReal.tendsto _).comp (hlim.add_const _)).limsup_eq
    _ ≤ ENNReal.ofReal J + ε := by simpa using ENNReal.ofReal_add_le (p := J) (q := ε)
    _ ≤ perimeter μ ⟨ball 0 ρ, isOpen_ball⟩ H + ε := add_le_add_left hpair _

/-- The upper bound in the density of the perimeter measure:

`limsup_{r → 0⁺} |Dχ_s|(closedBall x r) / r ^ (n - 1) ≤ P({y | ⟪y, ν⟫ < 0}; ball 0 1)`.

The half-space is invariant under positive dilations, so its perimeter in `ball 0 ρ` is
`ρ ^ (n - 1)` times its perimeter in the unit ball, and the bound follows from
`limsup_variationMeasure_closedBall_div_le` by letting `ρ → 1⁺`. -/
private theorem limsup_variationMeasure_closedBall_div_le_perimeter_ball_one
    (hn : 2 ≤ finrank ℝ E) (hx : x ∈ reducedBoundary μ Ω s) :
    limsup (fun r => variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) /
        ENNReal.ofReal (r ^ (finrank ℝ E - 1))) (𝓝[>] 0) ≤
      perimeter μ ⟨ball 0 1, isOpen_ball⟩ {y | ⟪y, outerNormal μ Ω s x⟫ < 0} := by
  set L := limsup (fun r => variationMeasure μ Ω (s.indicator 1)
    (((↑) : Ω → E) ⁻¹' closedBall x r) / ENNReal.ofReal (r ^ (finrank ℝ E - 1))) (𝓝[>] 0)
  set H := {y : E | ⟪y, outerNormal μ Ω s x⟫ < 0}
  have hscale (ρ : ℝ) (hρ : 1 < ρ) :
      ENNReal.ofReal (ρ / ρ ^ finrank ℝ E) * L ≤ perimeter μ ⟨ball 0 1, isOpen_ball⟩ H := by
    have hρ0 : 0 < ρ := zero_lt_one.trans hρ
    have hpre : (fun y => (0 : E) + ρ • y) ⁻¹' H = H := by
      ext y
      simp only [H, mem_preimage, mem_ofPred_eq, zero_add, real_inner_smul_left]
      exact ⟨fun h => neg_of_mul_neg_right h hρ0.le, mul_neg_of_pos_of_neg hρ0⟩
    have h := perimeter_ball_zero_preimage_add_smul (μ := μ) (s := H) (x := 0) hρ0 1
    rw [hpre, mul_one] at h
    rw [h]
    exact mul_le_mul_right (limsup_variationMeasure_closedBall_div_le hn hx hρ) _
  have hlim : Tendsto (fun ρ => ENNReal.ofReal (ρ / ρ ^ finrank ℝ E) * L) (𝓝[>] 1) (𝓝 L) := by
    have hc : ContinuousAt (fun ρ : ℝ => ρ / ρ ^ finrank ℝ E) 1 :=
      continuousAt_id.div (continuousAt_id.pow _) (by simp)
    have h : Tendsto (fun ρ : ℝ => ρ / ρ ^ finrank ℝ E) (𝓝[>] 1) (𝓝 1) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h) (.inl (by simp))
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall hscale)

/-- **The density of the perimeter measure at the reduced boundary.** Let `E` have dimension
`n ≥ 2` and let `μ` be an additive Haar measure. At every point `x` of the reduced boundary of `s`
in `Ω`, with outer normal `ν = ν_s x`,

`|Dχ_s|(closedBall x r) / r ^ (n - 1) → P({y | ⟪y, ν⟫ < 0}; ball 0 1)`     as `r → 0⁺`,

the perimeter of the limiting half-space of the blow-ups in the unit ball. For Lebesgue measure
this is the volume `ω_{n-1}` of the unit ball of `ℝ^(n-1)`
(`TauCeti.tendsto_variationMeasure_closedBall_div_volume_closedBall`). -/
theorem tendsto_variationMeasure_closedBall_div (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary μ Ω s) :
    Tendsto (fun r => variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) /
        ENNReal.ofReal (r ^ (finrank ℝ E - 1))) (𝓝[>] 0)
      (𝓝 (perimeter μ ⟨ball 0 1, isOpen_ball⟩ {y | ⟪y, outerNormal μ Ω s x⟫ < 0})) :=
  tendsto_of_le_liminf_of_limsup_le
    ((perimeter_ball_setOf_inner_lt_le_liminf hn hx).trans
      (liminf_le_liminf
        ((eventually_perimeter_ball_le_variationMeasure_closedBall_of_mem_reducedBoundary hx).mono
          fun _ h => ENNReal.div_le_div_right h _)))
    (limsup_variationMeasure_closedBall_div_le_perimeter_ball_one hn hx)

/-- **The density of the perimeter at the reduced boundary.** Let `E` have dimension `n ≥ 2` and
let `μ` be an additive Haar measure. At every point `x` of the reduced boundary of `s` in `Ω`, with
outer normal `ν = ν_s x`,

`P(s; ball x r) / r ^ (n - 1) → P({y | ⟪y, ν⟫ < 0}; ball 0 1)`     as `r → 0⁺`.

Equivalently, the perimeters `P(s_{x,r}; ball 0 1)` of the blow-ups in the unit ball converge to
that of their limiting half-space. -/
theorem tendsto_perimeter_ball_div (hn : 2 ≤ finrank ℝ E) (hx : x ∈ reducedBoundary μ Ω s) :
    Tendsto (fun r => perimeter μ ⟨ball x r, isOpen_ball⟩ s /
        ENNReal.ofReal (r ^ (finrank ℝ E - 1))) (𝓝[>] 0)
      (𝓝 (perimeter μ ⟨ball 0 1, isOpen_ball⟩ {y | ⟪y, outerNormal μ Ω s x⟫ < 0})) :=
  tendsto_of_le_liminf_of_limsup_le (perimeter_ball_setOf_inner_lt_le_liminf hn hx)
    ((limsup_le_limsup
        ((eventually_perimeter_ball_le_variationMeasure_closedBall_of_mem_reducedBoundary hx).mono
          fun _ h => ENNReal.div_le_div_right h _)).trans
      (limsup_variationMeasure_closedBall_div_le_perimeter_ball_one hn hx))

/-- **The perimeter measure has density one with respect to `Hⁿ⁻¹` at the reduced boundary.** Let
`F` have dimension `n ≥ 2`, with Lebesgue measure. At every point `x` of the reduced boundary of
`s` in `Ω`,

`|Dχ_s|(closedBall x r) / (ω_{n-1} r ^ (n - 1)) → 1`     as `r → 0⁺`,

where `ω_{n-1} r ^ (n - 1)` is the volume of a closed ball of radius `r` in `ℝ^(n-1)`, the
normalization of `μHE[n - 1]`. -/
theorem tendsto_variationMeasure_closedBall_div_volume_closedBall {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] {Ω : Opens F} {s : Set F} {x : F} (hn : 2 ≤ finrank ℝ F)
    (hx : x ∈ reducedBoundary volume Ω s) :
    Tendsto (fun r =>
      variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → F) ⁻¹' closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) r)) (𝓝[>] 0) (𝓝 1) := by
  set ω := volume (ball (0 : EuclideanSpace ℝ (Fin (finrank ℝ F - 1))) 1)
  have hω0 : ω ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  -- The half-space has perimeter `ω_{n-1}` in the unit ball.
  have hP : perimeter volume ⟨ball 0 1, isOpen_ball⟩ {y | ⟪y, outerNormal volume Ω s x⟫ < 0} =
      ω := by
    simpa using perimeter_ball_setOf_inner_lt (norm_outerNormal hx) (0 : F) one_pos
  have h := ENNReal.Tendsto.div_const (tendsto_variationMeasure_closedBall_div hn hx) (.inr hω0)
  rw [hP, ENNReal.div_self hω0 hωtop] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
  dsimp only
  rw [Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin, div_eq_mul_inv,
    div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (.inr hωtop) (.inl ENNReal.ofReal_ne_top),
    mul_assoc]

end TauCeti
