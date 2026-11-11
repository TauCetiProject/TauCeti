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

* `TauCeti.tendsto_perimeter_ball_zero_preimage_add_smul`: in dimension `n ≥ 2`, the perimeters
  of the blow-ups converge to that of the half-space,
  `P(s_{x,r}; ball 0 R) → P({y | ⟪y, ν⟫ < 0}; ball 0 R)` for every `R > 0`. Lower semicontinuity
  gives the lower bound. For the upper bound, a cutoff multiple `φ` of `ν` equal to `ν` on
  `ball 0 R` has `P(s_{x,r}; ball 0 R) ≤ ∫_{s_{x,r}} div φ + o(1)` by the concentration of the
  normal, and the right side converges to `∫_{y | ⟪y, ν⟫ < 0} div φ`, at most the perimeter of the
  half-space in a slightly larger ball.
* `TauCeti.tendsto_ofReal_div_pow_mul_perimeter_ball`: equivalently,
  `P(s; ball x r) / r ^ (n - 1) → P({y | ⟪y, ν⟫ < 0}; ball 0 1)`, the density of the perimeter
  measure at points of the reduced boundary. For Lebesgue measure the limit is the volume
  `ω_{n-1}` of the unit ball of `ℝ^(n-1)`.

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
  have hA : 0 ≤ A := by positivity
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
  rw [(integrable_and_integral_divergenceCLM_mul_indicator_preimage hu hfin φ hr hdiv).2]
  -- The field `ψ` vanishes off `S`.
  have hψS (y : Ω) (hy : y ∉ S) : ψ y = 0 := by
    rw [hψ]
    refine image_eq_zero_of_notMem_tsupport fun h => hy ?_
    have h' : ‖r⁻¹ • ((y : E) - x)‖ ≤ R' :=
      (mem_closedBall_zero_iff.1 (hR h)).trans (le_max_left _ _)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_mul_le_iff₀ hr] at h'
    rw [mem_preimage, mem_closedBall, dist_eq_norm]
    linarith
  have hSm : MeasurableSet S := (isClosed_closedBall.preimage continuous_subtype_val).measurableSet
  -- The perimeter measure of `S` is bounded by the upper density estimate.
  have hSfin : lam S ≠ ∞ := ne_top_of_le_ne_top (by finiteness) h2
  have hlamS : lam.real S ≤ 2 * (n * (R' * r) ^ (n - 1) * ω) := by
    have h := ENNReal.toReal_mono (by finiteness) h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  -- Replacing `ν_s` by `ν` in the pairing costs at most `M' ∫_S ‖ν_s - ν‖ d|Dχ_s|`.
  have hlow := neg_mul_setIntegral_le_integral_inner_outerNormal hSm hSfin (M := M')
    (fun y => by rw [hψ]; exact (hM _).trans (le_max_left _ _)) (fun y => by rw [hψ]; exact hφ _)
    hψS
  have hrn : r / r ^ n * (R' * r) ^ (n - 1) = R' ^ m := by
    rw [hm, Nat.add_sub_cancel, pow_succ, mul_pow]
    field_simp
  calc -ε ≤ -(A * η) := by
        rw [neg_le_neg_iff, mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
    _ = r / r ^ n * -(M' * (2 * η * (2 * (n * (R' * r) ^ (n - 1) * ω)))) := by
        rw [mul_neg, neg_inj, show r / r ^ n * (M' * (2 * η * (2 * (n * (R' * r) ^ (n - 1) * ω))))
            = 4 * M' * n * ω * η * (r / r ^ n * (R' * r) ^ (n - 1)) by ring, hrn, hAdef]
        ring
    _ ≤ r / r ^ n * ∫ y, ⟪ψ y, outerNormal μ Ω s y⟫ ∂lam := by
        refine mul_le_mul_of_nonneg_left (le_trans ?_ hlow) (by positivity)
        rw [neg_le_neg_iff]
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (le_max_right _ _)
        exact mul_le_mul_of_nonneg_left hlamS (by positivity)

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
      t * ENNReal.ofReal (finrank ℝ E * R ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
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
    _ ≤ _ := by
        refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
        filter_upwards [hagree,
          hr.eventually (eventually_perimeter_ball_zero_preimage_add_smul_le hx ht hR)]
          with i hi hle
        rwa [perimeter_congr_of_inter_eq (Ω := ⟨ball 0 R, isOpen_ball⟩)
          (preimage_add_smul_inter_ball_eq hi.1 hi.2)]

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

omit [μ.IsAddHaarMeasure] in
/-- The perimeter measure of a set `B ⊆ S` is at most the pairing of `Dχ_s` with a field `ψ` that
is a multiple `a • ν`, `0 ≤ a ≤ 1`, of `ν = ν_s x`, equals `ν` on `B` and vanishes off `S`, plus
the error `∫_S ‖ν_s - ν‖ d|Dχ_s|`. -/
private theorem measureReal_le_integral_inner_outerNormal_add {ψ : 𝓓(Ω, E)} {B S : Set Ω}
    (hBm : MeasurableSet B) (hSm : MeasurableSet S) (hBS : B ⊆ S)
    (hSfin : variationMeasure μ Ω (s.indicator 1) S ≠ ∞)
    (hψ : ∀ y, ∃ a ∈ Icc (0 : ℝ) 1, ψ y = a • outerNormal μ Ω s x)
    (hψB : ∀ y : Ω, y ∈ B → ψ y = outerNormal μ Ω s x) (hψS : ∀ y : Ω, y ∉ S → ψ y = 0)
    (hν : ‖outerNormal μ Ω s x‖ = 1) :
    (variationMeasure μ Ω (s.indicator 1)).real B ≤
      ∫ y, ⟪ψ y, outerNormal μ Ω s y⟫ ∂variationMeasure μ Ω (s.indicator 1) +
        ∫ y in S, ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖
          ∂variationMeasure μ Ω (s.indicator 1) := by
  set lam := variationMeasure μ Ω (s.indicator 1)
  set ν := outerNormal μ Ω s x
  have hBfin : lam B ≠ ∞ := ne_top_of_le_ne_top hSfin (measure_mono hBS)
  have hint : Integrable (fun y : Ω => ⟪ψ y, outerNormal μ Ω s y⟫) lam :=
    (integrable_inner_polarDensity ψ.continuous ψ.hasCompactSupport ψ.tsupport_subset).neg.congr
      (by filter_upwards [ae_outerNormal_eq] with y hy; simp [hy, inner_neg_right])
  have hg : IntegrableOn (fun y : Ω => ‖outerNormal μ Ω s y - ν‖) S lam :=
    ((integrableOn_outerNormal hSfin).sub (integrableOn_const hSfin)).norm
  rw [← integral_indicator hSm, ← integral_add hint (hg.integrable_indicator hSm),
    ← integral_indicator_one hBm]
  refine integral_mono_ae ((integrable_indicator_iff hBm).2 (integrableOn_const hBfin))
    (hint.add (hg.integrable_indicator hSm)) ?_
  filter_upwards [ae_mem_reducedBoundary] with y hy
  have hνy : ‖outerNormal μ Ω s y‖ = 1 := norm_outerNormal hy
  -- For unit vectors, `⟪a • ν, ν_s⟫ + ‖ν_s - ν‖ ≥ a`, since `⟪ν, ν_s⟫ ≥ 1 - ‖ν_s - ν‖`.
  have hkey : 1 - ‖outerNormal μ Ω s y - ν‖ ≤ ⟪ν, outerNormal μ Ω s y⟫ := by
    have h := abs_real_inner_le_norm ν (outerNormal μ Ω s y - ν)
    have h' : ⟪ν, outerNormal μ Ω s y⟫ = 1 + ⟪ν, outerNormal μ Ω s y - ν⟫ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq, hν]
      ring
    rw [hν, one_mul] at h
    linarith [neg_abs_le ⟪ν, outerNormal μ Ω s y - ν⟫]
  have hnorm := norm_nonneg (outerNormal μ Ω s y - ν)
  obtain ⟨a, ⟨ha0, ha1⟩, hψa⟩ := hψ y
  by_cases hyB : y ∈ B
  · rw [indicator_of_mem hyB, indicator_of_mem (hBS hyB), hψB y hyB, Pi.one_apply]
    linarith
  rw [indicator_of_notMem hyB]
  by_cases hyS : y ∈ S
  · rw [indicator_of_mem hyS, hψa, real_inner_smul_left]
    nlinarith
  · simp [indicator_of_notMem hyS, hψS y hyS]

/-- The key estimate for the upper bound on the perimeter of the blow-ups. Let `x` be a point of
the reduced boundary of `s` in `Ω`, with outer normal `ν`, let `0 < R` and let `φ` be a test
vector field that is a multiple `a • ν`, `0 ≤ a ≤ 1`, of `ν`, equals `ν` on `ball 0 R` and has
support in `closedBall 0 R'`, `R ≤ R'`. Then for every `ε > 0` and every small `r > 0`,

`P(s_{x,r}; ball 0 R) ≤ ∫_{s_{x,r}} div φ dμ + ε`. -/
private theorem eventually_perimeter_ball_zero_preimage_add_smul_le_integral
    (hx : x ∈ reducedBoundary μ Ω s) {R R' : ℝ} (hR : 0 < R) (hRR' : R ≤ R')
    (φ : 𝓓((⊤ : Opens E), E))
    (hφ : ∀ y, ∃ a ∈ Icc (0 : ℝ) 1, φ y = a • outerNormal μ Ω s x)
    (hφR : ∀ y ∈ ball (0 : E) R, φ y = outerNormal μ Ω s x)
    (hφR' : tsupport φ ⊆ closedBall 0 R') {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s) ≤
      ENNReal.ofReal
        (∫ y, divergenceCLM φ y * ((fun y => x + r • y) ⁻¹' s).indicator 1 y ∂μ + ε) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  set lam := variationMeasure μ Ω (s.indicator 1)
  set ν := outerNormal μ Ω s x
  set n := finrank ℝ E
  have hν1 : ‖ν‖ = 1 := norm_outerNormal hx
  have : Nontrivial E := ⟨⟨ν, 0, fun h => by simp [h] at hν1⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel finrank_pos).symm⟩
  have hR' : 0 < R' := hR.trans_le hRR'
  set ω := μ.real (ball 0 1)
  set A := 4 * n * ω * R' ^ m with hAdef
  have hA : 0 ≤ A := by positivity
  set η := ε / (A + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  have hRr : Tendsto (fun r => R' * r) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_const.mul continuous_id).tendsto' 0 0
      (mul_zero R')).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => mul_pos hR' hr⟩
  filter_upwards [hRr.eventually ((eventually_setIntegral_norm_outerNormal_sub_le hx hη).and
      (eventually_variationMeasure_closedBall_le hx (t := 2) (by norm_num))),
    eventually_forall_tsupport_add_smul_mem (reducedBoundary_subset hx) φ,
    Ioo_mem_nhdsGT (div_pos hδ hR)] with r ⟨⟨_, h1⟩, h2⟩ hΩ hr
  have hr0 : 0 < r := hr.1
  have hballΩ : ball x (r * R) ⊆ Ω := (ball_subset_ball ((lt_div_iff₀ hR).1 hr.2).le).trans hδΩ
  set B := ((↑) : Ω → E) ⁻¹' ball x (r * R)
  set S := ((↑) : Ω → E) ⁻¹' closedBall x (R' * r)
  obtain ⟨ψ, hψ, hdiv⟩ := TestFunction.exists_eq_comp φ hr0.ne' hΩ
  rw [(integrable_and_integral_divergenceCLM_mul_indicator_preimage hu hfin φ hr0 hdiv).2,
    perimeter_ball_zero_preimage_add_smul hr0, perimeter_def,
    ← variationMeasure_preimage_coe hu hfin (U := ⟨ball x (r * R), isOpen_ball⟩) hballΩ]
  -- The rescaled field `ψ` equals `ν` on `B` and vanishes off `S`.
  have hψB (y : Ω) (hy : y ∈ B) : ψ y = ν := by
    rw [hψ]
    refine hφR _ ?_
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr0.le),
      inv_mul_lt_iff₀ hr0, ← dist_eq_norm]
    exact hy
  have hψS (y : Ω) (hy : y ∉ S) : ψ y = 0 := by
    rw [hψ]
    refine image_eq_zero_of_notMem_tsupport fun h => hy ?_
    have h' := mem_closedBall_zero_iff.1 (hφR' h)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr0.le), inv_mul_le_iff₀ hr0] at h'
    rw [mem_preimage, mem_closedBall, dist_eq_norm]
    linarith
  have hSm : MeasurableSet S := (isClosed_closedBall.preimage continuous_subtype_val).measurableSet
  have hBm : MeasurableSet B := (isOpen_ball.preimage continuous_subtype_val).measurableSet
  have hBS : B ⊆ S := fun y hy => by
    have hy' : dist (y : E) x < r * R := hy
    have : r * R ≤ R' * r := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hRR' hr0.le
    exact le_of_lt (hy'.trans_le this)
  -- The perimeter measure of `S` is bounded by the upper density estimate.
  have hSfin : lam S ≠ ∞ := ne_top_of_le_ne_top (by finiteness) h2
  have hBfin : lam B ≠ ∞ := ne_top_of_le_ne_top hSfin (measure_mono hBS)
  have hlamS : lam.real S ≤ 2 * (n * (R' * r) ^ (n - 1) * ω) := by
    have h := ENNReal.toReal_mono (by finiteness) h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  have hmain := measureReal_le_integral_inner_outerNormal_add hBm hSm hBS hSfin
    (fun y => by rw [hψ]; exact hφ _) hψB hψS hν1
  have hrn : r / r ^ n * (R' * r) ^ (n - 1) = R' ^ m := by
    rw [hm, Nat.add_sub_cancel, pow_succ, mul_pow]
    field_simp
  have herr : r / r ^ n * ∫ y in S, ‖outerNormal μ Ω s y - ν‖ ∂lam ≤ ε := by
    calc r / r ^ n * ∫ y in S, ‖outerNormal μ Ω s y - ν‖ ∂lam
        ≤ r / r ^ n * (2 * η * (2 * (n * (R' * r) ^ (n - 1) * ω))) :=
          mul_le_mul_of_nonneg_left
            (h1.trans (mul_le_mul_of_nonneg_left hlamS (by positivity))) (by positivity)
      _ = A * η := by
          rw [show r / r ^ n * (2 * η * (2 * (n * (R' * r) ^ (n - 1) * ω))) =
            4 * n * ω * η * (r / r ^ n * (R' * r) ^ (n - 1)) by ring, hrn, hAdef]
          ring
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  change ENNReal.ofReal (r / r ^ n) * lam B ≤ _
  rw [← ofReal_measureReal hBfin, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ r / r ^ n)
  rw [mul_add] at this
  linarith

/-- The half-space `{y | ⟪y, ν⟫ < 0}` is a cone, so its perimeter in `ball 0 (t * R)` is
`t ^ (n - 1)` times its perimeter in `ball 0 R`, `n = dim E`. -/
private theorem perimeter_ball_zero_mul_setOf_inner_lt [Nontrivial E] (ν : E) {t : ℝ} (ht : 0 < t)
    (R : ℝ) :
    perimeter μ ⟨ball 0 (t * R), isOpen_ball⟩ {y | ⟪y, ν⟫ < 0} =
      ENNReal.ofReal (t ^ (finrank ℝ E - 1)) *
        perimeter μ ⟨ball 0 R, isOpen_ball⟩ {y | ⟪y, ν⟫ < 0} := by
  have hpre : (fun y => (0 : E) + t • y) ⁻¹' {y : E | ⟪y, ν⟫ < 0} = {y | ⟪y, ν⟫ < 0} := by
    ext y
    simp only [zero_add, mem_preimage, mem_ofPred_eq, real_inner_smul_left]
    exact ⟨fun h => neg_of_mul_neg_right h ht.le, fun h => mul_neg_of_pos_of_neg ht h⟩
  have h := perimeter_ball_zero_preimage_add_smul (μ := μ) (s := {y : E | ⟪y, ν⟫ < 0})
    (x := 0) ht R
  rw [hpre] at h
  obtain ⟨m, hm⟩ : ∃ m, finrank ℝ E = m + 1 := ⟨_, (Nat.sub_add_cancel finrank_pos).symm⟩
  rw [h, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hm, Nat.add_sub_cancel,
    show t ^ m * (t / t ^ (m + 1)) = 1 by field_simp; ring, ENNReal.ofReal_one, one_mul]

/-- **The perimeter of the blow-ups converges to that of the half-space.** Let `E` have dimension
`n ≥ 2`, let `μ` be an additive Haar measure, and let `x` be a point of the reduced boundary of `s`
in `Ω`, with outer normal `ν = ν_s x`. For every `R > 0`, as `r → 0⁺`,

`P(s_{x,r}; ball 0 R) → P({y | ⟪y, ν⟫ < 0}; ball 0 R)`.

Lower semicontinuity of the perimeter along the blow-up theorem gives the lower bound. For the
upper bound, test `Dχ_{s_{x,r}}` with a cutoff multiple of `ν` that equals `ν` on `ball 0 R`: the
concentration of the outer normal at `x` makes the pairing almost equal to the perimeter of
`s_{x,r}` in `ball 0 R`, and the pairing converges to that of the half-space. -/
theorem tendsto_perimeter_ball_zero_preimage_add_smul (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary μ Ω s) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ => perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s))
      (𝓝[>] 0)
      (𝓝 (perimeter μ ⟨ball 0 R, isOpen_ball⟩ {y | ⟪y, outerNormal μ Ω s x⟫ < 0})) := by
  set ν := outerNormal μ Ω s x
  set H := {y : E | ⟪y, ν⟫ < 0}
  set P : ℝ → ℝ≥0∞ := fun r =>
    perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s)
  have hν1 : ‖ν‖ = 1 := norm_outerNormal hx
  have : Nontrivial E := ⟨⟨ν, 0, fun h => by simp [h] at hν1⟩⟩
  have hHm : MeasurableSet H := measurableSet_lt (by fun_prop) measurable_const
  have hconv (K : Set E) (hK : IsCompact K) :=
    tendsto_measure_preimage_add_smul_symmDiff_setOf_inner_lt_inter hn hx hK
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝[>] 0) := tendsto_id
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · -- Lower semicontinuity, after replacing `s` by the null-measurable set `s ∩ Ω`.
    obtain ⟨δ, hδ, hδΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
    have hsΩ : NullMeasurableSet (s ∩ Ω) μ := nullMeasurableSet_inter_of_mem_reducedBoundary hx
    have hagree : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ s ∩ Ω ∩ ball x (r * R) = s ∩ ball x (r * R) := by
      filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r hr
      refine ⟨hr.1, ?_⟩
      rw [inter_assoc, inter_eq_right.2
        ((ball_subset_ball ((lt_div_iff₀ hR).1 hr.2).le).trans hδΩ)]
    calc perimeter μ ⟨ball 0 R, isOpen_ball⟩ H
        ≤ liminf (fun r => perimeter μ ⟨ball 0 R, isOpen_ball⟩
            ((fun y => x + r • y) ⁻¹' (s ∩ Ω))) (𝓝[>] 0) :=
          perimeter_le_liminf (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) =>
            hsΩ.preimage (μ.quasiMeasurePreserving_add_smul x hr.ne')) hHm.nullMeasurableSet
            fun K hK hKR => (hconv K hK).congr' (hagree.mono fun r hr =>
              congrArg μ (preimage_add_smul_symmDiff_inter_eq hr.1 hr.2.symm hKR))
      _ = liminf P (𝓝[>] 0) :=
          liminf_congr (hagree.mono fun r hr => perimeter_congr_of_inter_eq
            (Ω := ⟨ball 0 R, isOpen_ball⟩) (preimage_add_smul_inter_ball_eq hr.1 hr.2))
  -- The upper bound `P(H; ball 0 (t R))` for every `t > 1`.
  have hPH (t : ℝ) (ht : 1 < t) : limsup P (𝓝[>] 0) ≤
      ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * perimeter μ ⟨ball 0 R, isOpen_ball⟩ H := by
    rw [← perimeter_ball_zero_mul_setOf_inner_lt ν (by linarith) R]
    set R' := t * R
    have hRR' : R < R' := by simp only [R']; nlinarith
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < ε := hε
    -- A cutoff multiple of `ν`, equal to `ν` on `closedBall 0 R`, with support in `ball 0 R'`.
    obtain ⟨χ, hχ1, hχ01⟩ := exists_eventually_eq_one (n := ⊤)
      (Ω := ⟨ball (0 : E) R', isOpen_ball⟩) (isCompact_closedBall 0 R)
      (closedBall_subset_ball hRR')
    have hsupp : tsupport (fun y => χ y • ν) ⊆ ball 0 R' :=
      (tsupport_smul_subset_left _ _).trans χ.tsupport_subset
    let φ' : 𝓓((⟨ball (0 : E) R', isOpen_ball⟩ : Opens E), E) :=
      ⟨fun y => χ y • ν, χ.contDiff.smul contDiff_const, χ.hasCompactSupport.smul_right, hsupp⟩
    let φ : 𝓓((⊤ : Opens E), E) :=
      ⟨fun y => χ y • ν, χ.contDiff.smul contDiff_const, χ.hasCompactSupport.smul_right,
        by simp⟩
    have hφ (y : E) : ∃ a ∈ Icc (0 : ℝ) 1, φ y = a • ν := ⟨χ y, hχ01 y, rfl⟩
    have hφR (y : E) (hy : y ∈ ball (0 : E) R) : φ y = ν := by
      simp [φ, hχ1.self_of_nhdsSet y (ball_subset_closedBall hy)]
    have hlim := tendsto_integral_divergenceCLM_mul_indicator_of_tendsto_measure_symmDiff_inter
      hx hr hHm.nullMeasurableSet hconv φ
    -- The pairing with the half-space is at most its perimeter in `ball 0 R'`.
    have hHle : ENNReal.ofReal (∫ y, divergenceCLM φ y * H.indicator 1 y ∂μ) ≤
        perimeter μ ⟨ball 0 R', isOpen_ball⟩ H := by
      rw [perimeter_eq_iSup hHm.nullMeasurableSet]
      refine le_iSup₂_of_le (f := fun (ψ : 𝓓((⟨ball (0 : E) R', isOpen_ball⟩ : Opens E), E))
        (_ : ∀ y, ‖ψ y‖ ≤ 1) => ENNReal.ofReal (∫ y in H, divergenceCLM ψ y ∂μ)) φ'
        (fun y => ?_) (le_of_eq ?_)
      · simp only [φ', coe_mk, norm_smul, hν1, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (hχ01 y).1]
        exact (hχ01 y).2
      · congr 1
        rw [← integral_indicator hHm]
        congr 1 with y
        by_cases hy : y ∈ H <;> simp [hy, divergenceCLM_apply, φ, φ']
    calc limsup P (𝓝[>] 0)
        ≤ limsup (fun r => ENNReal.ofReal
            (∫ y, divergenceCLM φ y * ((fun y => x + r • y) ⁻¹' s).indicator 1 y ∂μ + ε))
            (𝓝[>] 0) :=
          limsup_le_limsup (eventually_perimeter_ball_zero_preimage_add_smul_le_integral hx hR
            hRR'.le φ hφ hφR ((tsupport_smul_subset_left _ _).trans
              (χ.tsupport_subset.trans ball_subset_closedBall)) hε')
      _ = ENNReal.ofReal (∫ y, divergenceCLM φ y * H.indicator 1 y ∂μ + ε) :=
          ((ENNReal.continuous_ofReal.tendsto _).comp (hlim.add_const _)).limsup_eq
      _ ≤ ENNReal.ofReal (∫ y, divergenceCLM φ y * H.indicator 1 y ∂μ) + ε := by
          refine ENNReal.ofReal_add_le.trans_eq ?_
          rw [ENNReal.ofReal_coe_nnreal]
      _ ≤ perimeter μ ⟨ball 0 R', isOpen_ball⟩ H + ε := by gcongr
  have hT : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ (finrank ℝ E - 1)) *
      perimeter μ ⟨ball 0 R, isOpen_ball⟩ H) (𝓝[>] 1)
      (𝓝 (perimeter μ ⟨ball 0 R, isOpen_ball⟩ H)) := by
    have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ (finrank ℝ E - 1))) (𝓝[>] 1) (𝓝 1) := by
      simpa [Function.comp_def] using
        ((ENNReal.continuous_ofReal.comp (continuous_pow _)).tendsto 1).mono_left
          nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const h1 (.inl one_ne_zero)
  exact ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun t ht => hPH t ht)

/-- **The density of the perimeter at the reduced boundary.** Let `E` have dimension `n ≥ 2`, let
`μ` be an additive Haar measure, and let `x` be a point of the reduced boundary of `s` in `Ω`, with
outer normal `ν = ν_s x`. As `r → 0⁺`,

`P(s; ball x r) / r ^ (n - 1) → P({y | ⟪y, ν⟫ < 0}; ball 0 1)`,

the perimeter of the half-space in the unit ball. For Lebesgue measure this constant is the volume
`ω_{n-1}` of the unit ball of `ℝ^(n-1)`, by the computation of the perimeter of a half-space in
`TauCeti.Analysis.BoundedVariation.Hyperplane`. -/
theorem tendsto_ofReal_div_pow_mul_perimeter_ball (hn : 2 ≤ finrank ℝ E)
    (hx : x ∈ reducedBoundary μ Ω s) :
    Tendsto (fun r : ℝ => ENNReal.ofReal (r / r ^ finrank ℝ E) *
        perimeter μ ⟨ball x r, isOpen_ball⟩ s) (𝓝[>] 0)
      (𝓝 (perimeter μ ⟨ball 0 1, isOpen_ball⟩ {y | ⟪y, outerNormal μ Ω s x⟫ < 0})) := by
  refine (tendsto_perimeter_ball_zero_preimage_add_smul hn hx one_pos).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [perimeter_ball_zero_preimage_add_smul hr, mul_one]

end TauCeti
