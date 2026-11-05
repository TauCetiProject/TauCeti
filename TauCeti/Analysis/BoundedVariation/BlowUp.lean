/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.DensityEstimates
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import TauCeti.Analysis.BoundedVariation.Compactness
import TauCeti.Analysis.BoundedVariation.Dilation
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import TauCeti.Analysis.BoundedVariation.Translation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Distribution.TestFunction.Dilation
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Blow-ups at points of the reduced boundary

Let `Ω` be an open set of a finite-dimensional real inner product space `E`, let `s` be a set
whose reduced boundary `∂*s` in `Ω` contains `x`, and let `ν = ν_s x` be the outer normal there.
The **blow-ups** of `s` at `x` are the sets `s_{x,r} = (s - x) / r`, written here as the
preimages `(fun y => x + r • y) ⁻¹' s`. This file shows that, as `r → 0⁺`, the blow-ups are
relatively compact for local convergence in measure, that every limit has locally finite perimeter
and fills a definite proportion of every ball around the origin together with its complement, and
that the distributional derivative of `χ_{s_{x,r}}` points in the direction `-ν` up to an error that
vanishes in the limit. These are the steps of De Giorgi's structure theorem that produce blow-up
limits and identify their normal.

* `TauCeti.perimeter_ball_zero_preimage_add_smul` and
  `TauCeti.measure_preimage_add_smul_inter_ball`: against an additive Haar measure,
  `P(s_{x,r}; ball 0 R) = r^(1-n) P(s; ball x (r R))` and
  `μ(s_{x,r} ∩ ball 0 ρ) = r^(-n) μ(s ∩ ball x (r ρ))`, where `n = dim E`.
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

No finite perimeter or measurability of `s` is assumed: a point of the reduced boundary forces
`s` to have locally finite perimeter in `Ω`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 15
  (blow-ups at points of the reduced boundary).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.2 (blow-up of the reduced boundary).
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
    (hx : x ∈ reducedBoundary μ Ω s) {ψ : 𝓓(Ω, E)} {S : Set Ω} (hSm : MeasurableSet S)
    (hSfin : variationMeasure μ Ω (s.indicator 1) S ≠ ∞) {M : ℝ} (hM : ∀ y, ‖ψ y‖ ≤ M)
    (hψν : ∀ y, 0 ≤ ⟪ψ y, outerNormal μ Ω s x⟫) (hψS : ∀ y : Ω, y ∉ S → ψ y = 0) :
    -(M * ∫ y in S, ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖
        ∂variationMeasure μ Ω (s.indicator 1)) ≤
      ∫ y, ⟪ψ y, outerNormal μ Ω s y⟫ ∂variationMeasure μ Ω (s.indicator 1) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  set ν := outerNormal μ Ω s x
  have hg : IntegrableOn (fun y : Ω => -(M * ‖outerNormal μ Ω s y - ν‖)) S
      (variationMeasure μ Ω (s.indicator 1)) :=
    (((integrableOn_outerNormal hSfin).sub (integrableOn_const hSfin)).norm.const_mul M).neg
  rw [← integral_const_mul, ← integral_neg, ← integral_indicator hSm]
  refine integral_mono (hg.integrable_indicator hSm) ?_ fun y => ?_
  · refine (integrable_inner_polarDensity hu hfin ψ.continuous ψ.hasCompactSupport
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
    simpa only [smul_eq_mul] using integrable_smul_of_locallyIntegrableOn hu (divergenceCLM ψ)
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
  have hlow := neg_mul_setIntegral_le_integral_inner_outerNormal hx hSm hSfin (M := M')
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
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  set g := divergenceCLM φ
  set S : ι → Set E := fun i => (fun y => x + r i • y) ⁻¹' s
  have hint : ∀ᶠ i in l, Integrable (fun y => g y * (S i).indicator 1 y) μ := by
    filter_upwards [hr.eventually (eventually_forall_tsupport_add_smul_mem
      (reducedBoundary_subset hx) φ), hr.eventually self_mem_nhdsWithin] with i hΩ (hri : 0 < r i)
    obtain ⟨ψ, -, hdiv⟩ := TestFunction.exists_eq_comp φ hri.ne' hΩ
    exact (integrable_and_integral_divergenceCLM_mul_indicator_preimage hu hfin φ hri hdiv).1
  have hJ : Integrable (fun y => g y * F.indicator 1 y) μ := by
    refine (integrable_smul_of_locallyIntegrableOn
      (locallyIntegrableOn_indicator_const (hF.mono Measure.restrict_le_self) 1) g).congr
      (.of_forall fun y => ?_)
    simp [Pi.one_def]
  -- The pairings converge, since `|∫ g (χ_{S i} - χ_F)| ≤ C μ ((S i ∆ F) ∩ tsupport g)`.
  obtain ⟨C, hC⟩ := g.hasCompactSupport.exists_bound_of_continuous g.continuous
  have hlim : Tendsto (fun i => ∫ y, g y * (S i).indicator 1 y ∂μ) l
      (𝓝 (∫ y, g y * F.indicator 1 y ∂μ)) := by
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
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [← neg_le_iff_add_nonneg]
  exact ge_of_tendsto hlim (hr.eventually
    (eventually_neg_le_integral_divergenceCLM_mul_indicator_preimage hx φ hφ hε))

/-! ### Perimeter and volume of the blow-ups -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The blow-up map `y ↦ x + r • y` pulls `ball x (r * R)` back to `ball 0 R`. -/
private theorem preimage_add_smul_ball {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (fun y => x + r • y) ⁻¹' ball x (r * R) = ball 0 R := by
  ext y
  simp [norm_smul, abs_of_pos hr, mul_lt_mul_iff_right₀ hr]

/-- **The perimeter of a blow-up in a ball.** Against an additive Haar measure and for `r > 0`, the
perimeter in `ball 0 R` of the blow-up `(fun y => x + r • y) ⁻¹' s` is `r / r ^ n` times the
perimeter of `s` in `ball x (r * R)`, where `n = dim E`. -/
theorem perimeter_ball_zero_preimage_add_smul {r : ℝ} (hr : 0 < r) (R : ℝ) :
    perimeter μ ⟨ball 0 R, isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s) =
      ENNReal.ofReal (r / r ^ finrank ℝ E) * perimeter μ ⟨ball x (r * R), isOpen_ball⟩ s := by
  have h : (fun y => x + r • y) ⁻¹' s = (r • ·) ⁻¹' ((· + x) ⁻¹' s) := by
    ext y
    simp [add_comm]
  rw [h, perimeter_preimage_smul (Ω := ⟨ball 0 (r * R), isOpen_ball⟩) hr ?_ ?_,
    perimeter_preimage_add_right (Ω := ⟨ball x (r * R), isOpen_ball⟩) ?_ ?_]
  · intro y hy
    simpa using hy
  · intro y hy
    simpa [dist_eq_norm] using hy
  · intro y hy
    simpa [norm_smul, abs_of_pos hr, mul_lt_mul_iff_right₀ hr] using hy
  · intro y hy
    simpa [norm_smul, abs_of_pos hr, inv_mul_lt_iff₀ hr] using hy

/-- **The volume of a blow-up in a ball.** Against an additive Haar measure and for `r > 0`,
`μ(s_{x,r} ∩ ball 0 ρ) = r ^ (-n) μ(s ∩ ball x (r * ρ))`, where `n = dim E`. -/
theorem measure_preimage_add_smul_inter_ball {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    μ ((fun y => x + r • y) ⁻¹' s ∩ ball 0 ρ) =
      ENNReal.ofReal ((r ^ finrank ℝ E)⁻¹) * μ (s ∩ ball x (r * ρ)) := by
  rw [← preimage_add_smul_ball (x := x) hr ρ, ← preimage_inter]
  have h : (fun y => x + r • y) ⁻¹' (s ∩ ball x (r * ρ)) =
      (r • ·) ⁻¹' ((fun y => x + y) ⁻¹' (s ∩ ball x (r * ρ))) := rfl
  rw [h, Measure.addHaar_preimage_smul μ hr.ne', measure_preimage_add,
    abs_of_pos (by positivity)]

/-- Blow-ups of a null-measurable set are null-measurable. -/
private theorem nullMeasurableSet_preimage_add_smul {t : Set E} (ht : NullMeasurableSet t μ)
    {r : ℝ} (hr : r ≠ 0) : NullMeasurableSet ((fun y => x + r • y) ⁻¹' t) μ :=
  (ht.preimage (measurePreserving_add_left μ x).quasiMeasurePreserving).preimage
    (Measure.quasiMeasurePreserving_smul μ hr)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Sets that agree on `ball x (r * R)` have blow-ups at scale `r` that agree on `ball 0 R`. -/
private theorem preimage_add_smul_inter_ball_eq {a b : Set E} {r R : ℝ} (hr : 0 < r)
    (h : a ∩ ball x (r * R) = b ∩ ball x (r * R)) :
    (fun y => x + r • y) ⁻¹' a ∩ ball 0 R = (fun y => x + r • y) ⁻¹' b ∩ ball 0 R := by
  rw [← preimage_add_smul_ball hr R, ← preimage_inter, ← preimage_inter, h]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Sets that agree on `ball x (r * R)` have blow-ups at scale `r` with the same symmetric
difference with `c` inside every `K ⊆ ball 0 R`. -/
private theorem preimage_add_smul_symmDiff_inter_eq {a b c K : Set E} {r R : ℝ} (hr : 0 < r)
    (h : a ∩ ball x (r * R) = b ∩ ball x (r * R)) (hK : K ⊆ ball 0 R) :
    (((fun y => x + r • y) ⁻¹' a) ∆ c) ∩ K = (((fun y => x + r • y) ⁻¹' b) ∆ c) ∩ K := by
  have hK' : (fun y => x + r • y) ⁻¹' a ∩ K = (fun y => x + r • y) ⁻¹' b ∩ K := by
    rw [← inter_eq_right.2 hK, ← inter_assoc, preimage_add_smul_inter_ball_eq hr h, inter_assoc]
  rw [inter_symmDiff_distrib_right, inter_symmDiff_distrib_right, hK']

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The scaling `r / r ^ n · n (r R) ^ (n - 1) ω = n R ^ (n - 1) ω` of the upper density bound
under a blow-up, in positive dimension `n`. -/
private theorem ofReal_div_pow_mul_ofReal_mul_pow [Nontrivial E] {r : ℝ} (hr : 0 < r) (R : ℝ)
    (t : ℝ≥0) :
    ENNReal.ofReal (r / r ^ finrank ℝ E) *
        (t * ENNReal.ofReal (finrank ℝ E * (r * R) ^ (finrank ℝ E - 1) * μ.real (ball 0 1))) =
      t * ENNReal.ofReal (finrank ℝ E * R ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
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
  rw [perimeter_ball_zero_preimage_add_smul hr.1, ← ofReal_div_pow_mul_ofReal_mul_pow hr.1]
  exact mul_le_mul_right (hP _ ⟨mul_pos hr.1 hR, (lt_div_iff₀ hR).1 hr.2⟩) _

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
      rw [perimeter_ball_zero_preimage_add_smul (hpos i),
        perimeter_congr_of_inter_eq (hagree' (ball_subset_ball hrR.le))]
      exact (mul_le_mul_right (hP _ ⟨mul_pos (hpos i) hR, hrR.trans hρ.2⟩) _).trans_eq
        (ofReal_div_pow_mul_ofReal_mul_pow (hpos i) R 2)
  obtain ⟨F, hF, φ, hφ, hconv⟩ := exists_subseq_tendsto_measure_symmDiff_inter_of_perimeter_le
    (Ω := ⊤) (s := fun i => (fun y => x + r i • y) ⁻¹' s')
    (fun i => nullMeasurableSet_preimage_add_smul hs' (hpos i).ne') fun K hK _ => by
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
          nullMeasurableSet_preimage_add_smul hsΩ (ne_of_gt hi)) hF fun K hK hKR =>
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
        rw [measure_preimage_add_smul_inter_ball hri, mul_left_comm]
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

end TauCeti
