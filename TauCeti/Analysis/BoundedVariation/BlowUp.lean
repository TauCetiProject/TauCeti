/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.DensityEstimates
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
preimages `(fun y => x + r • y) ⁻¹' s`. This file shows that, as `r → 0⁺`, the distributional
derivative of `χ_{s_{x,r}}` points in the direction `-ν` up to an error that vanishes in the
limit. This is the step of De Giorgi's structure theorem that identifies the normal of every
blow-up limit.

* `TauCeti.tendsto_setLIntegral_enorm_outerNormal_sub_div`: the outer normal concentrates at
  `ν` in mean, `⨍_{closedBall x r} ‖ν_s - ν‖ d|Dχ_s| → 0`. It follows from the definition of `∂*s`:
  the averages of the unit vectors `ν_s` tend to the unit vector `ν`, and for unit vectors
  `‖a - ν‖² = 2 (1 - ⟪a, ν⟫)`.
* `TauCeti.eventually_neg_le_integral_divergenceCLM_mul_indicator_preimage`: against an additive
  Haar measure, for every test vector field `φ` on `E` with `⟪φ, ν⟫ ≥ 0` pointwise,
  `liminf_{r → 0⁺} ∫_{s_{x,r}} div φ ≥ 0`. Changing variables, the pairing is
  `r^(1-n) ∫ ⟪φ((y - x) / r), ν_s y⟫ d|Dχ_s|(y)`, `n = dim E`. Replacing `ν_s` by `ν` gives a
  nonnegative quantity, and the error is controlled by the concentration of the normal together
  with the upper density estimate `|Dχ_s| (closedBall x ρ) ≤ C ρ^(n-1)`
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

/-! ### Concentration of the outer normal -/

/-- The outer normal is integrable against the perimeter measure on sets of finite measure. -/
private theorem integrableOn_outerNormal (hx : x ∈ reducedBoundary μ Ω s) {S : Set Ω}
    (hS : variationMeasure μ Ω (s.indicator 1) S ≠ ∞) :
    IntegrableOn (fun y : Ω => outerNormal μ Ω s y) S (variationMeasure μ Ω (s.indicator 1)) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  refine Measure.integrableOn_of_bounded hS ?_ (M := 1) ?_
  · exact (measurable_polarDensity (μ := μ) (Ω := Ω) (u := s.indicator 1)).neg
      |>.aestronglyMeasurable.congr (ae_outerNormal_eq.mono fun _ h => h.symm)
  · filter_upwards [ae_restrict_of_ae ae_outerNormal_eq,
      ae_restrict_of_ae (ae_norm_polarDensity_eq_one hu hfin)] with y h1 h2
    rw [h1, norm_neg, h2]

/-- At a point `x` of the reduced boundary, for every `η > 0` and every small `r`, the perimeter
measure of `closedBall x r` is finite and
`∫_{closedBall x r} ‖ν_s - ν_s x‖ d|Dχ_s| ≤ 2 η |Dχ_s| (closedBall x r)`. -/
private theorem eventually_setIntegral_norm_outerNormal_sub_le
    (hx : x ∈ reducedBoundary μ Ω s) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] 0,
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) ≠ ∞ ∧
      ∫ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
          ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖ ∂variationMeasure μ Ω (s.indicator 1) ≤
        2 * η * (variationMeasure μ Ω (s.indicator 1)).real
          (((↑) : Ω → E) ⁻¹' closedBall x r) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  set lam := variationMeasure μ Ω (s.indicator 1)
  set ν := outerNormal μ Ω s x
  set n : Ω → E := fun y => outerNormal μ Ω s y
  have hν : ‖ν‖ = 1 := norm_outerNormal hx
  have hn1 : ∀ᵐ y ∂lam, ‖n y‖ = 1 := by
    filter_upwards [ae_outerNormal_eq, ae_norm_polarDensity_eq_one hu hfin] with y h1 h2
    simp only [n, h1, norm_neg, h2]
  -- The averages of `ν_s` over small balls tend to `ν`.
  have havg : Tendsto (fun r => ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r, n y ∂lam) (𝓝[>] 0)
      (𝓝 ν) := by
    have h := (tendsto_setAverage_polarDensity hx).neg
    rw [neg_neg] at h
    refine h.congr fun r => ?_
    rw [← average_neg]
    exact average_congr (ae_restrict_of_ae (ae_outerNormal_eq.mono fun _ h => h.symm))
  have hinner : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      1 - η ^ 2 / 2 < ⟪ν, ⨍ y in ((↑) : Ω → E) ⁻¹' closedBall x r, n y ∂lam⟫ := by
    refine (tendsto_const_nhds.inner havg).eventually_const_lt ?_
    rw [real_inner_self_eq_norm_sq, hν]
    linarith [pow_pos hη 2]
  obtain ⟨ε, hε, hεΩ⟩ :=
    nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [hinner, Ioc_mem_nhdsGT hε] with r hr hrε
  set S := ((↑) : Ω → E) ⁻¹' closedBall x r
  have hS : IsCompact S := Topology.IsInducing.subtypeVal.isCompact_preimage'
    (isCompact_closedBall x r) (by
      rw [Subtype.range_coe]
      exact (closedBall_subset_closedBall hrε.2).trans hεΩ)
  have hSfin : lam S ≠ ∞ := hS.measure_lt_top.ne
  refine ⟨hSfin, ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hn : IntegrableOn n S lam := integrableOn_outerNormal hx hSfin
  have hc (c : ℝ) : IntegrableOn (fun _ => c) S lam := integrableOn_const hSfin
  have hν' : IntegrableOn (fun _ => ν) S lam := integrableOn_const hSfin
  have hin : IntegrableOn (fun y => ⟪ν, n y⟫) S lam := Integrable.const_inner ν hn
  calc ∫ y in S, ‖n y - ν‖ ∂lam
      ≤ ∫ y in S, ((η + 2 / η) - 2 / η * ⟪ν, n y⟫) ∂lam := by
        refine setIntegral_mono_on_ae (hn.sub hν').norm ((hc _).sub (hin.const_mul _)) hSm ?_
        filter_upwards [hn1] with y hy _
        -- For unit vectors, `‖a - ν‖² = 2 (1 - ⟪a, ν⟫)` and `‖a - ν‖ ≤ η + ‖a - ν‖² / η`.
        have h := norm_sub_sq_real (n y) ν
        rw [hy, hν, real_inner_comm] at h
        rw [show η + 2 / η - 2 / η * ⟪ν, n y⟫ = (η * η + ‖n y - ν‖ ^ 2) / η by
          field_simp; linarith, le_div_iff₀ hη]
        nlinarith [sq_nonneg (‖n y - ν‖ - η), norm_nonneg (n y - ν)]
    _ = lam.real S * ((η + 2 / η) - 2 / η * ⟪ν, ⨍ y in S, n y ∂lam⟫) := by
        rw [integral_sub (hc _) (hin.const_mul _), integral_const_mul, integral_inner hn,
          setIntegral_const, ← measure_smul_setAverage _ hSfin, inner_smul_right, smul_eq_mul]
        ring
    _ ≤ 2 * η * lam.real S := by
        have hle : (η + 2 / η) - 2 / η * ⟪ν, ⨍ y in S, n y ∂lam⟫ ≤ 2 * η := by
          have h2 : 2 / η * (1 - η ^ 2 / 2) = 2 / η - η := by field_simp
          nlinarith [mul_lt_mul_of_pos_left hr (div_pos two_pos hη)]
        nlinarith [measureReal_nonneg (μ := lam) (s := S)]

/-- **Concentration of the outer normal at the reduced boundary.** At a point `x` of the reduced
boundary of `s` in `Ω`, the mean deviation of the outer normal from `ν_s x` over small closed
balls tends to zero:

`(∫_{closedBall x r} ‖ν_s - ν_s x‖ d|Dχ_s|) / |Dχ_s| (closedBall x r) → 0`  as `r → 0⁺`. -/
theorem tendsto_setLIntegral_enorm_outerNormal_sub_div (hx : x ∈ reducedBoundary μ Ω s) :
    Tendsto (fun r => (∫⁻ y in ((↑) : Ω → E) ⁻¹' closedBall x r,
        ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖ₑ ∂variationMeasure μ Ω (s.indicator 1)) /
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
  set lam := variationMeasure μ Ω (s.indicator 1)
  refine ENNReal.tendsto_nhds_zero.2 fun δ hδ => ?_
  obtain rfl | hδt := eq_or_ne δ ∞
  · exact .of_forall fun _ => le_top
  have hδr : 0 < δ.toReal / 2 := half_pos (ENNReal.toReal_pos hδ.ne' hδt)
  filter_upwards [eventually_setIntegral_norm_outerNormal_sub_le hx hδr] with r ⟨hSfin, hr⟩
  set S := ((↑) : Ω → E) ⁻¹' closedBall x r
  refine ENNReal.div_le_of_le_mul ?_
  have hi : IntegrableOn (fun y : Ω => outerNormal μ Ω s y - outerNormal μ Ω s x) S lam :=
    (integrableOn_outerNormal hx hSfin).sub (integrableOn_const hSfin)
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
  calc ENNReal.ofReal (∫ y in S, ‖outerNormal μ Ω s y - outerNormal μ Ω s x‖ ∂lam)
      ≤ ENNReal.ofReal (2 * (δ.toReal / 2) * lam.real S) := ENNReal.ofReal_le_ofReal hr
    _ = δ * lam S := by
        rw [mul_div_cancel₀ _ two_ne_zero, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hδt, ofReal_measureReal hSfin]

/-! ### The blow-up pairing -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- Rescaling a test vector field on `E` around `x` by a ratio `r ≠ 0` gives a test vector field
on `Ω`, provided the rescaled support lies in `Ω`. -/
private theorem exists_testFunction_eq_comp (φ : 𝓓((⊤ : Opens E), E)) {r : ℝ} (hr : r ≠ 0)
    (hΩ : ∀ y ∈ tsupport φ, x + r • y ∈ Ω) :
    ∃ ψ : 𝓓(Ω, E), (∀ y, ψ y = φ (r⁻¹ • (y - x))) ∧
      ∀ y, divergenceCLM ψ y = r⁻¹ * divergenceCLM φ (r⁻¹ • (y - x)) := by
  have htop {f : E → E} : MapsTo f (⊤ : Opens E) (⊤ : Opens E) := by
    rw [Opens.coe_top]
    exact mapsTo_univ _ _
  let ψ' : 𝓓((⊤ : Opens E), E) :=
    translateTestFunction (h := x) htop (dilateTestFunction hr htop φ)
  have hψ' (y : E) : ψ' y = φ (r⁻¹ • (y - x)) := by
    rw [translateTestFunction_apply, dilateTestFunction_apply]
  -- The support of `ψ'` lies in the image of the support of `φ` under `z ↦ x + r • z`.
  have hsub : Function.support (ψ' : E → E) ⊆ (fun z => x + r • z) '' tsupport φ := fun y hy =>
    ⟨r⁻¹ • (y - x), subset_tsupport _ (by rwa [Function.mem_support, ← hψ']),
      by simp [smul_inv_smul₀ hr]⟩
  have hsupp : tsupport (ψ' : E → E) ⊆ Ω := by
    refine (closure_minimal hsub
      (φ.hasCompactSupport.isCompact.image (by fun_prop)).isClosed).trans ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hΩ y hy
  refine ⟨⟨ψ', ψ'.contDiff, ψ'.hasCompactSupport, hsupp⟩, fun y => by rw [coe_mk, hψ'],
    fun y => ?_⟩
  rw [divergenceCLM_apply, coe_mk, ← divergenceCLM_apply, divergenceCLM_translateTestFunction,
    translateTestFunction_apply, divergenceCLM_dilateTestFunction]
  simp only [IsSMulApply.smul_apply, dilateTestFunction_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For small `r > 0` the rescaled support of a test vector field lies in `Ω`. -/
private theorem eventually_forall_tsupport_add_smul_mem (hx : x ∈ Ω) (φ : 𝓓((⊤ : Opens E), E)) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ y ∈ tsupport φ, x + r • y ∈ Ω := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  obtain ⟨ε, hε, hεΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds hx)
  have hR1 : 0 < max R 1 := lt_max_of_lt_right one_pos
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε hR1)] with r hr y hy
  refine hεΩ ?_
  have hy' : ‖y‖ ≤ max R 1 := (mem_closedBall_zero_iff.1 (hR hy)).trans (le_max_left _ _)
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.1.le]
  calc r * ‖y‖ ≤ r * max R 1 := mul_le_mul_of_nonneg_left hy' hr.1.le
    _ ≤ ε := ((lt_div_iff₀ hR1).1 hr.2).le

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
    (((integrableOn_outerNormal hx hSfin).sub (integrableOn_const hSfin)).norm.const_mul M).neg
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
  simp_rw [hpt]
  refine ⟨((hk.comp_add_left x).comp_smul hr.ne').const_mul r, ?_⟩
  rw [integral_const_mul, μ.integral_comp_smul (fun z => k (x + z)), integral_add_left_eq_self,
    integral_divergenceCLM_mul_indicator_eq_integral_inner_outerNormal hu hfin ψ,
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
  obtain ⟨ψ, hψ, hdiv⟩ := exists_testFunction_eq_comp φ hr.ne' hΩ
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
    obtain ⟨ψ, -, hdiv⟩ := exists_testFunction_eq_comp φ hri.ne' hΩ
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

end TauCeti
