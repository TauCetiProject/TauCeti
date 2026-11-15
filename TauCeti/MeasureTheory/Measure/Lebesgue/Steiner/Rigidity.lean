/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.LebesgueDecomposition
public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Regular
import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.BoundedVariation.Slicing.Measurability
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Subgraph
import TauCeti.MeasureTheory.Integral.Lebesgue.Subsequence

/-!
# Quantitative perimeter excess and interval-section rigidity for Steiner symmetrization

Let `E` be a finite-dimensional real inner product space, `e` a unit vector with orthogonal
hyperplane `H = (ℝ ∙ e)ᗮ`, and `s ⊆ E` a null-measurable set of finite volume. Write
`v(y) = |{t : ℝ | y + t • e ∈ s}|` for the section-length function on `H`, `D = {y | 0 < v(y)}`
for the essential projection, and `∇ᵃv` for the absolutely continuous derivative density
`acDerivativeDensity volume ⊤ v (volume.comap Subtype.val)` of `v` on `H`.

This file proves the Chlebík–Cianchi–Fusco / Cagnetti–Colombo–De Philippis–Maggi quantitative
excess refinement of Steiner's perimeter inequality
(`TauCeti.perimeter_steinerSymmetrization_add_setLIntegral_le` and
`TauCeti.perimeter_steinerSymmetrization_add_lintegral_noninterval_le`):

`P(S_e s) + ∫_{y ∈ A} 4 / √(4 + ‖∇ᵃv(y)‖²) dy ≤ P(s)`,

where `S_e s = steinerSymmetrization e he s` and `A ⊆ H` is the family of transverse points whose
line sections do not agree almost everywhere with any interval. No boundedness or regularity of `s`
is assumed, and `P(s)` may be infinite.

Consequently, **equality in Steiner's perimeter inequality forces interval sections**
(`TauCeti.ae_lineSection_ordConnected_of_perimeter_steinerSymmetrization_eq`): if `P(s) < ∞` and
`P(S_e s) = P(s)`, then for almost every `y ∈ (ℝ ∙ e)ᗮ` the section `{t | y + t • e ∈ s}` agrees
almost everywhere with an interval. Interval sections are necessary but not sufficient for equality
in a single direction: a sheared slab has interval sections along `e`, yet symmetrization removes
the tilt of its midpoints and strictly decreases perimeter.

## Proof outline

1. **Smooth-slab upper bound
   (`TauCeti.perimeter_steinerSymmetrization_le_lintegral_add_singularPart`).**
   When `P(s) < ∞`, `v` is integrable on `H` with bounded variation (`|Dv|(H) ≤ P(s)`), and
   `volume D < ∞`. Mollifying `v` by shrinking normalized smooth bumps gives nonnegative `C¹`
   widths `v_k = ρ_k ⋆ v` whose symmetric slabs `{|⟪e, x⟫| < v_k(π_H x) / 2}` converge in measure
   to `S_e s`. By the `C¹` slab divergence formula
   (`TauCeti.setIntegral_setOf_abs_inner_lt_div_two_trace_fderiv`) and the Lebesgue decomposition
   `Dv = ∇ᵃv dy + σ_v d|Dˢv|`, passing to the limit `k → ∞` bounds `P(S_e s)` above by
   `∫_D √(4 + ‖∇ᵃv‖²) + ∫_{Dᶜ} ‖∇ᵃv‖ + |Dˢv|(H)`.
2. **Calibration lower bound on `P(s)`.** In the localized joint slicing inequality
   (`TauCeti.two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter`), we
   choose a measurable transverse vector field `Φ₀` of norm at most `1` equal to `-σ_v` on a
   singular carrier of `|Dˢv|`, to `-∇ᵃv / √(4 + ‖∇ᵃv‖²)` on `D`, and to `-∇ᵃv / ‖∇ᵃv‖` off `D`.
   Approximating `Φ₀` by smooth compactly supported test fields of norm at most `1` in `L¹` against
   the finite measure `volume.restrict D + ‖∇ᵃv‖ volume + |Dˢv|`
   (`MeasureTheory.MemLp.exists_testFunction_eLpNorm_sub_le_and_norm_le`) yields
   `∫_D √(4 + ‖∇ᵃv‖²) + ∫_{Dᶜ} ‖∇ᵃv‖ + |Dˢv|(H) + ∫_A 4 / √(4 + ‖∇ᵃv‖²) ≤ P(s)`,
   whose first three terms dominate `P(S_e s)`.

## References

* M. Chlebík, A. Cianchi, N. Fusco, *The perimeter inequality under Steiner symmetrization: cases
  of equality*, Ann. of Math. (2) **162** (2005), 525–555.
* F. Cagnetti, M. Colombo, G. De Philippis, F. Maggi, *Rigidity of equality cases in Steiner's
  perimeter inequality*, Anal. PDE **7** (2014), 1535–1593.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapter 14.
-/

public section

noncomputable section

open ContinuousLinearMap Filter MeasureTheory Metric Set TopologicalSpace TestFunction
open scoped BoundedContinuousFunction Convolution Distributions ENNReal RealInnerProductSpace
  Topology symmDiff

namespace TauCeti

section Elementary

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
/-- `y ↦ √(4 + ‖y‖²)` is `1`-Lipschitz, as the Euclidean norm of `(2, y)` in `ℝ × H`. -/
private theorem abs_sqrt_four_add_norm_sq_sub_le (a b : H) :
    |√(4 + ‖a‖ ^ 2) - √(4 + ‖b‖ ^ 2)| ≤ ‖a - b‖ := by
  have hnorm (z : H) : ‖WithLp.toLp 2 ((2 : ℝ), z)‖ = √(4 + ‖z‖ ^ 2) := by
    rw [WithLp.prod_norm_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs]
    norm_num
  rw [← hnorm a, ← hnorm b]
  refine (abs_norm_sub_norm_le _ _).trans_eq ?_
  have hsub : WithLp.toLp 2 ((2 : ℝ), a) - WithLp.toLp 2 ((2 : ℝ), b) =
      WithLp.toLp 2 ((0 : ℝ), a - b) := by
    apply (WithLp.ext_iff 2).2
    ext <;> simp
  rw [hsub, WithLp.norm_toLp_snd]

omit [InnerProductSpace ℝ H] in
/-- Elementary subadditivity `√(4 + ‖a‖²) ≤ 2 + ‖a‖`. -/
private theorem sqrt_four_add_norm_sq_le (a : H) : √(4 + ‖a‖ ^ 2) ≤ 2 + ‖a‖ := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg a]

/-- Orthogonal decomposition norm identity `⟪e, z⟫² + ‖π_H z‖² = ‖z‖²` for unit `e`. -/
private theorem sq_inner_add_norm_orthogonalProjectionOnto_sq {e : E} (he : ‖e‖ = 1) (z : E) :
    ⟪e, z⟫ ^ 2 + ‖(ℝ ∙ e)ᗮ.orthogonalProjectionOnto z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [(ℝ ∙ e).norm_sq_eq_add_norm_sq_starProjection z,
    Submodule.starProjection_unit_singleton ℝ he z, norm_smul, Real.norm_eq_abs, he, mul_one,
    sq_abs]
  rfl

/-- Pointwise Cauchy–Schwarz bound on the smooth-slab boundary integrand over positive-length
sections: if `‖z₁‖ ≤ 1` and `‖z₂‖ ≤ 1`, then
`⟪e, z₁ - z₂⟫ - (1/2) ⟪π_H (z₁ + z₂), b⟫ ≤ √(4 + ‖b‖²)`. -/
private theorem slab_boundary_le_sqrt {e : E} (he : ‖e‖ = 1) {z₁ z₂ : E}
    (hz₁ : ‖z₁‖ ≤ 1) (hz₂ : ‖z₂‖ ≤ 1) (b : (ℝ ∙ e)ᗮ) :
    ⟪e, z₁ - z₂⟫ - (2 : ℝ)⁻¹ * ⟪(ℝ ∙ e)ᗮ.orthogonalProjectionOnto (z₁ + z₂), b⟫ ≤
      √(4 + ‖b‖ ^ 2) := by
  let π := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  let p : WithLp 2 (ℝ × (ℝ ∙ e)ᗮ) :=
    WithLp.toLp 2 ((2 : ℝ)⁻¹ * ⟪e, z₁ - z₂⟫, -((2 : ℝ)⁻¹ • π (z₁ + z₂)))
  let q : WithLp 2 (ℝ × (ℝ ∙ e)ᗮ) := WithLp.toLp 2 (2, b)
  have hpq : ⟪p, q⟫ = ⟪e, z₁ - z₂⟫ - (2 : ℝ)⁻¹ * ⟪π (z₁ + z₂), b⟫ := by
    rw [WithLp.prod_inner_apply]
    simp only [p, q, RCLike.inner_apply, RCLike.conj_to_real, inner_neg_left, inner_smul_left]
    ring
  have hq : ‖q‖ = √(4 + ‖b‖ ^ 2) := by
    rw [WithLp.prod_norm_eq_of_L2]
    simp only [q, WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs]
    norm_num
  have hp : ‖p‖ ≤ 1 := by
    rw [WithLp.prod_norm_eq_of_L2, Real.sqrt_le_one]
    simp only [p, WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs, norm_neg,
      norm_smul]
    norm_num
    have h₁ : ⟪e, z₁⟫ ^ 2 + ‖(π z₁ : E)‖ ^ 2 = ‖z₁‖ ^ 2 :=
      sq_inner_add_norm_orthogonalProjectionOnto_sq he z₁
    have h₂ : ⟪e, z₂⟫ ^ 2 + ‖(π z₂ : E)‖ ^ 2 = ‖z₂‖ ^ 2 :=
      sq_inner_add_norm_orthogonalProjectionOnto_sq he z₂
    have hz₁' : ‖z₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z₁]
    have hz₂' : ‖z₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z₂]
    have hpar := parallelogram_law_with_norm ℝ (π z₁ : E) (π z₂ : E)
    rw [inner_sub_right, mul_pow, mul_pow]
    nlinarith [sq_nonneg (⟪e, z₁⟫ + ⟪e, z₂⟫), sq_nonneg ‖(π z₁ : E) - (π z₂ : E)‖]
  calc ⟪e, z₁ - z₂⟫ - (2 : ℝ)⁻¹ * ⟪π (z₁ + z₂), b⟫
      = ⟪p, q⟫ := hpq.symm
    _ ≤ ‖p‖ * ‖q‖ := real_inner_le_norm p q
    _ ≤ 1 * √(4 + ‖b‖ ^ 2) := by rw [hq]; exact mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg _)
    _ = √(4 + ‖b‖ ^ 2) := one_mul _

/-- Pointwise bound on the smooth-slab boundary integrand off the positive-length locus, using a
derivative bound `‖z₁ - z₂‖ ≤ M * w`. -/
private theorem slab_boundary_le_off {e : E} (he : ‖e‖ = 1) {z₁ z₂ : E}
    (hz₁ : ‖z₁‖ ≤ 1) (hz₂ : ‖z₂‖ ≤ 1) {M w : ℝ} (hdiff : ‖z₁ - z₂‖ ≤ M * w)
    (b s : (ℝ ∙ e)ᗮ) :
    ⟪e, z₁ - z₂⟫ - (2 : ℝ)⁻¹ * ⟪(ℝ ∙ e)ᗮ.orthogonalProjectionOnto (z₁ + z₂), b + s⟫ ≤
      M * w + ‖b‖ + ‖s‖ := by
  let π := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hπz (z : E) : ‖(π z : E)‖ ≤ ‖z‖ := by
    have : ⟪e, z⟫ ^ 2 + ‖(π z : E)‖ ^ 2 = ‖z‖ ^ 2 :=
      sq_inner_add_norm_orthogonalProjectionOnto_sq he z
    exact le_of_sq_le_sq (by nlinarith [sq_nonneg ⟪e, z⟫]) (norm_nonneg z)
  have hπ1 : ‖(2 : ℝ)⁻¹ • π (z₁ + z₂)‖ ≤ 1 := by
    change ‖(2 : ℝ)⁻¹ • ((π (z₁ + z₂) : E))‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, map_add, Submodule.coe_add]
    norm_num
    linarith [norm_add_le (π z₁ : E) (π z₂ : E), hπz z₁, hπz z₂]
  have h1 : ⟪e, z₁ - z₂⟫ ≤ M * w :=
    (real_inner_le_norm e (z₁ - z₂)).trans (by simpa [he] using hdiff)
  have h2 : -(2 : ℝ)⁻¹ * ⟪π (z₁ + z₂), b + s⟫ ≤ ‖b‖ + ‖s‖ := by
    have : -⟪(2 : ℝ)⁻¹ • π (z₁ + z₂), b + s⟫ ≤ ‖(2 : ℝ)⁻¹ • π (z₁ + z₂)‖ * ‖b + s‖ :=
      (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
    rw [inner_smul_left, RCLike.conj_to_real] at this
    calc -(2 : ℝ)⁻¹ * ⟪π (z₁ + z₂), b + s⟫
        = -((2 : ℝ)⁻¹ * ⟪π (z₁ + z₂), b + s⟫) := by ring
      _ ≤ ‖(2 : ℝ)⁻¹ • π (z₁ + z₂)‖ * ‖b + s‖ := this
      _ ≤ 1 * (‖b‖ + ‖s‖) := mul_le_mul hπ1 (norm_add_le b s) (norm_nonneg _) zero_le_one
      _ = ‖b‖ + ‖s‖ := one_mul _
  linarith

/-- Calibration identity `√(1 - ‖-(√(4 + ‖a‖²))⁻¹ • a‖²) = 2 / √(4 + ‖a‖²)`. -/
private theorem sqrt_one_sub_norm_calibration_sq (a : H) :
    √(1 - ‖-(√(4 + ‖a‖ ^ 2))⁻¹ • a‖ ^ 2) = 2 / √(4 + ‖a‖ ^ 2) := by
  have hpos : 0 < 4 + ‖a‖ ^ 2 := by positivity
  have hspos : 0 < √(4 + ‖a‖ ^ 2) := Real.sqrt_pos.2 hpos
  have halg : 1 - (4 + ‖a‖ ^ 2)⁻¹ * ‖a‖ ^ 2 = 4 / (4 + ‖a‖ ^ 2) := by
    field_simp [hpos.ne']
    ring
  rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_inv, abs_of_pos hspos, mul_pow, inv_pow,
    Real.sq_sqrt hpos.le, halg, Real.sqrt_div (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq zero_le_two]

end Elementary

section MollifiedBV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- The comap of Lebesgue volume to `(⊤ : Opens H)` is finite on compacts, hence σ-finite. -/
private theorem isFiniteMeasureOnCompacts_comap_top :
    IsFiniteMeasureOnCompacts ((volume : Measure H).comap Subtype.val : Measure (⊤ : Opens H)) :=
  ⟨fun _ hK => (Measure.comap_apply_le Subtype.val volume hK.nullMeasurableSet).trans_lt
    (hK.image continuous_subtype_val).measure_lt_top⟩

/-- Pulling `acDerivativeDensity volume ⊤ u (volume.comap Subtype.val)` back to `H` gives a
globally integrable vector field whenever `totalVariationOn volume ⊤ u ≠ ∞`. -/
private theorem integrable_acDerivativeDensity_on_univ {u : H → ℝ} (hu : LocallyIntegrable u volume)
    (hvar : totalVariationOn volume ⊤ u ≠ ∞) :
    Integrable (fun y : H => acDerivativeDensity volume ⊤ u
      (volume.comap Subtype.val) ⟨y, trivial⟩) volume := by
  let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
  have hgΩ := integrable_acDerivativeDensity (hu.locallyIntegrableOn _) ν hvar
  have hm : Measurable fun y : H => acDerivativeDensity volume ⊤ u ν ⟨y, trivial⟩ :=
    (measurable_acDerivativeDensity ν).comp
      (Continuous.subtype_mk continuous_id fun _ => trivial).measurable
  refine ⟨hm.aestronglyMeasurable, hasFiniteIntegral_iff_eNorm.2 ?_⟩
  have hlin := lintegral_subtype_comap (μ := volume) (s := ((⊤ : Opens H) : Set H))
    (⊤ : Opens H).isOpen.measurableSet
    (fun y : H => ‖acDerivativeDensity volume ⊤ u ν ⟨y, trivial⟩‖ₑ)
  rw [Opens.coe_top, Measure.restrict_univ] at hlin
  exact hlin ▸ hasFiniteIntegral_iff_eNorm.1 hgΩ.2

/-- Differentiating `ρ ⋆ u` for a `BV` function `u` splits into the convolution `ρ ⋆ ∇ᵃu` of the
absolutely continuous derivative density and the convolution of `ρ` against the singular part. -/
private theorem fderiv_convolution_eq_inner_add_singular {u : H → ℝ}
    (hu : LocallyIntegrable u volume) (hvar : totalVariationOn volume ⊤ u ≠ ∞)
    {ρ : H → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) (y w : H) :
    fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, volume] u) y w =
      ⟪w, (ρ ⋆[lsmul ℝ ℝ, volume] fun z : H =>
            acDerivativeDensity volume ⊤ u (volume.comap Subtype.val) ⟨z, trivial⟩) y +
          ∫ z : (⊤ : Opens H), ρ (y - z) • polarDensity volume ⊤ u z
            ∂(variationMeasure volume ⊤ u).singularPart (volume.comap Subtype.val)⟫ := by
  have := (⊤ : Opens H).isOpen.locallyCompactSpace
  have := isFiniteMeasureOnCompacts_comap_top (H := H)
  let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
  let g : H → H := fun z => acDerivativeDensity volume ⊤ u ν ⟨z, trivial⟩
  let μs := (variationMeasure volume ⊤ u).singularPart ν
  let σ := polarDensity volume ⊤ u
  have hg : Integrable g volume := integrable_acDerivativeDensity_on_univ hu hvar
  have hfin : ∀ K, IsCompact K → K ⊆ (⊤ : Opens H) →
      ∃ U : Opens H, K ⊆ (U : Set H) ∧ totalVariationOn volume U u ≠ ∞ :=
    fun _ _ hK => ⟨⊤, hK, hvar⟩
  -- Test the BV Lebesgue decomposition against `Ψ = ρ(y - ·) • w`.
  let φ : 𝓓((⊤ : Opens H), ℝ) :=
    ⟨fun z => ρ (y - z), by fun_prop, hρc.comp_homeomorph (Homeomorph.subLeft y), subset_univ _⟩
  have hφ_apply (z : H) : φ z = ρ (y - z) := rfl
  let Ψ : 𝓓((⊤ : Opens H), H) := postcompCLM (toSpanSingleton ℝ w) φ
  have hdiv (z : H) : divergenceCLM Ψ z = -fderiv ℝ ρ (y - z) w := by
    have hcoe : (Ψ : H → H) = fun s => ρ (y - s) • w := by ext s; simp [Ψ, hφ_apply]
    have hdρ : HasFDerivAt (fun s : H => ρ (y - s))
        ((fderiv ℝ ρ (y - z)).comp (0 - ContinuousLinearMap.id ℝ H)) z :=
      (hρ.differentiable (by simp) (y - z)).hasFDerivAt.comp z
        ((hasFDerivAt_const y z).sub (hasFDerivAt_id z))
    rw [divergenceCLM_apply, hcoe, trace_fderiv_smul_const hdρ.differentiableAt, hdρ.fderiv]
    simp
  have hleb := integral_divergenceCLM_mul_eq_neg_integral_inner_acDerivativeDensity_sub_singularPart
    (hu.locallyIntegrableOn _) hfin ν Ψ
  simp only [hdiv, neg_mul, integral_neg] at hleb
  have hd : fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, volume] u) y w = ∫ z : H, fderiv ℝ ρ (y - z) w * u z := by
    rw [← convolution_flip, hρc.fderiv_convolution_right_apply _ hu (hρ.of_le (by simp)) y w]
    simp [convolution_def, mul_comm]
  -- Identify the AC and singular pairings with the two right-hand terms.
  have hac_int : Integrable (fun z : H => ρ (y - z) • g z) volume := by
    simpa [convolution_def] using
      (hρc.convolutionExists_right (lsmul ℝ ℝ).flip hg.locallyIntegrable hρ.continuous y).integrable
  have hμs_int : Integrable (fun z : (⊤ : Opens H) => ρ (y - z) • σ z) μs :=
    φ.integrable_bilin_subtype (lsmul ℝ ℝ) ((locallyIntegrable_polarDensity (μ := volume)
      (Ω := (⊤ : Opens H)) (u := u)).mono_measure (Measure.singularPart_le _ ν))
  have hac_eq : ∫ z : (⊤ : Opens H), ⟪Ψ z, acDerivativeDensity volume ⊤ u ν z⟫ ∂ν =
      ⟪w, (ρ ⋆[lsmul ℝ ℝ, volume] g) y⟫ := by
    have hsub := integral_subtype_comap (μ := volume) (s := ((⊤ : Opens H) : Set H))
      (⊤ : Opens H).isOpen.measurableSet (fun z : H => ⟪w, ρ (y - z) • g z⟫)
    rw [Opens.coe_top, Measure.restrict_univ] at hsub
    have hcongr : (fun z : (⊤ : Opens H) => ⟪Ψ z, acDerivativeDensity volume ⊤ u ν z⟫) =
        fun z : (⊤ : Opens H) => ⟪w, ρ (y - z) • g z⟫ := by
      ext z; simp [Ψ, hφ_apply, g, inner_smul_left, inner_smul_right]
    rw [hcongr, show (∫ z : (⊤ : Opens H), ⟪w, ρ (y - z) • g z⟫ ∂ν) =
      ∫ z : H, ⟪w, ρ (y - z) • g z⟫ from hsub]
    refine ((innerSL ℝ w).integral_comp_comm hac_int).trans ?_
    rw [← convolution_flip]
    simp [convolution_def]
  have hsing_eq : ∫ z : (⊤ : Opens H), ⟪Ψ z, σ z⟫ ∂μs =
      ⟪w, ∫ z : (⊤ : Opens H), ρ (y - z) • σ z ∂μs⟫ := by
    have hcongr : (fun z : (⊤ : Opens H) => ⟪Ψ z, σ z⟫) =
        fun z : (⊤ : Opens H) => ⟪w, ρ (y - z) • σ z⟫ := by
      ext z; simp [Ψ, hφ_apply, inner_smul_left, inner_smul_right]
    rw [hcongr]
    exact (innerSL ℝ w).integral_comp_comm hμs_int
  rw [hd, show ∫ z : H, fderiv ℝ ρ (y - z) w * u z =
    -(-∫ z : H, fderiv ℝ ρ (y - z) w * u z) from (neg_neg _).symm, hleb, hac_eq, hsing_eq,
    inner_add_right]
  ring

/-- Convolving a normalized nonnegative smooth kernel against `σ_u d|Dˢu|` produces an integrable
field on `H` whose `L¹` norm is at most the total singular variation `|Dˢu|(H)`. -/
private theorem integrable_and_ofReal_integral_norm_singular_convolution_le {u : H → ℝ}
    (hu : LocallyIntegrable u volume) (hvar : totalVariationOn volume ⊤ u ≠ ∞)
    {ρ : H → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1) :
    Integrable (fun y : H => ∫ z : (⊤ : Opens H), ρ (y - z) • polarDensity volume ⊤ u z
      ∂(variationMeasure volume ⊤ u).singularPart (volume.comap Subtype.val)) volume ∧
      ENNReal.ofReal (∫ y : H, ‖∫ z : (⊤ : Opens H), ρ (y - z) • polarDensity volume ⊤ u z
        ∂(variationMeasure volume ⊤ u).singularPart (volume.comap Subtype.val)‖) ≤
        (variationMeasure volume ⊤ u).singularPart (volume.comap Subtype.val) univ := by
  have := (⊤ : Opens H).isOpen.locallyCompactSpace
  let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
  let μs : Measure (⊤ : Opens H) := (variationMeasure volume ⊤ u).singularPart ν
  let sρ : H → H := fun y => ∫ z : (⊤ : Opens H), ρ (y - z) • polarDensity volume ⊤ u z ∂μs
  have hfin : ∀ K, IsCompact K → K ⊆ (⊤ : Opens H) →
      ∃ U : Opens H, K ⊆ (U : Set H) ∧ totalVariationOn volume U u ≠ ∞ :=
    fun _ _ hK => ⟨⊤, hK, hvar⟩
  have hμs_fin : μs univ < ∞ :=
    (Measure.singularPart_le _ ν univ).trans_lt
      ((variationMeasure_univ (hu.locallyIntegrableOn _) hfin) ▸ hvar.lt_top)
  have : IsFiniteMeasure μs := ⟨hμs_fin⟩
  have hσ1 : ∀ᵐ z ∂μs, ‖polarDensity volume ⊤ u z‖ = 1 :=
    (Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ ν)).ae_le
      (ae_norm_polarDensity_eq_one (hu.locallyIntegrableOn _) hfin)
  have hsub_cont : Continuous fun p : H × (⊤ : Opens H) => ρ (p.1 - p.2) :=
    hρ.continuous.comp (continuous_fst.sub (continuous_subtype_val.comp continuous_snd))
  have hm_prod : AEStronglyMeasurable
      (fun p : H × (⊤ : Opens H) => ρ (p.1 - p.2) • polarDensity volume ⊤ u p.2)
      (volume.prod μs) :=
    hsub_cont.measurable.aestronglyMeasurable.smul
      (measurable_polarDensity.comp measurable_snd).aestronglyMeasurable
  have hsρ_meas : AEStronglyMeasurable sρ volume := hm_prod.integral_prod_right'
  have hρ_int : Integrable ρ volume := hρ.continuous.integrable_of_hasCompactSupport hρc
  have hbound : ∫⁻ y : H, ‖sρ y‖ₑ ≤ μs univ := by
    calc ∫⁻ y : H, ‖sρ y‖ₑ
        ≤ ∫⁻ y : H, ∫⁻ z : (⊤ : Opens H), ‖ρ (y - z) • polarDensity volume ⊤ u z‖ₑ ∂μs :=
          lintegral_mono fun y => eNorm_integral_le_lintegral_eNorm _
      _ ≤ ∫⁻ y : H, ∫⁻ z : (⊤ : Opens H), ENNReal.ofReal (ρ (y - z)) ∂μs := by
          refine lintegral_mono fun y => lintegral_mono_ae (hσ1.mono fun z hz => ?_)
          rw [← ofReal_norm, norm_smul, hz, mul_one, Real.norm_of_nonneg (hρ0 _)]
      _ = ∫⁻ z : (⊤ : Opens H), (∫⁻ y : H, ENNReal.ofReal (ρ (y - z))) ∂μs :=
          lintegral_lintegral_swap (μ := volume) (ν := μs)
            (ENNReal.continuous_ofReal.comp hsub_cont).measurable.aemeasurable
      _ = ∫⁻ _ : (⊤ : Opens H), 1 ∂μs := by
          refine lintegral_congr fun z => ?_
          rw [lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (ρ y)) (z : H),
            ← ofReal_integral_eq_lintegral_ofReal hρ_int (.of_forall hρ0), hρ1, ENNReal.ofReal_one]
      _ = μs univ := by simp
  have hsρ_int : Integrable sρ volume :=
    ⟨hsρ_meas, hasFiniteIntegral_iff_eNorm.2 (hbound.trans_lt hμs_fin)⟩
  refine ⟨hsρ_int, ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hsρ_int.norm (.of_forall fun _ => norm_nonneg _)]
  simpa only [ofReal_norm] using hbound

end MollifiedBV

section UpperBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Symmetric difference of two centered open intervals in `ℝ` has measure `‖a - b‖ₑ`. -/
private theorem volume_ball_symmDiff_ball {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    volume (ball (0 : ℝ) (a / 2) ∆ ball (0 : ℝ) (b / 2)) = ‖a - b‖ₑ := by
  have hsub {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
      volume (ball (0 : ℝ) (y / 2) \ ball (0 : ℝ) (x / 2)) = ENNReal.ofReal (y - x) := by
    rw [measure_sdiff (ball_subset_ball (by linarith)) measurableSet_ball.nullMeasurableSet
      (by rw [Real.volume_ball]; exact ENNReal.ofReal_ne_top), Real.volume_ball, Real.volume_ball]
    ring_nf
    rw [← ENNReal.ofReal_sub _ hx]
  rcases le_total a b with hab | hba
  · rw [symmDiff_of_le (ball_subset_ball (by linarith)), hsub ha hab,
      Real.eNorm_eq_ofReal_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]
  · rw [symmDiff_comm, symmDiff_of_le (ball_subset_ball (by linarith)), hsub hb hba,
      Real.eNorm_eq_ofReal_abs, abs_of_nonneg (sub_nonneg.2 hba)]

/-- Cavalieri's formula for the symmetric difference between a measurable symmetric slab of width
`w` and a Steiner symmetral. -/
private theorem volume_slab_symmDiff_steinerSymmetrization (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    {w : (ℝ ∙ e)ᗮ → ℝ} (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y) :
    volume ({x : E | |⟪e, x⟫| < w ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) / 2} ∆
        steinerSymmetrization e he s) =
      ∫⁻ y : (ℝ ∙ e)ᗮ, ‖w y - volume.real {t : ℝ | (y : E) + t • e ∈ s}‖ₑ := by
  let π := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  set S := {x : E | |⟪e, x⟫| < w (π x) / 2}
  have hSm : MeasurableSet S :=
    measurableSet_lt (continuous_const.inner continuous_id).abs.measurable
      ((hw.div_const 2).comp π.continuous.measurable)
  rw [volume_eq_lintegral_volume_lineSection e he
    (hSm.nullMeasurableSet.symmDiff (nullMeasurableSet_steinerSymmetrization e he hs))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hyfin
  have hsec_diff : {t : ℝ | (y : E) + t • e ∈ S ∆ steinerSymmetrization e he s} =
      {t : ℝ | (y : E) + t • e ∈ S} ∆ {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s} :=
    rfl
  have hsec_S : {t : ℝ | (y : E) + t • e ∈ S} = ball (0 : ℝ) (w y / 2) := by
    ext t
    have hπ : π ((y : E) + t • e) = y := by
      rw [map_add, (ℝ ∙ e)ᗮ.orthogonalProjectionOnto_mem_subspace_eq_self y, map_smul,
        Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, smul_zero,
        add_zero]
    change |⟪e, (y : E) + t • e⟫| < w (π ((y : E) + t • e)) / 2 ↔ t ∈ ball (0 : ℝ) (w y / 2)
    rw [inner_add_smul e he, hπ, mem_ball_zero_iff, Real.norm_eq_abs]
  have hsec_st : {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s} =
      ball (0 : ℝ) (volume.real {t : ℝ | (y : E) + t • e ∈ s} / 2) := by
    rw [lineSection_steinerSymmetrization]
    ext t
    have hrad : volume {t : ℝ | (y : E) + t • e ∈ s} / 2 =
        ENNReal.ofReal (volume.real {t : ℝ | (y : E) + t • e ∈ s} / 2) := by
      rw [ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_ofNat, measureReal_def,
        ENNReal.ofReal_toReal hyfin.ne]
    rw [mem_eball, mem_ball, edist_zero_right, dist_zero_right, Real.eNorm_eq_ofReal_abs,
      Real.norm_eq_abs, hrad, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)]
  rw [hsec_diff, hsec_S, hsec_st, volume_ball_symmDiff_ball (hw0 y) measureReal_nonneg]

/-- For a finite-volume null-measurable set `s`, the section-length function `y ↦ |s_y|` is
integrable on `(ℝ ∙ e)ᗮ`. -/
private theorem integrable_measureReal_lineSection (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞) :
    Integrable (fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) volume := by
  have hm := (aemeasurable_volume_lineSection e he hs).ennreal_toReal
  refine ⟨hm.aestronglyMeasurable, hasFiniteIntegral_iff_eNorm.2 ?_⟩
  have hcongr : (fun y : (ℝ ∙ e)ᗮ => ‖volume.real {t : ℝ | (y : E) + t • e ∈ s}‖ₑ) =ᵐ[volume]
      fun y => volume {t : ℝ | (y : E) + t • e ∈ s} := by
    filter_upwards [ae_volume_lineSection_lt_top e he hs hfin] with y hy
    rw [Real.eNorm_of_nonneg measureReal_nonneg, measureReal_def, ENNReal.ofReal_toReal hy.ne]
  rw [lintegral_congr_ae hcongr, ← volume_eq_lintegral_volume_lineSection e he hs]
  exact hfin.lt_top

/-- Pointwise bound on the symmetric-slab boundary integrand for a mollified width `w = ρ ⋆ v`,
splitting across `MD` and `MDᶜ`. -/
private theorem slab_mollified_pointwise_le (e : E) (he : ‖e‖ = 1)
    {v : (ℝ ∙ e)ᗮ → ℝ} (hv : Integrable v volume) (hvar : totalVariationOn volume ⊤ v ≠ ∞)
    (MD : Set (ℝ ∙ e)ᗮ) {ρ : (ℝ ∙ e)ᗮ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) (hw0 : ∀ y, 0 ≤ (ρ ⋆[lsmul ℝ ℝ, volume] v) y)
    {ψ : E → E} (hψ : ContDiff ℝ 1 ψ) (hψ1 : ∀ x, ‖ψ x‖ ≤ 1)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ ψ x‖ ≤ M) (y : (ℝ ∙ e)ᗮ) :
    let π := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
    let w := ρ ⋆[lsmul ℝ ℝ, volume] v
    let g : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ := fun z =>
      acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) ⟨z, trivial⟩
    let sρ : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ := fun y =>
      ∫ z : (⊤ : Opens (ℝ ∙ e)ᗮ), ρ (y - z) • polarDensity volume ⊤ v z
        ∂(variationMeasure volume ⊤ v).singularPart (volume.comap Subtype.val)
    ⟪e, ψ ((y : E) + (w y / 2) • e) - ψ ((y : E) - (w y / 2) • e)⟫ -
        (2 : ℝ)⁻¹ * fderiv ℝ w y (π (ψ ((y : E) + (w y / 2) • e) + ψ ((y : E) - (w y / 2) • e))) ≤
      (MD.indicator (fun y => √(4 + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖ ^ 2)) y +
        MDᶜ.indicator (fun y => M * w y + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖) y) + ‖sρ y‖ := by
  intro π w g sρ
  set z₁ := ψ ((y : E) + (w y / 2) • e)
  set z₂ := ψ ((y : E) - (w y / 2) • e)
  have hz₁ : ‖z₁‖ ≤ 1 := hψ1 _
  have hz₂ : ‖z₂‖ ≤ 1 := hψ1 _
  have hfd : fderiv ℝ w y (π (z₁ + z₂)) = ⟪π (z₁ + z₂), (ρ ⋆[lsmul ℝ ℝ, volume] g) y + sρ y⟫ :=
    fderiv_convolution_eq_inner_add_singular hv.locallyIntegrable hvar hρ hρc y (π (z₁ + z₂))
  rw [hfd]
  by_cases hy : y ∈ MD
  · have hyc : y ∉ MDᶜ := fun h => h hy
    simp only [indicator_of_mem hy, indicator_of_notMem hyc, add_zero]
    rw [inner_add_right, mul_add, sub_add_eq_sub_sub]
    have hmain := slab_boundary_le_sqrt he hz₁ hz₂ ((ρ ⋆[lsmul ℝ ℝ, volume] g) y)
    have hπz (z : E) : ‖(π z : E)‖ ≤ ‖z‖ := by
      have : ⟪e, z⟫ ^ 2 + ‖(π z : E)‖ ^ 2 = ‖z‖ ^ 2 :=
        sq_inner_add_norm_orthogonalProjectionOnto_sq he z
      exact le_of_sq_le_sq (by nlinarith [sq_nonneg ⟪e, z⟫]) (norm_nonneg z)
    have hπ2 : ‖π (z₁ + z₂)‖ ≤ 2 := by
      change ‖(π (z₁ + z₂) : E)‖ ≤ 2
      rw [map_add, Submodule.coe_add]
      linarith [norm_add_le (π z₁ : E) (π z₂ : E), hπz z₁, hπz z₂, hz₁, hz₂]
    have hcs := (neg_le_abs _).trans (abs_real_inner_le_norm (π (z₁ + z₂)) (sρ y))
    nlinarith [norm_nonneg (sρ y)]
  · have hyc : y ∈ MDᶜ := hy
    simp only [indicator_of_notMem hy, indicator_of_mem hyc, zero_add]
    have hseg := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hψ.differentiable one_ne_zero x) (fun x _ => hM x)
      (mem_univ ((y : E) - (w y / 2) • e)) (mem_univ ((y : E) + (w y / 2) • e))
    have hnorm_seg : ‖((y : E) + (w y / 2) • e) - ((y : E) - (w y / 2) • e)‖ = w y := by
      rw [show ((y : E) + (w y / 2) • e) - ((y : E) - (w y / 2) • e) = w y • e by module,
        norm_smul, Real.norm_of_nonneg (hw0 y), he, mul_one]
    rw [hnorm_seg] at hseg
    have hseg' : ‖z₁ - z₂‖ ≤ M * w y := hseg
    have := slab_boundary_le_off he hz₁ hz₂ hseg' ((ρ ⋆[lsmul ℝ ℝ, volume] g) y) (sρ y)
    linarith

/-- Smooth-slab divergence estimate for a single mollified width `w = ρ ⋆ v`. -/
private theorem setIntegral_slab_mollified_le (e : E) (he : ‖e‖ = 1)
    {v : (ℝ ∙ e)ᗮ → ℝ} (hv : Integrable v volume) (hv0 : ∀ y, 0 ≤ v y)
    (hvar : totalVariationOn volume ⊤ v ≠ ∞)
    {MD : Set (ℝ ∙ e)ᗮ} (hMDm : MeasurableSet MD) (hMDfin : volume MD ≠ ∞)
    {ρ : (ℝ ∙ e)ᗮ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1)
    {ψ : E → E} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hψ1 : ∀ x, ‖ψ x‖ ≤ 1)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ ψ x‖ ≤ M) :
    ∫ x in {x : E | |⟪e, x⟫| <
        (ρ ⋆[lsmul ℝ ℝ, volume] v) ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) / 2},
        LinearMap.trace ℝ E (fderiv ℝ ψ x : E →ₗ[ℝ] E) ≤
      (∫ y in MD, √(4 + ‖(ρ ⋆[lsmul ℝ ℝ, volume] fun z : (ℝ ∙ e)ᗮ =>
            acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) ⟨z, trivial⟩) y‖ ^ 2)) +
        (∫ y in MDᶜ, ‖(ρ ⋆[lsmul ℝ ℝ, volume] fun z : (ℝ ∙ e)ᗮ =>
            acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) ⟨z, trivial⟩) y‖) +
        M * (∫ y in MDᶜ, (ρ ⋆[lsmul ℝ ℝ, volume] v) y) +
        ∫ y : (ℝ ∙ e)ᗮ, ‖∫ z : (⊤ : Opens (ℝ ∙ e)ᗮ), ρ (y - z) • polarDensity volume ⊤ v z
          ∂(variationMeasure volume ⊤ v).singularPart (volume.comap Subtype.val)‖ := by
  let ν : Measure (⊤ : Opens (ℝ ∙ e)ᗮ) := volume.comap Subtype.val
  let g : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ := fun z => acDerivativeDensity volume ⊤ v ν ⟨z, trivial⟩
  let sρ : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ := fun y =>
    ∫ z : (⊤ : Opens (ℝ ∙ e)ᗮ), ρ (y - z) • polarDensity volume ⊤ v z
      ∂(variationMeasure volume ⊤ v).singularPart ν
  let w : (ℝ ∙ e)ᗮ → ℝ := ρ ⋆[lsmul ℝ ℝ, volume] v
  have hw : ContDiff ℝ 1 w :=
    hρc.contDiff_convolution_left _ (hρ.of_le (by simp)) hv.locallyIntegrable
  have hw0 (y : (ℝ ∙ e)ᗮ) : 0 ≤ w y := by
    dsimp only [w]; rw [convolution_def]
    exact integral_nonneg fun z => mul_nonneg (hρ0 z) (hv0 _)
  have hg : Integrable g volume := integrable_acDerivativeDensity_on_univ hv.locallyIntegrable hvar
  have hρ_int : Integrable ρ volume := hρ.continuous.integrable_of_hasCompactSupport hρc
  have hgk : Integrable (ρ ⋆[lsmul ℝ ℝ, volume] g) volume :=
    hρ_int.integrable_convolution (lsmul ℝ ℝ) hg
  have hwk : Integrable w volume := hρ_int.integrable_convolution (lsmul ℝ ℝ) hv
  have hsρ : Integrable sρ volume :=
    (integrable_and_ofReal_integral_norm_singular_convolution_le
      hv.locallyIntegrable hvar hρ hρc hρ0 hρ1).1
  have hint_MD : Integrable (MD.indicator fun y => √(4 + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖ ^ 2))
      volume := by
    rw [integrable_indicator_iff hMDm]
    refine ((integrableOn_const (C := (2 : ℝ)) hMDfin).add hgk.norm.integrableOn).mono' ?_ ?_
    · exact (Real.continuous_sqrt.comp (continuous_const.add
        (continuous_norm.pow 2))).comp_aestronglyMeasurable hgk.aestronglyMeasurable.restrict
    · exact .of_forall fun _ =>
        (Real.norm_of_nonneg (Real.sqrt_nonneg _)).trans_le (sqrt_four_add_norm_sq_le _)
  have hint_MDc : Integrable (MDᶜ.indicator fun y =>
      M * w y + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖) volume :=
    (integrable_indicator_iff hMDm.compl).2 ((hwk.const_mul M).add hgk.norm).integrableOn
  have hint_sum : Integrable (fun y => (MD.indicator (fun y =>
      √(4 + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖ ^ 2)) y +
      MDᶜ.indicator (fun y => M * w y + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖) y) + ‖sρ y‖) volume :=
    ((hint_MD.add hint_MDc).add hsρ.norm).congr (.of_forall fun _ => by simp)
  have hint_12 : Integrable (fun y => MD.indicator (fun y =>
      √(4 + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖ ^ 2)) y +
      MDᶜ.indicator (fun y => M * w y + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖) y) volume :=
    (hint_MD.add hint_MDc).congr (.of_forall fun _ => by simp)
  rw [setIntegral_setOf_abs_inner_lt_div_two_trace_fderiv e he hw hw0 hψ hψc]
  refine (integral_mono (integrable_slab_boundary_integrand e hw hψ hψc) hint_sum
    (slab_mollified_pointwise_le e he hv hvar MD hρ hρc hw0 hψ hψ1 hM)).trans_eq ?_
  rw [integral_add hint_12 hsρ.norm, integral_add hint_MD hint_MDc,
    integral_indicator hMDm, integral_indicator hMDm.compl,
    integral_add (hwk.const_mul M).integrableOn hgk.norm.integrableOn, integral_const_mul]
  dsimp only [g, w, sρ, ν]
  ring

/-- As `k → ∞`, the divergence integrals over the mollified symmetric slabs converge to the
distributional divergence pairing with `steinerSymmetrization e he s`. -/
private theorem tendsto_setIntegral_slab_trace_fderiv (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (β : ℕ → ContDiffBump (0 : (ℝ ∙ e)ᗮ))
    (hβ : Tendsto (fun k => (β k).rOut) atTop (𝓝 0)) (ψ : 𝓓((⊤ : Opens E), E)) :
    Tendsto (fun k => ∫ x in {x : E | |⟪e, x⟫| <
        ((β k).normed volume ⋆[lsmul ℝ ℝ, volume]
          fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s})
          ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) / 2},
        LinearMap.trace ℝ E (fderiv ℝ (ψ : E → E) x : E →ₗ[ℝ] E)) atTop
      (𝓝 (∫ x, divergenceCLM ψ x * (steinerSymmetrization e he s).indicator 1 x)) := by
  let π := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  let v : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
  have hv : Integrable v volume := integrable_measureReal_lineSection e he hs hfin
  have hconv_v := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_lintegral_enorm_normed_convolution_sub hβ hv)
  rw [Function.comp_def, ENNReal.toReal_zero] at hconv_v
  let C : ℝ := ‖(divergenceCLM ψ : E →ᵇ ℝ)‖
  have hC (x : E) : ‖divergenceCLM ψ x‖ ≤ C :=
    BoundedContinuousFunction.norm_coe_le_norm (divergenceCLM ψ : E →ᵇ ℝ) x
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_)
    (by simpa using hconv_v.const_mul C))
  let wk := (β k).normed volume ⋆[lsmul ℝ ℝ, volume] v
  let Sk := {x : E | |⟪e, x⟫| < wk (π x) / 2}
  have hwk_cont : Continuous wk :=
    (β k).hasCompactSupport_normed.continuous_convolution_left _
      (β k).continuous_normed hv.locallyIntegrable
  have hwk0 (y : (ℝ ∙ e)ᗮ) : 0 ≤ wk y := by
    dsimp only [wk]; rw [convolution_def]
    exact integral_nonneg fun z => mul_nonneg ((β k).nonneg_normed z) measureReal_nonneg
  have hSkm : MeasurableSet Sk :=
    measurableSet_lt (continuous_const.inner continuous_id).abs.measurable
      ((hwk_cont.div_const 2).comp π.continuous).measurable
  -- Rewrite the divergence integral on `Sk` via indicator multiplication.
  have hSk_eq : ∫ x in Sk, LinearMap.trace ℝ E (fderiv ℝ (ψ : E → E) x : E →ₗ[ℝ] E) =
      ∫ x, divergenceCLM ψ x * Sk.indicator 1 x := by
    simp_rw [← divergenceCLM_apply]
    rw [← integral_indicator hSkm]
    exact integral_congr_ae (.of_forall fun x => by by_cases hx : x ∈ Sk <;> simp [hx])
  have hint_div : Integrable (divergenceCLM ψ) volume :=
    (divergenceCLM ψ).continuous.integrable_of_hasCompactSupport (divergenceCLM ψ).hasCompactSupport
  have hint_mul {T : Set E} (hTm : NullMeasurableSet T volume) :
      Integrable (fun x => divergenceCLM ψ x * T.indicator 1 x) volume :=
    (hint_div.indicator₀ hTm).congr (.of_forall fun x => by by_cases hx : x ∈ T <;> simp [hx])
  -- Bound the difference by `C` times the symmetric-difference volume.
  have hsymm_m := hSkm.nullMeasurableSet.symmDiff (nullMeasurableSet_steinerSymmetrization e he hs)
  have hsymm_fin : volume (Sk ∆ steinerSymmetrization e he s) ≠ ∞ := by
    rw [volume_slab_symmDiff_steinerSymmetrization e he hs hfin hwk_cont.measurable hwk0]
    exact (hasFiniteIntegral_iff_eNorm.1
      (((β k).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hv).sub hv).2).ne
  have hint_C : Integrable ((Sk ∆ steinerSymmetrization e he s).indicator fun _ => C) volume :=
    (integrable_indicator_iff₀ hsymm_m).2 (integrableOn_const hsymm_fin)
  rw [hSk_eq, dist_eq_norm, ← integral_sub (hint_mul hSkm.nullMeasurableSet)
    (hint_mul (nullMeasurableSet_steinerSymmetrization e he hs))]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono
    ((hint_mul hSkm.nullMeasurableSet).sub
      (hint_mul (nullMeasurableSet_steinerSymmetrization e he hs))).norm
    hint_C fun x => ?_).trans_eq ?_)
  · dsimp only [Pi.sub_apply]
    by_cases hx1 : x ∈ Sk <;> by_cases hx2 : x ∈ steinerSymmetrization e he s <;>
      simp only [symmDiff_def, mem_union, Set.mem_sdiff, hx1, hx2, not_true_eq_false,
        not_false_eq_true, and_self, and_false, false_and, or_false, false_or, indicator_of_mem,
        indicator_of_notMem, Pi.one_apply, mul_one, mul_zero, sub_self, sub_zero, zero_sub,
        norm_zero, norm_neg, le_refl] <;>
      exact hC x
  · rw [integral_indicator₀ hsymm_m, setIntegral_const, smul_eq_mul, mul_comm, measureReal_def,
      volume_slab_symmDiff_steinerSymmetrization e he hs hfin hwk_cont.measurable hwk0]

/-- Express the `L¹` norm of a difference of integrable functions as
`(∫⁻ y, ‖f₁ y - f₂ y‖ₑ).toReal`. -/
private theorem integral_norm_sub_eq_toReal_lintegral {H F : Type*} [MeasurableSpace H]
    [NormedAddCommGroup F] {μ : Measure H} {f₁ f₂ : H → F}
    (hf₁ : Integrable f₁ μ) (hf₂ : Integrable f₂ μ) :
    ∫ y, ‖(f₁ - f₂) y‖ ∂μ = (∫⁻ y, ‖f₁ y - f₂ y‖ₑ ∂μ).toReal := by
  simp_rw [← ofReal_norm, ← Pi.sub_apply]
  rw [← ofReal_integral_eq_lintegral_ofReal (hf₁.sub hf₂).norm (.of_forall fun _ => norm_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]

/-- As `k → ∞`, the three non-singular mollified upper-bound integrals converge to
`∫_MD √(4 + ‖g‖²) + ∫_{MDᶜ} ‖g‖`. -/
private theorem tendsto_mollified_upper_rhs {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {v : H → ℝ} (hv : Integrable v volume) (hv0 : ∀ y, 0 ≤ v y)
    {g : H → H} (hg : Integrable g volume)
    {MD : Set H} (hMDm : MeasurableSet MD) (hMDfin : volume MD ≠ ∞)
    (hv_zero : ∀ y ∈ MDᶜ, v y = 0) {M : ℝ} (hM0 : 0 ≤ M)
    (β : ℕ → ContDiffBump (0 : H)) (hβ : Tendsto (fun k => (β k).rOut) atTop (𝓝 0)) :
    Tendsto (fun k =>
      (∫ y in MD, √(4 + ‖((β k).normed volume ⋆[lsmul ℝ ℝ, volume] g) y‖ ^ 2)) +
        (∫ y in MDᶜ, ‖((β k).normed volume ⋆[lsmul ℝ ℝ, volume] g) y‖) +
        M * ∫ y in MDᶜ, ((β k).normed volume ⋆[lsmul ℝ ℝ, volume] v) y) atTop
      (𝓝 ((∫ y in MD, √(4 + ‖g y‖ ^ 2)) + ∫ y in MDᶜ, ‖g y‖)) := by
  let wk (k : ℕ) := (β k).normed volume ⋆[lsmul ℝ ℝ, volume] v
  let gk (k : ℕ) := (β k).normed volume ⋆[lsmul ℝ ℝ, volume] g
  have hconv_v := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_lintegral_enorm_normed_convolution_sub hβ hv)
  have hconv_g := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_lintegral_enorm_normed_convolution_sub hβ hg)
  rw [Function.comp_def, ENNReal.toReal_zero] at hconv_v hconv_g
  have hint_sqrt {f : H → H} (hf : Integrable f volume) :
      IntegrableOn (fun y => √(4 + ‖f y‖ ^ 2)) MD volume :=
    ((integrableOn_const (C := (2 : ℝ)) hMDfin).add hf.norm.integrableOn).mono'
      ((Real.continuous_sqrt.comp (continuous_const.add
        (continuous_norm.pow 2))).comp_aestronglyMeasurable hf.aestronglyMeasurable.restrict)
      (.of_forall fun _ =>
        (Real.norm_of_nonneg (Real.sqrt_nonneg _)).trans_le (sqrt_four_add_norm_sq_le _))
  have hrhs1 : Tendsto (fun k => ∫ y in MD, √(4 + ‖gk k y‖ ^ 2)) atTop
      (𝓝 (∫ y in MD, √(4 + ‖g y‖ ^ 2))) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_)
      hconv_g)
    have hgk : Integrable (gk k) volume :=
      (β k).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hg
    rw [dist_eq_norm, ← integral_sub (hint_sqrt hgk) (hint_sqrt hg),
      ← integral_norm_sub_eq_toReal_lintegral hgk hg]
    exact (norm_integral_le_integral_norm _).trans ((integral_mono
      ((hint_sqrt hgk).sub (hint_sqrt hg)).norm (hgk.sub hg).norm.integrableOn
      fun _ => (Real.norm_eq_abs _).trans_le (abs_sqrt_four_add_norm_sq_sub_le _ _)).trans
      (setIntegral_le_integral (hgk.sub hg).norm (.of_forall fun _ => norm_nonneg _)))
  have hrhs2 : Tendsto (fun k => ∫ y in MDᶜ, ‖gk k y‖) atTop (𝓝 (∫ y in MDᶜ, ‖g y‖)) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_)
      hconv_g)
    have hgk : Integrable (gk k) volume :=
      (β k).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hg
    rw [dist_eq_norm, ← integral_sub hgk.norm.integrableOn hg.norm.integrableOn,
      ← integral_norm_sub_eq_toReal_lintegral hgk hg]
    exact (norm_integral_le_integral_norm _).trans ((integral_mono
      (hgk.norm.integrableOn.sub hg.norm.integrableOn).norm (hgk.sub hg).norm.integrableOn
      fun _ => (Real.norm_eq_abs _).trans_le (abs_norm_sub_norm_le _ _)).trans
      (setIntegral_le_integral (hgk.sub hg).norm (.of_forall fun _ => norm_nonneg _)))
  have hrhs3 : Tendsto (fun k => M * ∫ y in MDᶜ, wk k y) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => mul_nonneg hM0 (integral_nonneg fun _ =>
      integral_nonneg fun z => mul_nonneg ((β k).nonneg_normed z) (hv0 _)))
      (fun k => ?_) (by simpa using hconv_v.const_mul M)
    have hwk : Integrable (wk k) volume :=
      (β k).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hv
    rw [← integral_norm_sub_eq_toReal_lintegral hwk hv]
    refine mul_le_mul_of_nonneg_left ((setIntegral_mono_on hwk.integrableOn
      (hwk.sub hv).norm.integrableOn hMDm.compl fun y hy => ?_).trans
      (setIntegral_le_integral (hwk.sub hv).norm (.of_forall fun _ => norm_nonneg _))) hM0
    dsimp only [Pi.sub_apply]
    rw [hv_zero y hy, sub_zero]
    exact (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm
  simpa only [add_zero] using (hrhs1.add hrhs2).add hrhs3

/-- Convert `(∫⁻_D √(4 + ‖g‖²)) + (∫⁻_{Dᶜ} ‖g‖ₑ)` to `ENNReal.ofReal` of the corresponding Bochner
sum on the measurable hull `MD` of `D`. -/
private theorem setLIntegral_sqrt_add_enorm_eq_ofReal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {g : H → H} (hg : Integrable g volume) {D MD : Set H}
    (hMDfin : volume MD ≠ ∞) (hMD_ae : D =ᵐ[volume] MD) :
    (∫⁻ y in D, ENNReal.ofReal √(4 + ‖g y‖ ^ 2)) + (∫⁻ y in Dᶜ, ‖g y‖ₑ) =
      ENNReal.ofReal ((∫ y in MD, √(4 + ‖g y‖ ^ 2)) + ∫ y in MDᶜ, ‖g y‖) := by
  have hint_sqrt : IntegrableOn (fun y => √(4 + ‖g y‖ ^ 2)) MD volume :=
    ((integrableOn_const (C := (2 : ℝ)) hMDfin).add hg.norm.integrableOn).mono'
      ((Real.continuous_sqrt.comp (continuous_const.add
        (continuous_norm.pow 2))).comp_aestronglyMeasurable hg.aestronglyMeasurable.restrict)
      (.of_forall fun _ =>
        (Real.norm_of_nonneg (Real.sqrt_nonneg _)).trans_le (sqrt_four_add_norm_sq_le _))
  rw [setLIntegral_congr hMD_ae, setLIntegral_congr hMD_ae.compl,
    ENNReal.ofReal_add (integral_nonneg fun _ => Real.sqrt_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hint_sqrt (.of_forall fun _ => Real.sqrt_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hg.norm.integrableOn (.of_forall fun _ => norm_nonneg _)]
  simp only [ofReal_norm]

/-- **De Giorgi–Chlebík–Cianchi–Fusco upper bound on the perimeter of a Steiner symmetral.**
For a null-measurable set `s` of finite volume and finite perimeter, the perimeter of its Steiner
symmetral along a unit vector `e` is bounded above by
`∫_D √(4 + ‖∇ᵃv‖²) + ∫_{Dᶜ} ‖∇ᵃv‖ + |Dˢv|((ℝ ∙ e)ᗮ)`, where `v(y) = |{t | y + t • e ∈ s}|` and
`D = {y | 0 < |{t | y + t • e ∈ s}|}`. -/
theorem perimeter_steinerSymmetrization_le_lintegral_add_singularPart
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) (e : E) (he : ‖e‖ = 1) :
    perimeter volume ⊤ (steinerSymmetrization e he s) ≤
      (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}},
          ENNReal.ofReal √(4 + ‖acDerivativeDensity volume ⊤
            (fun z : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (z : E) + t • e ∈ s})
            (volume.comap Subtype.val) ⟨y, trivial⟩‖ ^ 2)) +
        (∫⁻ y in {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}ᶜ,
          ‖acDerivativeDensity volume ⊤
            (fun z : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (z : E) + t • e ∈ s})
            (volume.comap Subtype.val) ⟨y, trivial⟩‖ₑ) +
        (variationMeasure volume ⊤
          (fun z : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (z : E) + t • e ∈ s})).singularPart
          (volume.comap Subtype.val) univ := by
  let ν : Measure (⊤ : Opens (ℝ ∙ e)ᗮ) := volume.comap Subtype.val
  let v : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let g : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ := fun y => acDerivativeDensity volume ⊤ v ν ⟨y, trivial⟩
  let μs : Measure (⊤ : Opens (ℝ ∙ e)ᗮ) := (variationMeasure volume ⊤ v).singularPart ν
  let D : Set (ℝ ∙ e)ᗮ := {y | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  have hv : Integrable v volume := integrable_measureReal_lineSection e he hs hfin
  have hvar : totalVariationOn volume ⊤ v ≠ ∞ :=
    ne_top_of_le_ne_top hP (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  have hg : Integrable g volume := integrable_acDerivativeDensity_on_univ hv.locallyIntegrable hvar
  have hD : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hDfin : volume D ≠ ∞ := by
    have h2 := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
      hs hfin e he (A := (∅ : Set (ℝ ∙ e)ᗮ)) MeasurableSet.empty.nullMeasurableSet
      (.of_forall fun _ h => False.elim h)
    intro htop
    rw [show {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} = D from rfl, htop,
      ENNReal.mul_top two_ne_zero, top_add, top_le_iff] at h2
    exact hP h2
  let MD := toMeasurable volume D
  have hMDm : MeasurableSet MD := measurableSet_toMeasurable volume D
  have hMD_ae : D =ᵐ[volume] MD := (NullMeasurableSet.toMeasurable_ae_eq hD).symm
  have hMDfin : volume MD ≠ ∞ := by rwa [measure_toMeasurable]
  rw [setLIntegral_sqrt_add_enorm_eq_ofReal hg hMDfin hMD_ae, perimeter_def,
    totalVariationOn_le_iff]
  intro ψ hψ1
  have hψd : ContDiff ℝ 1 (ψ : E → E) := ψ.contDiff.of_le (by simp)
  obtain ⟨M₀, hM₀⟩ := (hψd.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (ψ.hasCompactSupport.fderiv ℝ)
  let β : ℕ → ContDiffBump (0 : (ℝ ∙ e)ᗮ) := fun k =>
    ⟨1 / (k + 2), 1 / (k + 1), by positivity, by gcongr; norm_num⟩
  have hβ : Tendsto (fun k => (β k).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hv_zero (y : (ℝ ∙ e)ᗮ) (hy : y ∈ MDᶜ) : v y = 0 := by
    have hvol0 : volume {t : ℝ | (y : E) + t • e ∈ s} = 0 :=
      nonpos_iff_eq_zero.1 (not_lt.1 fun h => hy (subset_toMeasurable volume D h))
    simp [v, measureReal_def, hvol0]
  have hrhs := (ENNReal.tendsto_ofReal (tendsto_mollified_upper_rhs hv (fun _ => measureReal_nonneg)
    hg hMDm hMDfin hv_zero (le_max_right M₀ 0) β hβ)).add (tendsto_const_nhds (x := μs univ))
  refine le_of_tendsto_of_tendsto (ENNReal.tendsto_ofReal
    (tendsto_setIntegral_slab_trace_fderiv e he hs hfin β hβ ψ)) hrhs (.of_forall fun k => ?_)
  have hslab := setIntegral_slab_mollified_le e he hv (fun _ => measureReal_nonneg) hvar
    hMDm hMDfin (β k).contDiff_normed (β k).hasCompactSupport_normed (β k).nonneg_normed
    (β k).integral_normed hψd ψ.hasCompactSupport hψ1 fun x => (hM₀ x).trans (le_max_left M₀ 0)
  have hsing := (integrable_and_ofReal_integral_norm_singular_convolution_le hv.locallyIntegrable
    hvar (β k).contDiff_normed (β k).hasCompactSupport_normed (β k).nonneg_normed
    (β k).integral_normed).2
  exact (ENNReal.ofReal_le_ofReal hslab).trans
    (ENNReal.ofReal_add_le.trans (add_le_add_right hsing _))

end UpperBound

section Rigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Construct the measurable calibration field `Φ₀ : (⊤ : Opens H) → H` of norm at most `1`
capturing the absolutely continuous density on `D'`, on `D'ᶜ`, and the singular polar density. -/
private theorem exists_measurable_calibrationField {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {v : H → ℝ} (hv : LocallyIntegrable v volume) (hvar : totalVariationOn volume ⊤ v ≠ ∞)
    {MD : Set H} (hMDm : MeasurableSet MD) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    let gΩ : (⊤ : Opens H) → H := acDerivativeDensity volume ⊤ v ν
    let μs : Measure (⊤ : Opens H) := (variationMeasure volume ⊤ v).singularPart ν
    let D' : Set (⊤ : Opens H) := Subtype.val ⁻¹' MD
    ∃ Φ₀ : (⊤ : Opens H) → H,
      Measurable Φ₀ ∧ (∀ z, ‖Φ₀ z‖ ≤ 1) ∧
      (∀ᵐ z ∂ν, z ∈ D' → Φ₀ z = -(√(4 + ‖gΩ z‖ ^ 2))⁻¹ • gΩ z) ∧
      (∀ᵐ z ∂ν, z ∉ D' → Φ₀ z = -‖gΩ z‖⁻¹ • gΩ z) ∧
      (∀ᵐ z ∂μs, -⟪Φ₀ z, polarDensity volume ⊤ v z⟫ = 1) := by
  classical
  intro ν gΩ μs D'
  have := (⊤ : Opens H).isOpen.locallyCompactSpace
  let σ := polarDensity volume ⊤ v
  have hfin : ∀ K, IsCompact K → K ⊆ (⊤ : Opens H) →
      ∃ U : Opens H, K ⊆ (U : Set H) ∧ totalVariationOn volume U v ≠ ∞ :=
    fun _ _ hK => ⟨⊤, hK, hvar⟩
  have hmut := Measure.mutuallySingular_singularPart (variationMeasure volume ⊤ v) ν
  let N := hmut.nullSet
  let Φ₀ : (⊤ : Opens H) → H := fun z =>
    if z ∈ N then
      if z ∈ D' then -(√(4 + ‖gΩ z‖ ^ 2))⁻¹ • gΩ z else -‖gΩ z‖⁻¹ • gΩ z
    else -‖σ z‖⁻¹ • σ z
  have hΦ₀m : Measurable Φ₀ := by
    have h1 : Measurable fun z : (⊤ : Opens H) => -(√(4 + ‖gΩ z‖ ^ 2))⁻¹ • gΩ z :=
      ((Real.continuous_sqrt.comp (continuous_const.add
        (continuous_norm.pow 2))).measurable.comp (measurable_acDerivativeDensity ν)).inv.neg.smul
        (measurable_acDerivativeDensity ν)
    have h2 : Measurable fun z : (⊤ : Opens H) => -‖gΩ z‖⁻¹ • gΩ z :=
      (measurable_acDerivativeDensity ν).norm.inv.neg.smul (measurable_acDerivativeDensity ν)
    have h3 : Measurable fun z : (⊤ : Opens H) => -‖σ z‖⁻¹ • σ z :=
      measurable_polarDensity.norm.inv.neg.smul measurable_polarDensity
    exact Measurable.ite hmut.measurableSet_nullSet
      (Measurable.ite (hMDm.preimage continuous_subtype_val.measurable) h1 h2) h3
  have hΦ₀1 (z : (⊤ : Opens H)) : ‖Φ₀ z‖ ≤ 1 := by
    have hunit (u : H) : ‖-‖u‖⁻¹ • u‖ ≤ 1 := by
      rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_inv, abs_norm]
      by_cases hu0 : ‖u‖ = 0 <;> simp [hu0]
    dsimp only [Φ₀]
    split_ifs
    · rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
        inv_mul_le_iff₀ (Real.sqrt_pos.2 (by positivity)), mul_one]
      exact Real.le_sqrt_of_sq_le (by linarith)
    · exact hunit _
    · exact hunit _
  have haeN : ∀ᵐ z ∂ν, z ∈ N := by rw [ae_iff]; exact hmut.measure_compl_nullSet
  have haeNc : ∀ᵐ z ∂μs, z ∉ N := by
    rw [ae_iff]
    have : {z : (⊤ : Opens H) | ¬z ∉ N} = N := by ext z; simp
    rw [this]
    exact hmut.measure_nullSet
  have hσ1 : ∀ᵐ z ∂μs, ‖σ z‖ = 1 :=
    (Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ ν)).ae_le
      (ae_norm_polarDensity_eq_one (hv.locallyIntegrableOn _) hfin)
  refine ⟨Φ₀, hΦ₀m, hΦ₀1, haeN.mono fun z hzN hzD => by simp [Φ₀, hzN, hzD],
    haeN.mono fun z hzN hzD => by simp [Φ₀, hzN, hzD], ?_⟩
  filter_upwards [haeNc, hσ1] with z hzN hzσ
  dsimp only [Φ₀, σ] at hzσ ⊢
  simp [hzN, hzσ]

/-- Approximate `Φ₀` by smooth compactly supported test fields `φ k` of norm at most `1` in `L¹`
against `ν.restrict D' + ν.withDensity ‖∇ᵃv‖ₑ + |Dˢv|`. -/
private theorem exists_calibration_testFunction_seq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {v : H → ℝ} (hv : LocallyIntegrable v volume) (hvar : totalVariationOn volume ⊤ v ≠ ∞)
    {MD : Set H} (hMDm : MeasurableSet MD) (hMDfin : volume MD ≠ ∞) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    let gΩ : (⊤ : Opens H) → H := acDerivativeDensity volume ⊤ v ν
    let μs : Measure (⊤ : Opens H) := (variationMeasure volume ⊤ v).singularPart ν
    let D' : Set (⊤ : Opens H) := Subtype.val ⁻¹' MD
    ∃ (Φ₀ : (⊤ : Opens H) → H) (φ : ℕ → 𝓓((⊤ : Opens H), H)),
      Measurable Φ₀ ∧ (∀ z, ‖Φ₀ z‖ ≤ 1) ∧ (∀ k y, ‖φ k y‖ ≤ 1) ∧
      (∀ᵐ z ∂ν, z ∈ D' → Φ₀ z = -(√(4 + ‖gΩ z‖ ^ 2))⁻¹ • gΩ z) ∧
      (∀ᵐ z ∂ν, z ∉ D' → Φ₀ z = -‖gΩ z‖⁻¹ • gΩ z) ∧
      (∀ᵐ z ∂μs, -⟪Φ₀ z, polarDensity volume ⊤ v z⟫ = 1) ∧
      (∀ k, ∫⁻ z in D', ‖Φ₀ z - φ k z‖ₑ ∂ν ≤ (1 / 2 : ℝ≥0∞) ^ k) ∧
      (∀ k, ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ * ‖gΩ z‖ₑ ∂ν ≤ (1 / 2 : ℝ≥0∞) ^ k) ∧
      (∀ k, ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ ∂μs ≤ (1 / 2 : ℝ≥0∞) ^ k) := by
  intro ν gΩ μs D'
  have := (⊤ : Opens H).isOpen.locallyCompactSpace
  have := isFiniteMeasureOnCompacts_comap_top (H := H)
  obtain ⟨Φ₀, hΦ₀m, hΦ₀1, hΦ₀_D, hΦ₀_Dc, hΦ₀_μs⟩ :=
    exists_measurable_calibrationField hv hvar hMDm
  have hνD'_fin : ν D' < ∞ :=
    (Measure.comap_apply_le Subtype.val volume
      (hMDm.preimage measurable_subtype_coe).nullMeasurableSet).trans_lt
      ((measure_mono (image_preimage_subset Subtype.val MD)).trans_lt hMDfin.lt_top)
  have hgΩ_int := integrable_acDerivativeDensity (hv.locallyIntegrableOn _) ν hvar
  have hμs_fin : μs univ < ∞ :=
    (Measure.singularPart_le _ ν univ).trans_lt
      ((variationMeasure_univ (hv.locallyIntegrableOn _) fun _ _ hK => ⟨⊤, hK, hvar⟩) ▸ hvar.lt_top)
  let μ : Measure (⊤ : Opens H) := ν.restrict D' + ν.withDensity (fun z => ‖gΩ z‖ₑ) + μs
  have : IsFiniteMeasure (ν.restrict D') := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have : IsFiniteMeasure (ν.withDensity (fun z => ‖gΩ z‖ₑ)) :=
    ⟨by rw [withDensity_apply _ .univ, Measure.restrict_univ]
        exact hasFiniteIntegral_iff_eNorm.1 hgΩ_int.2⟩
  have : IsFiniteMeasure μs := ⟨hμs_fin⟩
  have hmem : MemLp Φ₀ 1 μ := MemLp.of_bound hΦ₀m.aestronglyMeasurable 1 (.of_forall hΦ₀1)
  choose φ hφ1 hφerr using fun k : ℕ =>
    hmem.exists_testFunction_eLpNorm_sub_le_and_norm_le (n := (⊤ : ℕ∞)) ENNReal.one_ne_top
      zero_le_one (.of_forall hΦ₀1) (ENNReal.pow_pos (by norm_num : (0 : ℝ≥0∞) < 1 / 2) k).ne'
  have herr_μ (k : ℕ) : ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ ∂μ ≤ (1 / 2 : ℝ≥0∞) ^ k := by
    simpa only [Pi.sub_apply] using lintegral_eNorm_le_eLpNorm_one.trans (hφerr k)
  refine ⟨Φ₀, φ, hΦ₀m, hΦ₀1, hφ1, hΦ₀_D, hΦ₀_Dc, hΦ₀_μs, fun k => ?_, fun k => ?_, fun k =>
    (lintegral_mono' (Measure.le_add_left le_rfl) le_rfl).trans (herr_μ k)⟩
  · exact (lintegral_mono' ((Measure.le_add_right le_rfl).trans
      (Measure.le_add_right le_rfl)) le_rfl).trans (herr_μ k)
  · have hg_aem : AEMeasurable (fun z : (⊤ : Opens H) => ‖Φ₀ z - φ k z‖ₑ) ν :=
      (hΦ₀m.sub (by fun_prop)).eNorm.aemeasurable
    have hf_aem : AEMeasurable (fun z : (⊤ : Opens H) => ‖gΩ z‖ₑ) ν :=
      (measurable_acDerivativeDensity ν).eNorm.aemeasurable
    calc ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ * ‖gΩ z‖ₑ ∂ν
        = ∫⁻ z, ((fun z => ‖gΩ z‖ₑ) * (fun z => ‖Φ₀ z - φ k z‖ₑ)) z ∂ν :=
          lintegral_congr fun _ => mul_comm _ _
      _ = ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ ∂ν.withDensity (fun z => ‖gΩ z‖ₑ) :=
          (lintegral_withDensity_eq_lintegral_mul₀ hf_aem hg_aem).symm
      _ ≤ ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ ∂μ :=
          lintegral_mono' ((Measure.le_add_left le_rfl).trans (Measure.le_add_right le_rfl)) le_rfl
      _ ≤ (1 / 2 : ℝ≥0∞) ^ k := herr_μ k

/-- Dominated convergence of `2 * ∫⁻_S √(1 - ‖φ k‖²)` to `∫⁻_S 4 / √(4 + ‖gΩ‖²)` along a fast `L¹`
approximating sequence on `MD`. -/
private theorem tendsto_two_mul_setLIntegral_calibration {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {MD S : Set H} (hMDm : MeasurableSet MD) (hSm : NullMeasurableSet S volume)
    (hSfin : volume S ≠ ∞) (hSMD : ∀ᵐ y : H ∂volume, y ∈ S → y ∈ MD)
    {Φ₀ gΩ : (⊤ : Opens H) → H} (hΦ₀m : Measurable Φ₀)
    (hΦ₀_D : ∀ᵐ z : (⊤ : Opens H) ∂(volume.comap Subtype.val),
      z ∈ Subtype.val ⁻¹' MD → Φ₀ z = -(√(4 + ‖gΩ z‖ ^ 2))⁻¹ • gΩ z)
    (φ : ℕ → 𝓓((⊤ : Opens H), H))
    (herr_D : ∀ k, ∫⁻ z in Subtype.val ⁻¹' MD, ‖Φ₀ z - φ k z‖ₑ
      ∂(volume.comap Subtype.val) ≤ (1 / 2 : ℝ≥0∞) ^ k) :
    Tendsto (fun k => 2 * ∫⁻ y in S, ENNReal.ofReal √(1 - ‖φ k y‖ ^ 2)) atTop
      (𝓝 (∫⁻ y in S, ENNReal.ofReal (4 / √(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2)))) := by
  -- Summable `L¹` errors yield almost-everywhere convergence on `MD`.
  have hae_MD : ∀ᵐ y : H ∂volume, y ∈ MD →
      Tendsto (fun k => φ k y) atTop (𝓝 (Φ₀ ⟨y, trivial⟩)) := by
    have hF (k : ℕ) : Measurable (MD.indicator fun y : H => ‖Φ₀ ⟨y, trivial⟩ - φ k y‖ₑ) :=
      ((hΦ₀m.comp (Continuous.subtype_mk continuous_id fun _ => trivial).measurable).sub
        (φ k).continuous.measurable).eNorm.indicator hMDm
    have hle (k : ℕ) : ∫⁻ y : H, MD.indicator (fun y => ‖Φ₀ ⟨y, trivial⟩ - φ k y‖ₑ) y ≤
        (1 / 2 : ℝ≥0∞) ^ k := by
      rw [lintegral_indicator hMDm]
      let T : Set ((⊤ : Opens H) : Set H) := Subtype.val ⁻¹' MD
      have hsub := setLIntegral_subtype (μ := volume) (s := ((⊤ : Opens H) : Set H))
        (⊤ : Opens H).isOpen.measurableSet T
        (fun y : H => ‖Φ₀ ⟨y, trivial⟩ - φ k y‖ₑ)
      have himg : Subtype.val '' T = MD := by
        ext y; exact ⟨fun ⟨_, hz, hzy⟩ => hzy ▸ hz, fun hy => ⟨⟨y, trivial⟩, hy, rfl⟩⟩
      rw [himg] at hsub
      exact hsub.symm.trans_le (herr_D k)
    have hsum : (∑' k, ∫⁻ y : H, MD.indicator (fun y => ‖Φ₀ ⟨y, trivial⟩ - φ k y‖ₑ) y) ≠ ∞ :=
      ne_top_of_le_ne_top (by simp [ENNReal.tsum_geometric]) (_root_.tsum_le_tsum hle)
    filter_upwards [ae_tendsto_zero_of_tsum_lintegral_ne_top (fun k => (hF k).aemeasurable) hsum]
      with y hy hyMD
    simp only [hyMD, indicator_of_mem] at hy
    exact tendsto_iff_norm_sub_tendsto_zero.2 <| by
      simpa only [Function.comp_def, ENNReal.toReal_zero, ← ofReal_norm, norm_sub_rev,
        ENNReal.toReal_ofReal (norm_nonneg _)] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hy
  -- Dominated convergence on `S` evaluates the limit of `2 * ∫⁻_S √(1 - ‖φ k‖²)`.
  have hae_val : ∀ᵐ y : H ∂volume, y ∈ MD →
      Φ₀ ⟨y, trivial⟩ = -(√(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2))⁻¹ • gΩ ⟨y, trivial⟩ := by
    have h := (ae_restrict_iff_subtype (μ := volume) (s := ((⊤ : Opens H) : Set H))
      (⊤ : Opens H).isOpen.measurableSet
      (p := fun y : H => y ∈ MD →
        Φ₀ ⟨y, trivial⟩ = -(√(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2))⁻¹ • gΩ ⟨y, trivial⟩)).2 hΦ₀_D
    rwa [Opens.coe_top, Measure.restrict_univ] at h
  have hdct : Tendsto (fun k => ∫⁻ y in S, ENNReal.ofReal √(1 - ‖φ k y‖ ^ 2)) atTop
      (𝓝 (∫⁻ y in S, ENNReal.ofReal (2 / √(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2)))) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞))
      (fun k => (ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp
        (continuous_const.sub ((φ k).continuous.norm.pow 2)))).measurable)
      (fun k => .of_forall fun y => ENNReal.ofReal_le_one.2
        (Real.sqrt_le_one.2 (by nlinarith [norm_nonneg (φ k y)])))
      (by simp [hSfin]) ((ae_restrict_iff'₀ hSm).2 ?_)
    filter_upwards [hSMD, hae_MD, hae_val] with y hyS hy_lim hy_val hy_mem
    have hcont : Continuous fun u : H => ENNReal.ofReal √(1 - ‖u‖ ^ 2) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp
        (continuous_const.sub (continuous_norm.pow 2)))
    simpa only [Function.comp_def, hy_val (hyS hy_mem), sqrt_one_sub_norm_calibration_sq] using
      (hcont.tendsto _).comp (hy_lim (hyS hy_mem))
  have hmul_eq : ∫⁻ y in S, ENNReal.ofReal (4 / √(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2)) =
      2 * ∫⁻ y in S, ENNReal.ofReal (2 / √(4 + ‖gΩ ⟨y, trivial⟩‖ ^ 2)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    refine lintegral_congr fun _ => ?_
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]
    ring_nf
  rw [hmul_eq]
  exact ENNReal.Tendsto.const_mul hdct (.inr ENNReal.ofNat_ne_top)

/-- Convergence of the absolutely continuous pairings `-∫ ⟪φ k, gΩ⟫ ∂ν` to `-∫ ⟪Φ₀, gΩ⟫ ∂ν`. -/
private theorem tendsto_neg_integral_inner_ac_calibration {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {v : H → ℝ} (hv : LocallyIntegrable v volume) (hvar : totalVariationOn volume ⊤ v ≠ ∞)
    {Φ₀ : (⊤ : Opens H) → H} (hΦ₀m : Measurable Φ₀) (hΦ₀1 : ∀ z, ‖Φ₀ z‖ ≤ 1)
    (φ : ℕ → 𝓓((⊤ : Opens H), H)) (hφ1 : ∀ k y, ‖φ k y‖ ≤ 1)
    (herr_g : ∀ k, ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ *
      ‖acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) z‖ₑ
      ∂(volume.comap Subtype.val) ≤ (1 / 2 : ℝ≥0∞) ^ k) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    Tendsto (fun k => -∫ z, ⟪φ k z, acDerivativeDensity volume ⊤ v ν z⟫ ∂ν) atTop
      (𝓝 (-∫ z, ⟪Φ₀ z, acDerivativeDensity volume ⊤ v ν z⟫ ∂ν)) := by
  intro ν
  have := (⊤ : Opens H).isOpen.locallyCompactSpace
  have := isFiniteMeasureOnCompacts_comap_top (H := H)
  let gΩ := acDerivativeDensity volume ⊤ v ν
  have hfin : ∀ K, IsCompact K → K ⊆ (⊤ : Opens H) →
      ∃ U : Opens H, K ⊆ (U : Set H) ∧ totalVariationOn volume U v ≠ ∞ :=
    fun _ _ hK => ⟨⊤, hK, hvar⟩
  have hgΩ_int := integrable_acDerivativeDensity (hv.locallyIntegrableOn _) ν hvar
  have hpow0 : Tendsto (fun k => (∫⁻ z, ‖Φ₀ z - φ k z‖ₑ * ‖gΩ z‖ₑ ∂ν).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0∞) < 1))
        (fun _ => zero_le) herr_g)
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hpow0)
  have hi_k := (φ k).integrable_inner_subtype
    (locallyIntegrable_acDerivativeDensity (hv.locallyIntegrableOn _) hfin ν)
  have hi_0 : Integrable (fun z => ⟪Φ₀ z, gΩ z⟫) ν :=
    hgΩ_int.norm.mono' (hΦ₀m.aestronglyMeasurable.inner hgΩ_int.aestronglyMeasurable)
      (.of_forall fun z => (Real.norm_eq_abs _).trans_le ((abs_real_inner_le_norm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (hΦ₀1 z))))
  have hdiff_int : Integrable (fun z => ‖Φ₀ z - φ k z‖ * ‖gΩ z‖) ν :=
    (hgΩ_int.norm.const_mul 2).mono'
      ((hΦ₀m.sub (by fun_prop)).norm.aestronglyMeasurable.mul hgΩ_int.norm.aestronglyMeasurable)
      (.of_forall fun z => (Real.norm_of_nonneg (by positivity)).trans_le
        (mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (by linarith [hΦ₀1 z, hφ1 k z]))
          (norm_nonneg _)))
  rw [dist_neg_neg, dist_eq_norm, norm_sub_rev, ← integral_sub hi_0 hi_k]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono (hi_0.sub hi_k).norm hdiff_int
    fun z => ?_).trans_eq ?_)
  · dsimp only [Pi.sub_apply]
    rw [← inner_sub_left]; exact (Real.norm_eq_abs _).trans_le (abs_real_inner_le_norm _ _)
  · rw [← ENNReal.toReal_ofReal (integral_nonneg fun _ => by positivity),
      ofReal_integral_eq_lintegral_ofReal hdiff_int (.of_forall fun _ => by positivity)]
    congr 1
    refine lintegral_congr fun z => ?_
    dsimp only [gΩ, ν]
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]

/-- Convergence of the transverse divergence pairings `∫ div(φ k) v` to `-∫ ⟪Φ₀, gΩ⟫ ∂ν + |Dˢv|(H)`
along the calibration sequence. -/
private theorem tendsto_integral_divergenceCLM_calibration {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {v : H → ℝ} (hv : LocallyIntegrable v volume) (hvar : totalVariationOn volume ⊤ v ≠ ∞)
    {Φ₀ : (⊤ : Opens H) → H} (hΦ₀m : Measurable Φ₀) (hΦ₀1 : ∀ z, ‖Φ₀ z‖ ≤ 1)
    (hΦ₀_μs : ∀ᵐ z ∂(variationMeasure volume ⊤ v).singularPart (volume.comap Subtype.val),
      -⟪Φ₀ z, polarDensity volume ⊤ v z⟫ = 1)
    (φ : ℕ → 𝓓((⊤ : Opens H), H)) (hφ1 : ∀ k y, ‖φ k y‖ ≤ 1)
    (herr_g : ∀ k, ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ *
      ‖acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) z‖ₑ
      ∂(volume.comap Subtype.val) ≤ (1 / 2 : ℝ≥0∞) ^ k)
    (herr_μs : ∀ k, ∫⁻ z, ‖Φ₀ z - φ k z‖ₑ
      ∂(variationMeasure volume ⊤ v).singularPart (volume.comap Subtype.val) ≤
      (1 / 2 : ℝ≥0∞) ^ k) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    Tendsto (fun k => ∫ y : H, divergenceCLM (φ k) y * v y) atTop
      (𝓝 (-∫ z, ⟪Φ₀ z, acDerivativeDensity volume ⊤ v ν z⟫ ∂ν +
        ((variationMeasure volume ⊤ v).singularPart ν).real univ)) := by
  intro ν
  have := (⊤ : Opens H).isOpen.locallyCompactSpace
  have := isFiniteMeasureOnCompacts_comap_top (H := H)
  let μs := (variationMeasure volume ⊤ v).singularPart ν
  let σ := polarDensity volume ⊤ v
  have hfin : ∀ K, IsCompact K → K ⊆ (⊤ : Opens H) →
      ∃ U : Opens H, K ⊆ (U : Set H) ∧ totalVariationOn volume U v ≠ ∞ :=
    fun _ _ hK => ⟨⊤, hK, hvar⟩
  have hμs_fin : μs univ < ∞ :=
    (Measure.singularPart_le _ ν univ).trans_lt
      ((variationMeasure_univ (hv.locallyIntegrableOn _) hfin) ▸ hvar.lt_top)
  have : IsFiniteMeasure μs := ⟨hμs_fin⟩
  have hpow0 : Tendsto (fun k => (∫⁻ z, ‖Φ₀ z - φ k z‖ₑ ∂μs).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0∞) < 1))
        (fun _ => zero_le) herr_μs)
  have hlim_sing : Tendsto (fun k => -∫ z, ⟪φ k z, σ z⟫ ∂μs) atTop (𝓝 (μs.real univ)) := by
    have hσ1 : ∀ᵐ z ∂μs, ‖σ z‖ = 1 :=
      (Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ ν)).ae_le
        (ae_norm_polarDensity_eq_one (hv.locallyIntegrableOn _) hfin)
    rw [show μs.real univ = ∫ z : (⊤ : Opens H), -⟪Φ₀ z, σ z⟫ ∂μs by
      rw [integral_congr_ae hΦ₀_μs, integral_const, smul_eq_mul, mul_one]]
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hpow0)
    have hi_k : Integrable (fun z : (⊤ : Opens H) => -⟪φ k z, σ z⟫) μs :=
      ((φ k).integrable_inner_subtype ((locallyIntegrable_polarDensity (μ := volume)
        (Ω := (⊤ : Opens H)) (u := v)).mono_measure (Measure.singularPart_le _ ν))).neg
    have hi_0 : Integrable (fun z : (⊤ : Opens H) => -⟪Φ₀ z, σ z⟫) μs :=
      (integrable_const (1 : ℝ)).congr (hΦ₀_μs.mono fun _ hz => hz.symm)
    have hdiff_int : Integrable (fun z : (⊤ : Opens H) => ‖Φ₀ z - φ k z‖) μs :=
      (integrable_const (2 : ℝ)).mono' (hΦ₀m.sub (by fun_prop)).norm.aestronglyMeasurable
        (.of_forall fun z => (Real.norm_of_nonneg (norm_nonneg _)).trans_le
          ((norm_sub_le _ _).trans (by linarith [hΦ₀1 z, hφ1 k z])))
    rw [← integral_neg (fun z : (⊤ : Opens H) => ⟪φ k z, σ z⟫), dist_eq_norm, norm_sub_rev,
      ← integral_sub hi_0 hi_k]
    refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae (hi_0.sub hi_k).norm
      hdiff_int (hσ1.mono fun z hz => ?_)).trans_eq ?_)
    · dsimp only [Pi.sub_apply]
      rw [show -⟪Φ₀ z, σ z⟫ - -⟪φ k z, σ z⟫ = ⟪φ k z - Φ₀ z, σ z⟫ by rw [inner_sub_left]; ring]
      exact (Real.norm_eq_abs _).trans_le ((abs_real_inner_le_norm _ _).trans_eq
        (by rw [hz, mul_one, norm_sub_rev]))
    · simp_rw [← ofReal_norm]
      rw [← ofReal_integral_eq_lintegral_ofReal hdiff_int (.of_forall fun _ => norm_nonneg _),
        ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
  refine ((tendsto_neg_integral_inner_ac_calibration hv hvar hΦ₀m hΦ₀1 φ hφ1 herr_g).add
    hlim_sing).congr fun k => ?_
  have hleb := integral_divergenceCLM_mul_eq_neg_integral_inner_acDerivativeDensity_sub_singularPart
    (hv.locallyIntegrableOn _) hfin ν (φ k)
  linarith

/-- Identify `ENNReal.ofReal (-∫ ⟪Φ₀, gΩ⟫ ∂ν + |Dˢv|.real univ)` as
`∫⁻_D ‖g‖² / √(4 + ‖g‖²) + ∫⁻_{Dᶜ} ‖g‖ₑ + |Dˢv|(H)`. -/
private theorem ofReal_calibration_limit_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {v : H → ℝ} (hv : LocallyIntegrable v volume) (hvar : totalVariationOn volume ⊤ v ≠ ∞)
    {D MD : Set H} (hMDm : MeasurableSet MD) (hMD_ae : D =ᵐ[volume] MD)
    {Φ₀ : (⊤ : Opens H) → H} (hΦ₀m : Measurable Φ₀) (hΦ₀1 : ∀ z, ‖Φ₀ z‖ ≤ 1)
    (hΦ₀_D : ∀ᵐ z : (⊤ : Opens H) ∂(volume.comap Subtype.val), z ∈ Subtype.val ⁻¹' MD →
      Φ₀ z = -(√(4 + ‖acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) z‖ ^ 2))⁻¹ •
        acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) z)
    (hΦ₀_Dc : ∀ᵐ z : (⊤ : Opens H) ∂(volume.comap Subtype.val), z ∉ Subtype.val ⁻¹' MD →
      Φ₀ z = -‖acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) z‖⁻¹ •
        acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) z) :
    let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
    let g : H → H := fun y => acDerivativeDensity volume ⊤ v ν ⟨y, trivial⟩
    ENNReal.ofReal (-∫ z, ⟪Φ₀ z, acDerivativeDensity volume ⊤ v ν z⟫ ∂ν +
        ((variationMeasure volume ⊤ v).singularPart ν).real univ) =
      (∫⁻ y in D, ENNReal.ofReal (‖g y‖ ^ 2 / √(4 + ‖g y‖ ^ 2))) +
        (∫⁻ y in Dᶜ, ‖g y‖ₑ) + (variationMeasure volume ⊤ v).singularPart ν univ := by
  classical
  intro ν g
  have := (⊤ : Opens H).isOpen.locallyCompactSpace
  let gΩ := acDerivativeDensity volume ⊤ v ν
  let μs := (variationMeasure volume ⊤ v).singularPart ν
  have hgΩ_int := integrable_acDerivativeDensity (hv.locallyIntegrableOn _) ν hvar
  have hμs_fin : μs univ < ∞ :=
    (Measure.singularPart_le _ ν univ).trans_lt
      ((variationMeasure_univ (hv.locallyIntegrableOn _) fun _ _ hK => ⟨⊤, hK, hvar⟩) ▸ hvar.lt_top)
  have hi_0 : Integrable (fun z => -⟪Φ₀ z, gΩ z⟫) ν :=
    hgΩ_int.norm.mono' (hΦ₀m.aestronglyMeasurable.inner hgΩ_int.aestronglyMeasurable).neg
      (.of_forall fun z => (Real.norm_eq_abs _).trans_le ((abs_neg _).trans_le
        ((abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hΦ₀1 z)))))
  have hae_pt : (fun z : (⊤ : Opens H) => -⟪Φ₀ z, gΩ z⟫) =ᵐ[ν]
      fun z => if z ∈ Subtype.val ⁻¹' MD then ‖gΩ z‖ ^ 2 / √(4 + ‖gΩ z‖ ^ 2) else ‖gΩ z‖ := by
    filter_upwards [hΦ₀_D, hΦ₀_Dc] with z hzD hzDc
    change z ∈ Subtype.val ⁻¹' MD → Φ₀ z = -(√(4 + ‖gΩ z‖ ^ 2))⁻¹ • gΩ z at hzD
    change z ∉ Subtype.val ⁻¹' MD → Φ₀ z = -‖gΩ z‖⁻¹ • gΩ z at hzDc
    by_cases hz : z ∈ Subtype.val ⁻¹' MD
    · simp only [hz, ↓reduceIte]
      rw [hzD hz, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
      ring
    · simp only [hz, ↓reduceIte]
      rw [hzDc hz, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq]
      by_cases hg0 : ‖gΩ z‖ = 0
      · simp [hg0]
      · rw [neg_mul, neg_neg, sq, inv_mul_cancel_left₀ hg0]
  have hnonneg : 0 ≤ᵐ[ν] fun z => -⟪Φ₀ z, gΩ z⟫ :=
    hae_pt.mono fun z hz => by dsimp only [Pi.zero_apply] at hz ⊢; rw [hz]; split_ifs <;> positivity
  rw [← integral_neg, ENNReal.ofReal_add (integral_nonneg_of_ae hnonneg) measureReal_nonneg,
    measureReal_def, ENNReal.ofReal_toReal hμs_fin.ne,
    ofReal_integral_eq_lintegral_ofReal hi_0 hnonneg,
    lintegral_congr_ae (hae_pt.mono fun z hz => by dsimp only at hz; rw [hz])]
  have hsub := lintegral_subtype_comap (μ := volume) (s := ((⊤ : Opens H) : Set H))
    (⊤ : Opens H).isOpen.measurableSet
    (fun y : H => ENNReal.ofReal (if y ∈ MD then ‖g y‖ ^ 2 / √(4 + ‖g y‖ ^ 2) else ‖g y‖))
  rw [Opens.coe_top, Measure.restrict_univ] at hsub
  rw [show (∫⁻ z : (⊤ : Opens H), ENNReal.ofReal
      (if z ∈ Subtype.val ⁻¹' MD then ‖gΩ z‖ ^ 2 / √(4 + ‖gΩ z‖ ^ 2) else ‖gΩ z‖) ∂ν) =
      ∫⁻ y : H, ENNReal.ofReal (if y ∈ MD then ‖g y‖ ^ 2 / √(4 + ‖g y‖ ^ 2) else ‖g y‖) from hsub,
    ← lintegral_add_compl _ hMDm, setLIntegral_congr hMD_ae, setLIntegral_congr hMD_ae.compl]
  congr 2
  · exact setLIntegral_congr_fun hMDm fun y hy => by simp [hy]
  · exact setLIntegral_congr_fun hMDm.compl fun y hy => by
      have hy' : y ∉ MD := hy; simp [hy', ofReal_norm]

/-- Algebraic recombination `(4 / √(4 + ‖g‖²)) + (‖g‖² / √(4 + ‖g‖²)) = √(4 + ‖g‖²)` under the
Lebesgue integral on `D`. -/
private theorem setLIntegral_four_add_norm_sq_div_sqrt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (v : H → ℝ) (D : Set H) :
    let g : H → H := fun y =>
      acDerivativeDensity volume ⊤ v (volume.comap Subtype.val) ⟨y, trivial⟩
    (∫⁻ y in D, ENNReal.ofReal (4 / √(4 + ‖g y‖ ^ 2))) +
        (∫⁻ y in D, ENNReal.ofReal (‖g y‖ ^ 2 / √(4 + ‖g y‖ ^ 2))) =
      ∫⁻ y in D, ENNReal.ofReal √(4 + ‖g y‖ ^ 2) := by
  intro g
  have hm1 : Measurable fun y : H => ENNReal.ofReal (4 / √(4 + ‖g y‖ ^ 2)) :=
    ENNReal.continuous_ofReal.measurable.comp (measurable_const.div ((Real.continuous_sqrt.comp
      (continuous_const.add (continuous_norm.pow 2))).measurable.comp
      ((measurable_acDerivativeDensity (volume.comap Subtype.val)).comp
        (Continuous.subtype_mk continuous_id fun _ => trivial).measurable)))
  rw [← lintegral_add_left hm1]
  exact lintegral_congr fun _ => by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div, Real.div_sqrt]

/-- **Quantitative excess inequality for Steiner symmetrization.** Let `s` be a null-measurable set
of finite volume in `E`, `e` a unit vector, and `A ⊆ (ℝ ∙ e)ᗮ` a null-measurable family of
noninterval line sections. Then
`P(S_e s) + ∫_{y ∈ A} 4 / √(4 + ‖∇ᵃv(y)‖²) dy ≤ P(s)`,
where `v(y) = |{t | y + t • e ∈ s}|` and `∇ᵃv` is its absolutely continuous derivative density.
No finiteness assumption on `P(s)` is needed. -/
theorem perimeter_steinerSymmetrization_add_setLIntegral_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) {A : Set (ℝ ∙ e)ᗮ} (hA : NullMeasurableSet A volume)
    (hbad : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A →
      ∀ I : Set ℝ, I.OrdConnected → ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    perimeter volume ⊤ (steinerSymmetrization e he s) +
      (∫⁻ y in A, ENNReal.ofReal (4 / √(4 + ‖acDerivativeDensity volume ⊤
        (fun z : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (z : E) + t • e ∈ s})
        (volume.comap Subtype.val) ⟨y, trivial⟩‖ ^ 2))) ≤
      perimeter volume ⊤ s := by
  by_cases hP : perimeter volume ⊤ s = ∞
  · rw [hP]; exact le_top
  let ν : Measure (⊤ : Opens (ℝ ∙ e)ᗮ) := volume.comap Subtype.val
  let v : (ℝ ∙ e)ᗮ → ℝ := fun y => volume.real {t : ℝ | (y : E) + t • e ∈ s}
  let g : (ℝ ∙ e)ᗮ → (ℝ ∙ e)ᗮ := fun y => acDerivativeDensity volume ⊤ v ν ⟨y, trivial⟩
  let D : Set (ℝ ∙ e)ᗮ := {y | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}}
  -- Establish finiteness of `|Dv|`, `volume D`, and `volume A` from `P(s) < ∞`.
  have hv : Integrable v volume := integrable_measureReal_lineSection e he hs hfin
  have hvar : totalVariationOn volume ⊤ v ≠ ∞ :=
    ne_top_of_le_ne_top hP (totalVariationOn_measureReal_lineSection_le hs hfin e he)
  have hD : NullMeasurableSet D volume :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_volume_lineSection e he hs)
  have hDA_fin := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
    hs hfin e he hA hbad
  have hDfin : volume D ≠ ∞ := fun htop => by
    rw [show {y : (ℝ ∙ e)ᗮ | 0 < volume {t : ℝ | (y : E) + t • e ∈ s}} = D from rfl, htop,
      ENNReal.mul_top two_ne_zero, top_add, top_le_iff] at hDA_fin
    exact hP hDA_fin
  have hAfin : volume A ≠ ∞ := fun htop => by
    rw [htop, ENNReal.mul_top two_ne_zero, add_top, top_le_iff] at hDA_fin
    exact hP hDA_fin
  have hAD : ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume, y ∈ A → y ∈ D := by
    filter_upwards [hbad] with y hy hyA
    by_contra hyD
    exact hy hyA ∅ ordConnected_empty (ae_eq_empty.2 (nonpos_iff_eq_zero.1 (not_lt.1 hyD)))
  -- Pass to the limit along the calibration sequence `φ k` and combine with the slab upper bound.
  let MD := toMeasurable volume D
  have hMDm : MeasurableSet MD := measurableSet_toMeasurable volume D
  have hMD_ae : D =ᵐ[volume] MD := (NullMeasurableSet.toMeasurable_ae_eq hD).symm
  have hMDfin : volume MD ≠ ∞ := by rwa [measure_toMeasurable]
  have hsub_MD : ∀ y : (ℝ ∙ e)ᗮ, y ∈ D → y ∈ MD := fun _ hy => subset_toMeasurable volume D hy
  obtain ⟨Φ₀, φ, hΦ₀m, hΦ₀1, hφ1, hΦ₀_D, hΦ₀_Dc, hΦ₀_μs, herr_D, herr_g, herr_μs⟩ :=
    exists_calibration_testFunction_seq hv.locallyIntegrable hvar hMDm hMDfin
  have hlim_D := tendsto_two_mul_setLIntegral_calibration hMDm hD hDfin
    (.of_forall hsub_MD) hΦ₀m hΦ₀_D φ herr_D
  have hlim_A := tendsto_two_mul_setLIntegral_calibration hMDm hA hAfin
    (hAD.mono fun y hy h => hsub_MD y (hy h)) hΦ₀m hΦ₀_D φ herr_D
  have hlim_div := ENNReal.tendsto_ofReal
    (tendsto_integral_divergenceCLM_calibration hv.locallyIntegrable hvar hΦ₀m hΦ₀1 hΦ₀_μs φ hφ1
      herr_g herr_μs)
  rw [ofReal_calibration_limit_eq hv.locallyIntegrable hvar hMDm hMD_ae hΦ₀m hΦ₀1 hΦ₀_D hΦ₀_Dc]
    at hlim_div
  have hineq := le_of_tendsto ((hlim_D.add hlim_A).add hlim_div) (.of_forall fun k =>
    two_mul_setLIntegral_add_two_mul_setLIntegral_add_ofReal_integral_le_perimeter
      hs hfin e he hA hbad (φ k) (hφ1 k))
  refine (add_le_add_left
    (perimeter_steinerSymmetrization_le_lintegral_add_singularPart hs hfin hP e he) _).trans ?_
  calc ((∫⁻ y in D, ENNReal.ofReal √(4 + ‖g y‖ ^ 2)) + (∫⁻ y in Dᶜ, ‖g y‖ₑ) +
          (variationMeasure volume ⊤ v).singularPart ν univ) +
          (∫⁻ y in A, ENNReal.ofReal (4 / √(4 + ‖g y‖ ^ 2)))
      = ((∫⁻ y in D, ENNReal.ofReal (4 / √(4 + ‖g y‖ ^ 2))) +
          (∫⁻ y in A, ENNReal.ofReal (4 / √(4 + ‖g y‖ ^ 2)))) +
          ((∫⁻ y in D, ENNReal.ofReal (‖g y‖ ^ 2 / √(4 + ‖g y‖ ^ 2))) +
            (∫⁻ y in Dᶜ, ‖g y‖ₑ) + (variationMeasure volume ⊤ v).singularPart ν univ) := by
        rw [← setLIntegral_four_add_norm_sq_div_sqrt v D]; abel
    _ ≤ perimeter volume ⊤ s := hineq

/-- **Quantitative excess inequality over all noninterval sections.** For every null-measurable set
`s` of finite volume and every unit direction `e`, the perimeter gap `P(s) - P(S_e s)` controls the
integral of `4 / √(4 + ‖∇ᵃv(y)‖²)` over the full family of transverse points whose line sections do
not agree almost everywhere with an interval. -/
theorem perimeter_steinerSymmetrization_add_lintegral_noninterval_le
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (e : E) (he : ‖e‖ = 1) :
    perimeter volume ⊤ (steinerSymmetrization e he s) +
      (∫⁻ y in {y : (ℝ ∙ e)ᗮ | ∀ I : Set ℝ, I.OrdConnected →
          ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I},
        ENNReal.ofReal (4 / √(4 + ‖acDerivativeDensity volume ⊤
          (fun z : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (z : E) + t • e ∈ s})
          (volume.comap Subtype.val) ⟨y, trivial⟩‖ ^ 2))) ≤
      perimeter volume ⊤ s :=
  perimeter_steinerSymmetrization_add_setLIntegral_le hs hfin e he
    (nullMeasurableSet_noninterval_lineSection hs hfin e he) (.of_forall fun _ => id)

/-- **Steiner perimeter equality forces interval sections.** If a null-measurable set `s` of finite
volume and finite perimeter has the same perimeter as its Steiner symmetral along a unit vector
`e`, then almost every parallel line section of `s` agrees almost everywhere with an interval. -/
theorem ae_lineSection_ordConnected_of_perimeter_steinerSymmetrization_eq
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞)
    (hP : perimeter volume ⊤ s ≠ ∞) (e : E) (he : ‖e‖ = 1)
    (heq : perimeter volume ⊤ (steinerSymmetrization e he s) = perimeter volume ⊤ s) :
    ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I := by
  let A : Set (ℝ ∙ e)ᗮ := {y | ∀ I : Set ℝ, I.OrdConnected →
    ¬{t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I}
  let w : (ℝ ∙ e)ᗮ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (4 / √(4 + ‖acDerivativeDensity volume ⊤
      (fun z : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (z : E) + t • e ∈ s})
      (volume.comap Subtype.val) ⟨y, trivial⟩‖ ^ 2))
  have hle := perimeter_steinerSymmetrization_add_lintegral_noninterval_le hs hfin e he
  rw [heq, ← add_zero (perimeter volume ⊤ s)] at hle
  rw [add_assoc, zero_add] at hle
  have hzero : ∫⁻ y in A, w y = 0 := nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_left hP).1 hle)
  have hwm : Measurable w :=
    ENNReal.continuous_ofReal.measurable.comp (measurable_const.div ((Real.continuous_sqrt.comp
      (continuous_const.add (continuous_norm.pow 2))).measurable.comp
      ((measurable_acDerivativeDensity _).comp
        (Continuous.subtype_mk continuous_id fun _ => trivial).measurable)))
  have hae0 := (ae_restrict_iff'₀ (nullMeasurableSet_noninterval_lineSection hs hfin e he)).1
    ((lintegral_eq_zero_iff hwm).1 hzero)
  filter_upwards [hae0] with y hy
  by_contra hnot
  push Not at hnot
  have hwpos : 0 < w y :=
    ENNReal.ofReal_pos.2 (div_pos (by norm_num) (Real.sqrt_pos.2 (by positivity)))
  exact hwpos.ne' (hy hnot)

end Rigidity

end TauCeti
