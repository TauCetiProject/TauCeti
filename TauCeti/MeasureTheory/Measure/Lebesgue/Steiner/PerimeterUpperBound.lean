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
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import TauCeti.Analysis.BoundedVariation.Slicing.Excess
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Subgraph

/-!
# Smooth-slab upper bound for the perimeter of a Steiner symmetral

Let `E` be a finite-dimensional real inner product space, `e` a unit vector with orthogonal
hyperplane `H = (ℝ ∙ e)ᗮ`, and `s ⊆ E` a null-measurable set of finite volume and finite perimeter.
Write `v(y) = |{t : ℝ | y + t • e ∈ s}|` for the section-length function on `H`,
`D = {y | 0 < v(y)}` for the essential projection, and `∇ᵃv` for the absolutely continuous
derivative density `acDerivativeDensity volume ⊤ v (volume.comap Subtype.val)` of `v` on `H`.

This file proves the De Giorgi–Chlebík–Cianchi–Fusco upper bound on the perimeter of the Steiner
symmetral `S_e s = steinerSymmetrization e he s`
(`TauCeti.perimeter_steinerSymmetrization_le_lintegral_add_singularPart`):

`P(S_e s) ≤ ∫_D √(4 + ‖∇ᵃv‖²) + ∫_{Dᶜ} ‖∇ᵃv‖ + |Dˢv|(H)`.

Mollifying `v` by shrinking normalized smooth bumps gives nonnegative `C¹` widths `v_k = ρ_k ⋆ v`
whose symmetric slabs `{|⟪e, x⟫| < v_k(π_H x) / 2}` converge in measure to `S_e s`. Applying the
`C¹` symmetric-slab divergence formula
(`TauCeti.setIntegral_setOf_abs_inner_lt_div_two_trace_fderiv`) together with the BV Lebesgue
decomposition `Dv = ∇ᵃv dy + σ_v d|Dˢv|` and letting `k → ∞` yields the bound.

## Main declarations

* `TauCeti.integrable_measureReal_lineSection`: for a null-measurable set of finite volume, the
  section-length function `y ↦ |{t | y + t • e ∈ s}|` is integrable on `(ℝ ∙ e)ᗮ`.
* `TauCeti.perimeter_steinerSymmetrization_le_lintegral_add_singularPart`: the smooth-slab upper
  bound `P(S_e s) ≤ ∫_D √(4 + ‖∇ᵃv‖²) + ∫_{Dᶜ} ‖∇ᵃv‖ + |Dˢv|(H)`.

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
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs]; norm_num
  rw [← hnorm a, ← hnorm b]
  refine (abs_norm_sub_norm_le _ _).trans_eq ?_
  have hsub : WithLp.toLp 2 ((2 : ℝ), a) - WithLp.toLp 2 ((2 : ℝ), b) =
      WithLp.toLp 2 ((0 : ℝ), a - b) := by
    apply (WithLp.ext_iff 2).2; ext <;> simp
  rw [hsub, WithLp.norm_toLp_snd]

omit [InnerProductSpace ℝ H] in
/-- Elementary subadditivity `√(4 + ‖a‖²) ≤ 2 + ‖a‖`. -/
private theorem sqrt_four_add_norm_sq_le (a : H) : √(4 + ‖a‖ ^ 2) ≤ 2 + ‖a‖ :=
  Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [norm_nonneg a]⟩

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
    simp only [p, q, RCLike.inner_apply, RCLike.conj_to_real, inner_neg_left, inner_smul_left]; ring
  have hq : ‖q‖ = √(4 + ‖b‖ ^ 2) := by
    rw [WithLp.prod_norm_eq_of_L2]
    simp only [q, WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs]; norm_num
  have hp : ‖p‖ ≤ 1 := by
    have hsq (z : E) : ⟪e, z⟫ ^ 2 + ‖(π z : E)‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [(ℝ ∙ e).norm_sq_eq_add_norm_sq_starProjection z,
        Submodule.starProjection_unit_singleton ℝ he z, norm_smul, Real.norm_eq_abs, he, mul_one,
        sq_abs]; rfl
    rw [WithLp.prod_norm_eq_of_L2, Real.sqrt_le_one]
    simp only [p, WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs, norm_neg, norm_smul]
    norm_num
    have h₁ := hsq z₁
    have h₂ := hsq z₂
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
  have hπ1 : ‖(2 : ℝ)⁻¹ • π (z₁ + z₂)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hle := ((ℝ ∙ e)ᗮ.norm_orthogonalProjectionOnto_apply_le (z₁ + z₂)).trans
      (norm_add_le z₁ z₂)
    linarith
  have h1 : ⟪e, z₁ - z₂⟫ ≤ M * w :=
    (real_inner_le_norm e (z₁ - z₂)).trans (by simpa [he] using hdiff)
  have h2 : -(2 : ℝ)⁻¹ * ⟪π (z₁ + z₂), b + s⟫ ≤ ‖b‖ + ‖s‖ := by
    have hcs : -⟪(2 : ℝ)⁻¹ • π (z₁ + z₂), b + s⟫ ≤ ‖(2 : ℝ)⁻¹ • π (z₁ + z₂)‖ * ‖b + s‖ :=
      (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
    rw [inner_smul_left, RCLike.conj_to_real] at hcs
    calc -(2 : ℝ)⁻¹ * ⟪π (z₁ + z₂), b + s⟫
        = -((2 : ℝ)⁻¹ * ⟪π (z₁ + z₂), b + s⟫) := by ring
      _ ≤ ‖(2 : ℝ)⁻¹ • π (z₁ + z₂)‖ * ‖b + s‖ := hcs
      _ ≤ 1 * (‖b‖ + ‖s‖) := mul_le_mul hπ1 (norm_add_le b s) (norm_nonneg _) zero_le_one
      _ = ‖b‖ + ‖s‖ := one_mul _
  linarith

end Elementary

section MollifiedBV

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

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
  let ν : Measure (⊤ : Opens H) := volume.comap Subtype.val
  have : IsFiniteMeasureOnCompacts ν := ⟨fun _ hK =>
    (Measure.comap_apply_le Subtype.val volume hK.nullMeasurableSet).trans_lt
      (hK.image continuous_subtype_val).measure_lt_top⟩
  let g : H → H := fun z => acDerivativeDensity volume ⊤ u ν ⟨z, trivial⟩
  let μs := (variationMeasure volume ⊤ u).singularPart ν
  let σ := polarDensity volume ⊤ u
  have hg : Integrable g volume := integrable_acDerivativeDensity_on_univ hu hvar
  -- Test the BV Lebesgue decomposition against `Ψ = ρ(y - ·) • w`.
  let φ : 𝓓((⊤ : Opens H), ℝ) :=
    ⟨fun z => ρ (y - z), by fun_prop, hρc.comp_homeomorph (Homeomorph.subLeft y), subset_univ _⟩
  have hφ_apply (z : H) : φ z = ρ (y - z) := rfl
  let Ψ : 𝓓((⊤ : Opens H), H) := postcompCLM (toSpanSingleton ℝ w) φ
  have hdiv (z : H) : divergenceCLM Ψ z = -fderiv ℝ ρ (y - z) w := by
    have hcoe : (Ψ : H → H) = fun s => ρ (y - s) • w := by ext s; rfl
    have hdρ : HasFDerivAt (fun s : H => ρ (y - s))
        ((fderiv ℝ ρ (y - z)).comp (0 - ContinuousLinearMap.id ℝ H)) z :=
      (hρ.differentiable (by simp) (y - z)).hasFDerivAt.comp z
        ((hasFDerivAt_const y z).sub (hasFDerivAt_id z))
    rw [divergenceCLM_apply, hcoe, trace_fderiv_smul_const hdρ.differentiableAt, hdρ.fderiv]; simp
  have hleb := integral_divergenceCLM_mul_eq_neg_integral_inner_acDerivativeDensity_sub_singularPart
    (hu.locallyIntegrableOn _) (fun _ _ hK => ⟨⊤, hK, hvar⟩) ν Ψ
  simp only [hdiv, neg_mul, integral_neg] at hleb
  have hd : fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, volume] u) y w = ∫ z : H, fderiv ℝ ρ (y - z) w * u z := by
    rw [← convolution_flip, hρc.fderiv_convolution_right_apply _ hu (hρ.of_le (by simp)) y w]
    simp [convolution_def, mul_comm]
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
    rw [show (fun z : (⊤ : Opens H) => ⟪Ψ z, acDerivativeDensity volume ⊤ u ν z⟫) =
        fun z : (⊤ : Opens H) => ⟪w, ρ (y - z) • g z⟫ by
          ext z; simp [Ψ, hφ_apply, g, inner_smul_left, inner_smul_right],
      show (∫ z : (⊤ : Opens H), ⟪w, ρ (y - z) • g z⟫ ∂ν) = ∫ z : H, ⟪w, ρ (y - z) • g z⟫
        from hsub]
    refine ((innerSL ℝ w).integral_comp_comm hac_int).trans ?_
    rw [← convolution_flip]; simp [convolution_def]
  have hsing_eq : ∫ z : (⊤ : Opens H), ⟪Ψ z, σ z⟫ ∂μs =
      ⟪w, ∫ z : (⊤ : Opens H), ρ (y - z) • σ z ∂μs⟫ := by
    rw [show (fun z : (⊤ : Opens H) => ⟪Ψ z, σ z⟫) =
        fun z : (⊤ : Opens H) => ⟪w, ρ (y - z) • σ z⟫ by
          ext z; simp [Ψ, hφ_apply, inner_smul_left, inner_smul_right]]
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
  have hμs_fin : μs univ < ∞ := (Measure.singularPart_le _ ν univ).trans_lt
    ((variationMeasure_univ (hu.locallyIntegrableOn _) fun _ _ hK => ⟨⊤, hK, hvar⟩) ▸ hvar.lt_top)
  have : IsFiniteMeasure μs := ⟨hμs_fin⟩
  have hσ1 : ∀ᵐ z ∂μs, ‖polarDensity volume ⊤ u z‖ = 1 :=
    (Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ ν)).ae_le
      (ae_norm_polarDensity_eq_one (hu.locallyIntegrableOn _) fun _ _ hK => ⟨⊤, hK, hvar⟩)
  have hsub_cont : Continuous fun p : H × (⊤ : Opens H) => ρ (p.1 - p.2) :=
    hρ.continuous.comp (continuous_fst.sub (continuous_subtype_val.comp continuous_snd))
  have hsρ_meas : AEStronglyMeasurable sρ volume :=
    (hsub_cont.measurable.aestronglyMeasurable.smul
      (measurable_polarDensity.comp measurable_snd).aestronglyMeasurable).integral_prod_right'
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

/-- `y ↦ √(4 + ‖f y‖²)` is integrable on any finite-measure set whenever `f` is integrable. -/
private theorem integrableOn_sqrt_four_add_norm_sq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {f : H → H} (hf : Integrable f volume) {S : Set H} (hSfin : volume S ≠ ∞) :
    IntegrableOn (fun y => √(4 + ‖f y‖ ^ 2)) S volume :=
  ((integrableOn_const (C := (2 : ℝ)) hSfin).add hf.norm.integrableOn).mono'
    ((Real.continuous_sqrt.comp (continuous_const.add
      (continuous_norm.pow 2))).comp_aestronglyMeasurable hf.aestronglyMeasurable.restrict)
    (.of_forall fun _ =>
      (Real.norm_of_nonneg (Real.sqrt_nonneg _)).trans_le (sqrt_four_add_norm_sq_le _))

/-- Symmetric difference of two centered open intervals in `ℝ` has measure `‖a - b‖ₑ`. -/
private theorem volume_ball_symmDiff_ball {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    volume (ball (0 : ℝ) (a / 2) ∆ ball (0 : ℝ) (b / 2)) = ‖a - b‖ₑ := by
  have hsub {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
      volume (ball (0 : ℝ) (y / 2) \ ball (0 : ℝ) (x / 2)) = ENNReal.ofReal (y - x) := by
    rw [measure_sdiff (ball_subset_ball (by linarith)) measurableSet_ball.nullMeasurableSet
      (by rw [Real.volume_ball]; exact ENNReal.ofReal_ne_top), Real.volume_ball, Real.volume_ball]
    ring_nf; rw [← ENNReal.ofReal_sub _ hx]
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
  have hsec_S : {t : ℝ | (y : E) + t • e ∈ S} = ball (0 : ℝ) (w y / 2) := by
    ext t
    have hπ : π ((y : E) + t • e) = y := by
      simp [π, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
    change |⟪e, (y : E) + t • e⟫| < w (π ((y : E) + t • e)) / 2 ↔ t ∈ ball (0 : ℝ) (w y / 2)
    rw [inner_add_smul e he, hπ, mem_ball_zero_iff, Real.norm_eq_abs]
  have hsec_st : {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s} =
      ball (0 : ℝ) (volume.real {t : ℝ | (y : E) + t • e ∈ s} / 2) := by
    rw [lineSection_steinerSymmetrization]; ext t
    have hrad : volume {t : ℝ | (y : E) + t • e ∈ s} / 2 =
        ENNReal.ofReal (volume.real {t : ℝ | (y : E) + t • e ∈ s} / 2) := by
      rw [ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_ofNat, measureReal_def,
        ENNReal.ofReal_toReal hyfin.ne]
    rw [mem_eball, mem_ball, edist_zero_right, dist_zero_right, Real.eNorm_eq_ofReal_abs,
      Real.norm_eq_abs, hrad, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)]
  change volume ({t : ℝ | (y : E) + t • e ∈ S} ∆
    {t : ℝ | (y : E) + t • e ∈ steinerSymmetrization e he s}) = _
  rw [hsec_S, hsec_st, volume_ball_symmDiff_ball (hw0 y) measureReal_nonneg]

/-- For a finite-volume null-measurable set `s`, the section-length function `y ↦ |s_y|` is
integrable on `(ℝ ∙ e)ᗮ`. -/
theorem integrable_measureReal_lineSection (e : E) (he : ‖e‖ = 1)
    {s : Set E} (hs : NullMeasurableSet s volume) (hfin : volume s ≠ ∞) :
    Integrable (fun y : (ℝ ∙ e)ᗮ => volume.real {t : ℝ | (y : E) + t • e ∈ s}) volume := by
  refine ⟨(aemeasurable_volume_lineSection e he hs).ennreal_toReal.aestronglyMeasurable,
    hasFiniteIntegral_iff_eNorm.2 ?_⟩
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
  rw [fderiv_convolution_eq_inner_add_singular hv.locallyIntegrable hvar hρ hρc y (π (z₁ + z₂))]
  by_cases hy : y ∈ MD
  · simp only [indicator_of_mem hy, indicator_of_notMem (show y ∉ MDᶜ from not_not.2 hy), add_zero]
    rw [inner_add_right, mul_add, sub_add_eq_sub_sub]
    have hmain := slab_boundary_le_sqrt he hz₁ hz₂ ((ρ ⋆[lsmul ℝ ℝ, volume] g) y)
    have hπ2 : ‖π (z₁ + z₂)‖ ≤ 2 :=
      ((ℝ ∙ e)ᗮ.norm_orthogonalProjectionOnto_apply_le _).trans
        ((norm_add_le z₁ z₂).trans (by linarith))
    have hcs := (neg_le_abs _).trans (abs_real_inner_le_norm (π (z₁ + z₂)) (sρ y))
    nlinarith [norm_nonneg (sρ y)]
  · simp only [indicator_of_notMem hy, indicator_of_mem (show y ∈ MDᶜ from hy), zero_add]
    have hseg := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hψ.differentiable one_ne_zero x) (fun x _ => hM x)
      (mem_univ ((y : E) - (w y / 2) • e)) (mem_univ ((y : E) + (w y / 2) • e))
    rw [show ((y : E) + (w y / 2) • e) - ((y : E) - (w y / 2) • e) = w y • e by module,
      norm_smul, Real.norm_of_nonneg (hw0 y), he, mul_one] at hseg
    have := slab_boundary_le_off he hz₁ hz₂ hseg ((ρ ⋆[lsmul ℝ ℝ, volume] g) y) (sρ y)
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
  have hw0 (y : (ℝ ∙ e)ᗮ) : 0 ≤ w y :=
    integral_nonneg fun z => mul_nonneg (hρ0 z) (hv0 _)
  have hρ_int : Integrable ρ volume := hρ.continuous.integrable_of_hasCompactSupport hρc
  have hgk : Integrable (ρ ⋆[lsmul ℝ ℝ, volume] g) volume :=
    hρ_int.integrable_convolution (lsmul ℝ ℝ)
      (integrable_acDerivativeDensity_on_univ hv.locallyIntegrable hvar)
  have hwk : Integrable w volume := hρ_int.integrable_convolution (lsmul ℝ ℝ) hv
  have hsρ : Integrable sρ volume := (integrable_and_ofReal_integral_norm_singular_convolution_le
    hv.locallyIntegrable hvar hρ hρc hρ0 hρ1).1
  have hint_MD : Integrable (MD.indicator fun y => √(4 + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖ ^ 2))
      volume := (integrable_indicator_iff hMDm).2 (integrableOn_sqrt_four_add_norm_sq hgk hMDfin)
  have hint_MDc : Integrable (MDᶜ.indicator fun y =>
      M * w y + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖) volume :=
    (integrable_indicator_iff hMDm.compl).2 ((hwk.const_mul M).add hgk.norm).integrableOn
  have hint_12 : Integrable (fun y =>
      MD.indicator (fun y => √(4 + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖ ^ 2)) y +
        MDᶜ.indicator (fun y => M * w y + ‖(ρ ⋆[lsmul ℝ ℝ, volume] g) y‖) y) volume :=
    hint_MD.add hint_MDc
  rw [setIntegral_setOf_abs_inner_lt_div_two_trace_fderiv e he hw hw0 hψ hψc]
  refine (integral_mono (integrable_slab_boundary_integrand e hw hψ hψc) (hint_12.add hsρ.norm)
    (slab_mollified_pointwise_le e he hv hvar MD hρ hρc hw0 hψ hψ1 hM)).trans_eq ?_
  simp only [Pi.add_apply]
  rw [integral_add hint_12 hsρ.norm, integral_add hint_MD hint_MDc,
    integral_indicator hMDm, integral_indicator hMDm.compl,
    integral_add (hwk.const_mul M).integrableOn hgk.norm.integrableOn, integral_const_mul]
  dsimp only [g, w, sρ, ν]; ring

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
  have hwk0 (y : (ℝ ∙ e)ᗮ) : 0 ≤ wk y :=
    integral_nonneg fun z => mul_nonneg ((β k).nonneg_normed z) measureReal_nonneg
  have hSkm : MeasurableSet Sk :=
    measurableSet_lt (continuous_const.inner continuous_id).abs.measurable
      ((hwk_cont.div_const 2).comp π.continuous).measurable
  have hSk_eq : ∫ x in Sk, LinearMap.trace ℝ E (fderiv ℝ (ψ : E → E) x : E →ₗ[ℝ] E) =
      ∫ x, divergenceCLM ψ x * Sk.indicator 1 x := by
    simp_rw [← divergenceCLM_apply]; rw [← integral_indicator hSkm]
    exact integral_congr_ae (.of_forall fun x => by by_cases hx : x ∈ Sk <;> simp [hx])
  have hint_mul {T : Set E} (hTm : NullMeasurableSet T volume) :
      Integrable (fun x => divergenceCLM ψ x * T.indicator 1 x) volume :=
    (((divergenceCLM ψ).continuous.integrable_of_hasCompactSupport
      (divergenceCLM ψ).hasCompactSupport).indicator₀ hTm).congr
      (.of_forall fun x => by by_cases hx : x ∈ T <;> simp [hx])
  have hsymm_m := hSkm.nullMeasurableSet.symmDiff (nullMeasurableSet_steinerSymmetrization e he hs)
  have hsymm_fin : volume (Sk ∆ steinerSymmetrization e he s) ≠ ∞ := by
    rw [volume_slab_symmDiff_steinerSymmetrization e he hs hfin hwk_cont.measurable hwk0]
    exact (hasFiniteIntegral_iff_eNorm.1
      (((β k).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hv).sub hv).2).ne
  rw [hSk_eq, dist_eq_norm, ← integral_sub (hint_mul hSkm.nullMeasurableSet)
    (hint_mul (nullMeasurableSet_steinerSymmetrization e he hs))]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono
    ((hint_mul hSkm.nullMeasurableSet).sub
      (hint_mul (nullMeasurableSet_steinerSymmetrization e he hs))).norm
    ((integrable_indicator_iff₀ hsymm_m).2 (integrableOn_const hsymm_fin)) fun x => ?_).trans_eq ?_)
  · dsimp only [Pi.sub_apply]
    by_cases hx1 : x ∈ Sk <;> by_cases hx2 : x ∈ steinerSymmetrization e he s <;>
      simp [symmDiff_def, hx1, hx2, -divergenceCLM_apply, -Real.norm_eq_abs, hC x]
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
  have hlip {S : Set H} {F : H → ℝ} (hF : ∀ a b, |F a - F b| ≤ ‖a - b‖)
      (hFint : ∀ {f : H → H}, Integrable f volume → IntegrableOn (fun y => F (f y)) S volume) :
      Tendsto (fun k => ∫ y in S, F (gk k y)) atTop (𝓝 (∫ y in S, F (g y))) := by
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_)
      hconv_g)
    have hgk : Integrable (gk k) volume :=
      (β k).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hg
    rw [dist_eq_norm, ← integral_sub (hFint hgk) (hFint hg),
      ← integral_norm_sub_eq_toReal_lintegral hgk hg]
    exact (norm_integral_le_integral_norm _).trans ((integral_mono
      ((hFint hgk).sub (hFint hg)).norm (hgk.sub hg).norm.integrableOn
      fun _ => (Real.norm_eq_abs _).trans_le (hF _ _)).trans
      (setIntegral_le_integral (hgk.sub hg).norm (.of_forall fun _ => norm_nonneg _)))
  have hrhs1 := hlip abs_sqrt_four_add_norm_sq_sub_le
    fun hf => integrableOn_sqrt_four_add_norm_sq hf hMDfin
  have hrhs2 := hlip (S := MDᶜ) abs_norm_sub_norm_le fun hf => hf.norm.integrableOn
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
    simp only [Pi.sub_apply, hv_zero y hy, sub_zero, Real.norm_eq_abs, le_abs_self]
  simpa only [add_zero] using (hrhs1.add hrhs2).add hrhs3

/-- Convert `(∫⁻_D √(4 + ‖g‖²)) + (∫⁻_{Dᶜ} ‖g‖ₑ)` to `ENNReal.ofReal` of the corresponding Bochner
sum on the measurable hull `MD` of `D`. -/
private theorem setLIntegral_sqrt_add_enorm_eq_ofReal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {g : H → H} (hg : Integrable g volume) {D MD : Set H}
    (hMDfin : volume MD ≠ ∞) (hMD_ae : D =ᵐ[volume] MD) :
    (∫⁻ y in D, ENNReal.ofReal √(4 + ‖g y‖ ^ 2)) + (∫⁻ y in Dᶜ, ‖g y‖ₑ) =
      ENNReal.ofReal ((∫ y in MD, √(4 + ‖g y‖ ^ 2)) + ∫ y in MDᶜ, ‖g y‖) := by
  rw [setLIntegral_congr hMD_ae, setLIntegral_congr hMD_ae.compl,
    ENNReal.ofReal_add (integral_nonneg fun _ => Real.sqrt_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _),
    ofReal_integral_eq_lintegral_ofReal (integrableOn_sqrt_four_add_norm_sq hg hMDfin)
      (.of_forall fun _ => Real.sqrt_nonneg _),
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
  have hDfin : volume D ≠ ∞ := fun htop => by
    have h2 := two_mul_volume_add_two_mul_volume_le_perimeter_of_noninterval_lineSection
      hs hfin e he (A := (∅ : Set (ℝ ∙ e)ᗮ)) MeasurableSet.empty.nullMeasurableSet
      (.of_forall fun _ h => False.elim h)
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

end TauCeti
