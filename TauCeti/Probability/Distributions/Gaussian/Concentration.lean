/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Probability.Distributions.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Analysis.Calculus.IntervalIntegral.Rotation
import TauCeti.Probability.Distributions.Gaussian.Transforms
import TauCeti.Probability.Moments.Basic
import TauCeti.Probability.Distributions.Uniform.Basic

/-!
# Gaussian concentration of smooth functions

Let `μ` be a centred Gaussian measure on a separable Banach space `E`, and let `f : E → ℝ` be a
`C¹` function whose derivative has variance at most `v` under `μ` at almost every point, that is
`Var[fderiv ℝ f x; μ] ≤ v`. Then `f` concentrates around its mean with Gaussian tails: `f - 𝔼 f`
is sub-Gaussian with variance proxy `π² v / 4`, and

`μ {x | ε ≤ |f x - 𝔼 f|} ≤ 2 exp (-2 ε² / (π² v))`.

For the standard Gaussian measure on a finite-dimensional inner product space the variance of a
linear functional is its squared norm, so the hypothesis holds with `v = K²` when `‖f' x‖ ≤ K`,
that is, when the `C¹` function `f` is `K`-Lipschitz. Estimates of this kind, transported to the
Euclidean sphere, are the concentration of measure behind Dvoretzky's theorem on almost Euclidean
sections of normed spaces.

The proof is the interpolation argument of Maurey and Pisier. For `(x, y) ∈ E × E` and the
rotation `R θ (x, y) = (cos θ • x + sin θ • y, -sin θ • x + cos θ • y)`, the first coordinate of
`R θ (x, y)` runs along a quarter circle from `x` to `y` with velocity the second coordinate, so
(`ContDiff.sub_eq_integral_fderiv_rotation`)

`f y - f x = ∫ θ in 0..π/2, f' (R θ (x, y)).1 (R θ (x, y)).2`.

Averaging over `θ` and applying Jensen's inequality to the exponential bounds
`exp (t (f y - f x))` by an average of `exp (t π / 2 · f' (R θ (x, y)).1 (R θ (x, y)).2)`.
The product `μ ⊗ μ` is invariant under each rotation `R θ`
(`ProbabilityTheory.IsGaussian.map_rotation_eq_self`), so after integration every `θ`
contributes the same amount, which is an exponential moment of the Gaussian variable
`f' x y` in `y`. Jensen's inequality in `y` then gives the exponential-moment estimate
`𝔼 exp (t (f - 𝔼 f)) ≤ exp (π² t² v / 8)`, and Chernoff's bound
(`ProbabilityTheory.HasSubgaussianMGF.measure_ge_le`) gives the tails.

## Main results

* `ProbabilityTheory.IsGaussian.lintegral_exp_mul_sub_le`: the Maurey–Pisier inequality
  `∫∫ exp (t (f y - f x)) dμ(x) dμ(y) ≤ ∫ exp (π² t² / 8 · Var[f' x; μ]) dμ(x)`.
* `ProbabilityTheory.IsGaussian.hasSubgaussianMGF_sub_integral_of_variance_fderiv_le`:
  `f - 𝔼 f` is sub-Gaussian with variance proxy `π² v / 4`.
* `ProbabilityTheory.IsGaussian.measureReal_setOf_le_abs_sub_integral_le_of_variance_fderiv_le`:
  the two-sided tail bound.
* `TauCeti.Probability.measureReal_stdGaussian_setOf_le_abs_sub_integral_le`: the tail bound
  `2 exp (-2 ε² / (π² K²))` for the standard Gaussian measure and `‖f'‖ ≤ K`.

## References

* G. Pisier, *Probabilistic methods in the geometry of Banach spaces*, in Probability and
  Analysis (Varenna, 1985), Lecture Notes in Math. **1206**, Springer, 1986, Theorem 2.2.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §13.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace TauCeti.Probability

section Jensen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

private instance : IsProbabilityMeasure (uniformMeasure 0 (π / 2)) :=
  isProbabilityMeasure_uniformMeasure (by positivity)

/-- Jensen's inequality along the interpolation path: `exp (t (f y - f x))` is at most the
average over `θ ∈ (0, π / 2]` of `exp (t π / 2 · f' (R θ (x, y)).1 (R θ (x, y)).2)`. -/
private lemma exp_mul_sub_le_integral (hf : ContDiff ℝ 1 f) (t : ℝ) (p : E × E) :
    exp (t * (f p.2 - f p.1)) ≤ ∫ θ, exp (t * (π / 2) *
      fderiv ℝ f (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2)
        ∂uniformMeasure 0 (π / 2) := by
  set g : ℝ → ℝ := fun θ ↦
    fderiv ℝ f (ContinuousLinearMap.rotation θ p).1 (ContinuousLinearMap.rotation θ p).2
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hg : Continuous g := by
    simp only [g, ContinuousLinearMap.rotation_apply]
    fun_prop
  have hmean : ∫ θ, t * (π / 2) * g θ ∂uniformMeasure 0 (π / 2) = t * (f p.2 - f p.1) := by
    simp only [g]
    rw [integral_const_mul, integral_uniformMeasure (by positivity),
      hf.sub_eq_integral_fderiv_rotation p, sub_zero, smul_eq_mul]
    field_simp
  rw [← hmean]
  exact convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ (by simp)
    ((integrable_uniformMeasure hg.integrableOn_Ioc).const_mul _)
    (integrable_uniformMeasure (continuous_exp.comp (continuous_const.mul hg)).integrableOn_Ioc)

end Jensen

end TauCeti.Probability

namespace ProbabilityTheory.IsGaussian

section Gaussian

open TauCeti.Probability (uniformMeasure)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsGaussian μ]
  {f : E → ℝ} {v : ℝ≥0}

/-- **The Maurey–Pisier inequality.** For a centred Gaussian measure `μ` and a `C¹` function `f`,
`∫∫ exp (t (f y - f x)) dμ(x) dμ(y) ≤ ∫ exp (π² t² / 8 · Var[f' x; μ]) dμ(x)`. -/
theorem lintegral_exp_mul_sub_le (hμ : μ[id] = 0) (hf : ContDiff ℝ 1 f) (t : ℝ) :
    ∫⁻ p, .ofReal (exp (t * (f p.2 - f p.1))) ∂μ.prod μ ≤
      ∫⁻ x, .ofReal (exp (π ^ 2 * t ^ 2 / 8 * Var[fderiv ℝ f x; μ])) ∂μ := by
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  set G : E × E → ℝ≥0∞ := fun p ↦ .ofReal (exp (t * (π / 2) * fderiv ℝ f p.1 p.2))
  have hG : Measurable G := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    fun_prop
  -- Jensen's inequality in `θ`, then Tonelli's theorem.
  have hjensen : ∫⁻ p, .ofReal (exp (t * (f p.2 - f p.1))) ∂μ.prod μ ≤
      ∫⁻ θ, ∫⁻ p, G (ContinuousLinearMap.rotation θ p) ∂μ.prod μ ∂uniformMeasure 0 (π / 2) := by
    have hmeas : Measurable fun q : (E × E) × ℝ ↦ G (ContinuousLinearMap.rotation q.2 q.1) := by
      refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
      simp only [ContinuousLinearMap.rotation_apply]
      fun_prop
    rw [← lintegral_lintegral_swap hmeas.aemeasurable]
    refine lintegral_mono fun p ↦ ?_
    have hint : Integrable (fun θ ↦ exp (t * (π / 2) *
        fderiv ℝ f (ContinuousLinearMap.rotation θ p).1
          (ContinuousLinearMap.rotation θ p).2)) (uniformMeasure 0 (π / 2)) := by
      refine TauCeti.Probability.integrable_uniformMeasure (Continuous.integrableOn_Ioc ?_)
      simp only [ContinuousLinearMap.rotation_apply]
      fun_prop
    calc ENNReal.ofReal (exp (t * (f p.2 - f p.1)))
        ≤ .ofReal (∫ θ, exp (t * (π / 2) * fderiv ℝ f (ContinuousLinearMap.rotation θ p).1
            (ContinuousLinearMap.rotation θ p).2) ∂uniformMeasure 0 (π / 2)) :=
          ENNReal.ofReal_le_ofReal (TauCeti.Probability.exp_mul_sub_le_integral hf t p)
      _ = ∫⁻ θ, G (ContinuousLinearMap.rotation θ p) ∂uniformMeasure 0 (π / 2) :=
          ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ (exp_pos _).le)
  -- Each rotation preserves `μ ⊗ μ`.
  have hrot (θ : ℝ) :
      ∫⁻ p, G (ContinuousLinearMap.rotation θ p) ∂μ.prod μ = ∫⁻ p, G p ∂μ.prod μ := by
    rw [← lintegral_map hG (ContinuousLinearMap.rotation θ).measurable,
      IsGaussian.map_rotation_eq_self hμ θ]
  -- The remaining integral is an exponential moment of the Gaussian variable `f' x`.
  have hmgf (x : E) : ∫⁻ y, .ofReal (exp (t * (π / 2) * fderiv ℝ f x y)) ∂μ =
      .ofReal (exp (π ^ 2 * t ^ 2 / 8 * Var[fderiv ℝ f x; μ])) := by
    have hμ' : ∫ y, y ∂μ = 0 := by simpa using hμ
    rw [lintegral_ofReal_exp_mul_dual, integral_dual, hμ', map_zero, mul_zero, zero_add]
    congr 2
    ring
  calc ∫⁻ p, .ofReal (exp (t * (f p.2 - f p.1))) ∂μ.prod μ
      ≤ ∫⁻ θ, ∫⁻ p, G (ContinuousLinearMap.rotation θ p) ∂μ.prod μ ∂uniformMeasure 0 (π / 2) :=
        hjensen
    _ = ∫⁻ p, G p ∂μ.prod μ := by simp_rw [hrot, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ x, .ofReal (exp (π ^ 2 * t ^ 2 / 8 * Var[fderiv ℝ f x; μ])) ∂μ := by
      rw [lintegral_prod _ hG.aemeasurable]
      simp_rw [G, hmgf]

/-- The Maurey–Pisier inequality when the variances of the derivative are at most `v` almost
everywhere. -/
theorem lintegral_exp_mul_sub_le_of_variance_fderiv_le (hμ : μ[id] = 0) (hf : ContDiff ℝ 1 f)
    (hv : ∀ᵐ x ∂μ, Var[fderiv ℝ f x; μ] ≤ v) (t : ℝ) :
    ∫⁻ p, .ofReal (exp (t * (f p.2 - f p.1))) ∂μ.prod μ ≤ .ofReal (exp (π ^ 2 * t ^ 2 / 8 * v)) :=
  calc _ ≤ _ := lintegral_exp_mul_sub_le hμ hf t
    _ ≤ ∫⁻ _, .ofReal (exp (π ^ 2 * t ^ 2 / 8 * v)) ∂μ :=
      lintegral_mono_ae <| hv.mono fun x hx ↦ by gcongr
    _ = _ := by simp

/-- A `C¹` function whose derivative has variance at most `v` almost everywhere under a centred
Gaussian measure has finite exponential moments of every order. -/
theorem integrable_exp_mul_of_variance_fderiv_le (hμ : μ[id] = 0) (hf : ContDiff ℝ 1 f)
    (hv : ∀ᵐ x ∂μ, Var[fderiv ℝ f x; μ] ≤ v) (t : ℝ) :
    Integrable (fun x ↦ exp (t * f x)) μ := by
  have hfc : Continuous f := hf.continuous
  set F : E × E → ℝ≥0∞ := fun p ↦ .ofReal (exp (t * (f p.2 - f p.1)))
  have hF : Measurable F := ENNReal.measurable_ofReal.comp (by fun_prop)
  have hfin : ∫⁻ x, ∫⁻ y, F (x, y) ∂μ ∂μ ≠ ∞ := by
    rw [← lintegral_prod _ hF.aemeasurable]
    exact ((lintegral_exp_mul_sub_le_of_variance_fderiv_le hμ hf hv t).trans_lt
      ENNReal.ofReal_lt_top).ne
  obtain ⟨x₀, hx₀⟩ := (ae_lt_top' hF.lintegral_prod_right'.aemeasurable hfin).exists
  have hexp (y : E) : ENNReal.ofReal (exp (t * f y)) = .ofReal (exp (t * f x₀)) * F (x₀, y) := by
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
    congr 2
    ring
  have hlt : ∫⁻ y, .ofReal (exp (t * f y)) ∂μ ≠ ∞ := by
    rw [lintegral_congr hexp, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx₀.ne
  exact (integrable_toReal_of_lintegral_ne_top (by fun_prop) hlt).congr
    (.of_forall fun y ↦ ENNReal.toReal_ofReal (exp_pos _).le)

/-- A `C¹` function whose derivative has variance at most `v` almost everywhere under a centred
Gaussian measure is integrable. -/
theorem integrable_of_variance_fderiv_le (hμ : μ[id] = 0) (hf : ContDiff ℝ 1 f)
    (hv : ∀ᵐ x ∂μ, Var[fderiv ℝ f x; μ] ≤ v) : Integrable f μ := by
  have h : integrableExpSet f μ = Set.univ :=
    Set.eq_univ_of_forall (integrable_exp_mul_of_variance_fderiv_le hμ hf hv)
  exact integrable_of_mem_interior_integrableExpSet (by simp [h])

/-- **Gaussian concentration, exponential-moment form.** If `f` is `C¹` and its derivative has
variance at most `v` under a centred Gaussian measure `μ` at almost every point, then `f - 𝔼 f` is
sub-Gaussian with variance proxy `π² v / 4`: `𝔼 exp (t (f - 𝔼 f)) ≤ exp (π² t² v / 8)`. -/
theorem hasSubgaussianMGF_sub_integral_of_variance_fderiv_le (hμ : μ[id] = 0)
    (hf : ContDiff ℝ 1 f) (hv : ∀ᵐ x ∂μ, Var[fderiv ℝ f x; μ] ≤ v) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂μ) (NNReal.pi ^ 2 / 4 * v) μ := by
  set m := ∫ y, f y ∂μ
  have hfi := integrable_of_variance_fderiv_le hμ hf hv
  have hint (t : ℝ) : Integrable (fun x ↦ exp (t * (f x - m))) μ := by
    have h := (integrable_exp_mul_of_variance_fderiv_le hμ hf hv t).mul_const (exp (-t * m))
    refine h.congr (.of_forall fun x ↦ ?_)
    simp only [← exp_add]
    congr 1
    ring
  refine ⟨hint, fun t ↦ ?_⟩
  have hc : ((NNReal.pi ^ 2 / 4 * v : ℝ≥0) : ℝ) * t ^ 2 / 2 = π ^ 2 * t ^ 2 / 8 * v := by
    push_cast [NNReal.coe_real_pi]
    ring
  rw [hc, ← ENNReal.ofReal_le_ofReal_iff (exp_pos _).le]
  calc ENNReal.ofReal (mgf (fun x ↦ f x - m) μ t)
      ≤ ∫⁻ p, .ofReal (exp (t * (f p.1 - f p.2))) ∂μ.prod μ :=
        TauCeti.ofReal_mgf_sub_integral_le_lintegral hfi
          (hint t) (integrable_exp_mul_of_variance_fderiv_le hμ hf hv (-t))
    _ = ∫⁻ p, .ofReal (exp ((-t) * (f p.2 - f p.1))) ∂μ.prod μ :=
        lintegral_congr fun p ↦ by congr 2; ring
    _ ≤ .ofReal (exp (π ^ 2 * (-t) ^ 2 / 8 * v)) :=
        lintegral_exp_mul_sub_le_of_variance_fderiv_le hμ hf hv (-t)
    _ = .ofReal (exp (π ^ 2 * t ^ 2 / 8 * v)) := by rw [neg_sq]

/-- **Gaussian concentration.** If `f` is `C¹` and its derivative has variance at most `v` under
a centred Gaussian measure `μ` at almost every point, then for `ε ≥ 0`,
`μ {x | ε ≤ |f x - 𝔼 f|} ≤ 2 exp (-2 ε² / (π² v))`. -/
theorem measureReal_setOf_le_abs_sub_integral_le_of_variance_fderiv_le (hμ : μ[id] = 0)
    (hf : ContDiff ℝ 1 f) (hv : ∀ᵐ x ∂μ, Var[fderiv ℝ f x; μ] ≤ v) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {x | ε ≤ |f x - ∫ y, f y ∂μ|} ≤ 2 * exp (-2 * ε ^ 2 / (π ^ 2 * v)) := by
  set m := ∫ y, f y ∂μ
  have h := hasSubgaussianMGF_sub_integral_of_variance_fderiv_le hμ hf hv
  have hc : -ε ^ 2 / (2 * ((NNReal.pi ^ 2 / 4 * v : ℝ≥0) : ℝ)) = -2 * ε ^ 2 / (π ^ 2 * v) := by
    rw [show 2 * ((NNReal.pi ^ 2 / 4 * v : ℝ≥0) : ℝ) = π ^ 2 * v / 2 by
      push_cast [NNReal.coe_real_pi]; ring, div_div_eq_mul_div]
    ring
  have hsub : {x | ε ≤ |f x - m|} ⊆ {x | ε ≤ f x - m} ∪ {x | ε ≤ (-fun x ↦ f x - m) x} := by
    intro x hx
    rw [Set.mem_ofPred_eq, le_abs'] at hx
    rcases hx with hx | hx
    · exact Or.inr (by simp only [Set.mem_ofPred_eq, Pi.neg_apply]; linarith)
    · exact Or.inl hx
  calc μ.real {x | ε ≤ |f x - m|}
      ≤ μ.real {x | ε ≤ f x - m} + μ.real {x | ε ≤ (-fun x ↦ f x - m) x} :=
        (measureReal_mono hsub).trans (measureReal_union_le _ _)
    _ ≤ exp (-2 * ε ^ 2 / (π ^ 2 * v)) + exp (-2 * ε ^ 2 / (π ^ 2 * v)) := by
        rw [← hc]
        exact add_le_add (h.measure_ge_le hε) (h.neg.measure_ge_le hε)
    _ = 2 * exp (-2 * ε ^ 2 / (π ^ 2 * v)) := by ring

end Gaussian

end ProbabilityTheory.IsGaussian

namespace TauCeti.Probability

section StdGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {f : E → ℝ} {K : ℝ≥0}

/-- Under the standard Gaussian measure, the variance of the derivative of `f` is at most `K²`
when `‖f' x‖ ≤ K` everywhere. -/
private lemma variance_fderiv_stdGaussian_le (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K) (x : E) :
    Var[fderiv ℝ f x; stdGaussian E] ≤ ((K ^ 2 : ℝ≥0) : ℝ) := by
  rw [variance_dual_stdGaussian, NNReal.coe_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hK x) 2

/-- Under the standard Gaussian measure, a `C¹` function `f` with `‖f' x‖ ≤ K` everywhere (that
is, a `C¹` function which is `K`-Lipschitz) is sub-Gaussian about its mean with variance proxy
`π² K² / 4`. -/
theorem hasSubgaussianMGF_stdGaussian_sub_integral (hf : ContDiff ℝ 1 f)
    (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂stdGaussian E)
      (NNReal.pi ^ 2 / 4 * K ^ 2) (stdGaussian E) :=
  IsGaussian.hasSubgaussianMGF_sub_integral_of_variance_fderiv_le (by simp) hf
    (.of_forall (variance_fderiv_stdGaussian_le hK))

/-- **Gaussian concentration for the standard Gaussian measure.** If `f` is `C¹` with
`‖f' x‖ ≤ K` everywhere, then for `ε ≥ 0`,
`γ {x | ε ≤ |f x - 𝔼 f|} ≤ 2 exp (-2 ε² / (π² K²))` for the standard Gaussian measure `γ`. -/
theorem measureReal_stdGaussian_setOf_le_abs_sub_integral_le (hf : ContDiff ℝ 1 f)
    (hK : ∀ x, ‖fderiv ℝ f x‖ ≤ K) {ε : ℝ} (hε : 0 ≤ ε) :
    (stdGaussian E).real {x | ε ≤ |f x - ∫ y, f y ∂stdGaussian E|} ≤
      2 * exp (-2 * ε ^ 2 / (π ^ 2 * K ^ 2)) := by
  simpa using IsGaussian.measureReal_setOf_le_abs_sub_integral_le_of_variance_fderiv_le
    (by simp) hf (.of_forall (variance_fderiv_stdGaussian_le hK)) hε

end StdGaussian

end TauCeti.Probability
