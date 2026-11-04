/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound
import TauCeti.Probability.Distributions.Gaussian.ChiSquared
import TauCeti.Probability.Moments.Basic

/-!
# Squared and directional exponential moments of sub-Gaussian random variables

This file develops the squared-variable exponential moment bounds for
`ProbabilityTheory.HasSubgaussianMGF` needed for quadratic-form concentration (such as the
Hanson–Wright inequality), together with directional sub-Gaussianity for complex random variables.

Starting from Mathlib's sub-Gaussian moment-generating function hypothesis
`∀ t, mgf X μ t ≤ exp (c * t ^ 2 / 2)`, we prove:
* `HasSubgaussianMGF.mono`, `HasSubgaussianMGF.const_mul_nnnorm`, and `HasLaw.hasSubgaussianMGF`
  for centred Gaussian laws;
* `HasSubgaussianMGF.integral_eq_zero`: every sub-Gaussian random variable under a zero or
  probability measure has expectation zero;
* `HasSubgaussianMGF.integrable_exp_mul_sq` and `HasSubgaussianMGF.integral_exp_mul_sq_le`:
  introducing an auxiliary standard Gaussian variable and applying Tonelli's theorem shows that
  `∫ ω, exp (s * X ω ^ 2) ∂μ ≤ (1 - 2 * c * s) ^ (-1 / 2)` for `0 ≤ s` and `2 * c * s < 1`;
* `HasSubgaussianMGF.mgf_sq_sub_integral_le`: the centred square `X ^ 2 - μ[X ^ 2]` has
  sub-exponential moment-generating function bounded by `exp (384 * c ^ 2 * θ ^ 2)` for
  `c * |θ| ≤ 1 / 8`;
* `ProbabilityTheory.mgf_add_le_of_mgf_two_mul_le`,
  `ProbabilityTheory.measureReal_gt_le_exp_min_of_mgf_le`, and
  `ProbabilityTheory.measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le`: AM-GM combination of two MGF
  bounds without independence and sub-exponential Chernoff tail bounds with dual quadratic/linear
  rate;
* Complex directional sub-Gaussianity `∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re)
  (‖u‖₊ ^ 2 * K) μ`: component extraction, integrability, zero mean, centred squared-norm MGF
  bounds, and constructors for bounded mean-zero complex variables (including unit-modulus
  Steinhaus / circular variables) and variables with independent sub-Gaussian real and imaginary
  parts.

## References

* [R. Vershynin, *High-Dimensional Probability*][vershynin2018high], §2.5–2.7.
* [M. Rudelson, R. Vershynin, *Hanson–Wright inequality and sub-gaussian
  concentration*][rudelson2013]
-/

public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

section CombineMGF

/-- **AM-GM bound for the moment-generating function of a sum.** Without any independence
assumption, if `exp (2 * θ * X)` and `exp (2 * θ * Y)` are integrable with moment-generating
functions bounded by `M₁` and `M₂`, then `exp (θ * (X + Y))` is integrable and its
moment-generating function at `θ` is bounded by `(M₁ + M₂) / 2`. -/
theorem mgf_add_le_of_mgf_two_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} {θ M₁ M₂ : ℝ}
    (hX_int : Integrable (fun ω ↦ exp (2 * θ * X ω)) μ)
    (hY_int : Integrable (fun ω ↦ exp (2 * θ * Y ω)) μ)
    (hX_le : mgf X μ (2 * θ) ≤ M₁) (hY_le : mgf Y μ (2 * θ) ≤ M₂) :
    Integrable (fun ω ↦ exp (θ * (X ω + Y ω))) μ ∧
      mgf (fun ω ↦ X ω + Y ω) μ θ ≤ (M₁ + M₂) / 2 := by
  have hsqrt : (fun ω ↦ exp (θ * (X ω + Y ω))) =
      fun ω ↦ Real.sqrt (exp (2 * θ * X ω) * exp (2 * θ * Y ω)) := by
    ext ω
    have hsq : exp (2 * θ * X ω) * exp (2 * θ * Y ω) = (exp (θ * (X ω + Y ω))) ^ 2 := by
      rw [← exp_add, sq, ← exp_add]
      congr 1
      ring
    rw [hsq, Real.sqrt_sq (exp_pos _).le]
  have hpt : ∀ ω, exp (θ * (X ω + Y ω)) ≤ (exp (2 * θ * X ω) + exp (2 * θ * Y ω)) / 2 := by
    intro ω
    have hsq : 0 ≤ (exp (θ * X ω) - exp (θ * Y ω)) ^ 2 := sq_nonneg _
    have hx2 : exp (2 * θ * X ω) = exp (θ * X ω) ^ 2 := by
      rw [sq, ← exp_add]; congr 1; ring
    have hy2 : exp (2 * θ * Y ω) = exp (θ * Y ω) ^ 2 := by
      rw [sq, ← exp_add]; congr 1; ring
    have hxy : exp (θ * (X ω + Y ω)) = exp (θ * X ω) * exp (θ * Y ω) := by
      rw [mul_add, exp_add]
    linarith
  have haesm : AEStronglyMeasurable (fun ω ↦ exp (θ * (X ω + Y ω))) μ := by
    rw [hsqrt]
    exact continuous_sqrt.comp_aestronglyMeasurable (hX_int.1.mul hY_int.1)
  have hdom : Integrable (fun ω ↦ (exp (2 * θ * X ω) + exp (2 * θ * Y ω)) / 2) μ :=
    (hX_int.add hY_int).div_const 2
  have hint : Integrable (fun ω ↦ exp (θ * (X ω + Y ω))) μ :=
    hdom.mono' haesm (ae_of_all _ fun ω ↦ by
      rw [Real.norm_of_nonneg (exp_pos _).le]
      exact hpt ω)
  refine ⟨hint, ?_⟩
  rw [mgf]
  calc ∫ ω, exp (θ * (X ω + Y ω)) ∂μ
      ≤ ∫ ω, (exp (2 * θ * X ω) + exp (2 * θ * Y ω)) / 2 ∂μ :=
        integral_mono hint hdom hpt
    _ = (mgf X μ (2 * θ) + mgf Y μ (2 * θ)) / 2 := by
        rw [integral_div, integral_add hX_int hY_int, mgf, mgf]
    _ ≤ (M₁ + M₂) / 2 := by linarith

/-- **Geometric-mean bound for the moment-generating function of a sum.** Without any independence
assumption, if `exp (2 * θ * X)` and `exp (2 * θ * Y)` are integrable with moment-generating
functions bounded by `exp a` and `exp b`, then `exp (θ * (X + Y))` is integrable and its
moment-generating function at `θ` is bounded by `exp ((a + b) / 2)`. -/
theorem mgf_add_le_exp_half_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} {θ a b : ℝ}
    (hX_int : Integrable (fun ω ↦ exp (2 * θ * X ω)) μ)
    (hY_int : Integrable (fun ω ↦ exp (2 * θ * Y ω)) μ)
    (hX_le : mgf X μ (2 * θ) ≤ exp a) (hY_le : mgf Y μ (2 * θ) ≤ exp b) :
    Integrable (fun ω ↦ exp (θ * (X ω + Y ω))) μ ∧
      mgf (fun ω ↦ X ω + Y ω) μ θ ≤ exp ((a + b) / 2) := by
  have hint := (mgf_add_le_of_mgf_two_mul_le hX_int hY_int hX_le hY_le).1
  refine ⟨hint, ?_⟩
  have hpt : ∀ ω, exp (θ * (X ω + Y ω)) ≤ exp ((a + b) / 2) / 2 *
      (exp (-a) * exp (2 * θ * X ω) + exp (-b) * exp (2 * θ * Y ω)) := by
    intro ω
    have hx2 : exp (-a) * exp (2 * θ * X ω) = exp (θ * X ω - a / 2) ^ 2 := by
      rw [sq, ← exp_add, ← exp_add]; congr 1; ring
    have hy2 : exp (-b) * exp (2 * θ * Y ω) = exp (θ * Y ω - b / 2) ^ 2 := by
      rw [sq, ← exp_add, ← exp_add]; congr 1; ring
    have hxy : exp (θ * (X ω + Y ω)) =
        exp ((a + b) / 2) * (exp (θ * X ω - a / 2) * exp (θ * Y ω - b / 2)) := by
      rw [← exp_add, ← exp_add]; congr 1; ring
    have hamgm : exp (θ * X ω - a / 2) * exp (θ * Y ω - b / 2) ≤
        (exp (-a) * exp (2 * θ * X ω) + exp (-b) * exp (2 * θ * Y ω)) / 2 := by
      linarith [two_mul_le_add_sq (exp (θ * X ω - a / 2)) (exp (θ * Y ω - b / 2))]
    rw [hxy]
    exact (mul_le_mul_of_nonneg_left hamgm (exp_pos _).le).trans_eq (by ring)
  have hdom : Integrable (fun ω ↦ exp ((a + b) / 2) / 2 *
      (exp (-a) * exp (2 * θ * X ω) + exp (-b) * exp (2 * θ * Y ω))) μ :=
    ((hX_int.const_mul (exp (-a))).add (hY_int.const_mul (exp (-b)))).const_mul _
  have hX1 : exp (-a) * mgf X μ (2 * θ) ≤ 1 := by
    calc exp (-a) * mgf X μ (2 * θ) ≤ exp (-a) * exp a :=
          mul_le_mul_of_nonneg_left hX_le (exp_pos _).le
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have hY1 : exp (-b) * mgf Y μ (2 * θ) ≤ 1 := by
    calc exp (-b) * mgf Y μ (2 * θ) ≤ exp (-b) * exp b :=
          mul_le_mul_of_nonneg_left hY_le (exp_pos _).le
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  rw [mgf]
  calc ∫ ω, exp (θ * (X ω + Y ω)) ∂μ
      ≤ ∫ ω, exp ((a + b) / 2) / 2 *
          (exp (-a) * exp (2 * θ * X ω) + exp (-b) * exp (2 * θ * Y ω)) ∂μ :=
        integral_mono hint hdom hpt
    _ = exp ((a + b) / 2) / 2 * (exp (-a) * mgf X μ (2 * θ) + exp (-b) * mgf Y μ (2 * θ)) := by
        rw [integral_const_mul, integral_add (hX_int.const_mul _) (hY_int.const_mul _),
          integral_const_mul, integral_const_mul, mgf, mgf]
    _ ≤ exp ((a + b) / 2) / 2 * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add hX1 hY1) (by positivity)
    _ = exp ((a + b) / 2) := by ring

end CombineMGF

/-- A random variable with centred Gaussian law `gaussianReal 0 v` has a sub-Gaussian
moment-generating function with variance proxy `v`. -/
theorem HasLaw.hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) :
    HasSubgaussianMGF X v μ := by
  rw [← HasSubgaussianMGF.id_map_iff hX.aemeasurable, hX.map_eq]
  exact ⟨integrable_exp_mul_gaussianReal, fun t ↦ by simp [mgf_id_gaussianReal]⟩

/-- Centred sub-exponential MGF estimate for an a.e.-nonnegative random variable satisfying an
Orlicz exponential bound `∫ exp (Y / B) ∂μ ≤ 2`. -/
private theorem mgf_sub_integral_le_of_nonneg_exp_le_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY_meas : AEMeasurable Y μ)
    (hY_nonneg : 0 ≤ᵐ[μ] Y) {B : ℝ} (hB : 0 < B)
    (hY_int_exp : Integrable (fun ω ↦ exp (Y ω / B)) μ)
    (hY_exp : ∫ ω, exp (Y ω / B) ∂μ ≤ 2) {θ : ℝ} (hθ : B * |θ| ≤ 1 / 2) :
    Integrable (fun ω ↦ exp (θ * (Y ω - μ[Y]))) μ ∧
      mgf (fun ω ↦ Y ω - μ[Y]) μ θ ≤ exp (24 * B ^ 2 * θ ^ 2) := by
  have hY_le_exp : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ B * exp (Y ω / B) := by
    filter_upwards [hY_nonneg] with ω hω
    rw [Real.norm_of_nonneg hω]
    have h1 : Y ω / B ≤ exp (Y ω / B) := by linarith [add_one_le_exp (Y ω / B)]
    have h2 := mul_le_mul_of_nonneg_left h1 hB.le
    rwa [mul_div_cancel₀ _ hB.ne'] at h2
  have hY_int : Integrable Y μ :=
    (hY_int_exp.const_mul B).mono' hY_meas.aestronglyMeasurable hY_le_exp
  let m : ℝ := μ[Y]
  have hm_nonneg : 0 ≤ m := integral_nonneg_of_ae hY_nonneg
  have hm_le : m ≤ B := by
    have h1 : ∫ ω, (1 + Y ω / B) ∂μ ≤ ∫ ω, exp (Y ω / B) ∂μ :=
      integral_mono ((integrable_const 1).add (hY_int.div_const B)) hY_int_exp
        fun ω ↦ by linarith [add_one_le_exp (Y ω / B)]
    rw [integral_add (integrable_const 1) (hY_int.div_const B), integral_const, probReal_univ,
      one_smul, integral_div] at h1
    have hdiv : m / B ≤ 1 := by linarith
    exact (div_le_one hB).mp hdiv
  let Z : Ω → ℝ := fun ω ↦ Y ω - m
  have hZ_int : Integrable Z μ := hY_int.sub (integrable_const m)
  have hZ_mean : ∫ ω, Z ω ∂μ = 0 := by
    dsimp [Z]
    rw [integral_sub hY_int (integrable_const m), integral_const, probReal_univ, one_smul]
    exact sub_self m
  have hexp_half_le : exp (1 / 2 : ℝ) ≤ 3 := by
    calc exp (1 / 2 : ℝ) ≤ exp 1 := exp_le_exp.2 (by norm_num)
      _ ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hpt : ∀ᵐ ω ∂μ,
      exp (θ * Z ω) ≤ 1 + θ * Z ω + 12 * B ^ 2 * θ ^ 2 * exp (Y ω / B) := by
    filter_upwards [hY_nonneg] with ω hω
    let u : ℝ := Y ω / B
    have hu0 : 0 ≤ u := div_nonneg hω hB.le
    have hY_eq : Y ω = B * u := by dsimp [u]; exact (mul_div_cancel₀ _ hB.ne').symm
    have hZ_abs : |Z ω| ≤ B * (u + 1) := by
      dsimp [Z]
      rw [abs_le]
      constructor <;> nlinarith
    have hθZ_abs : |θ * Z ω| ≤ u / 2 + 1 / 2 := by
      rw [abs_mul]
      calc |θ| * |Z ω| ≤ |θ| * (B * (u + 1)) :=
            mul_le_mul_of_nonneg_left hZ_abs (abs_nonneg θ)
        _ = (B * |θ|) * (u + 1) := by ring
        _ ≤ (1 / 2) * (u + 1) :=
            mul_le_mul_of_nonneg_right hθ (by positivity)
        _ = u / 2 + 1 / 2 := by ring
    have hu_quad : (u + 1) ^ 2 ≤ 8 * exp (u / 2) := by
      have hq1 : (u + 1) ^ 2 ≤ 8 * (1 + u / 2 + (u / 2) ^ 2 / 2) := by nlinarith
      have hq2 : 1 + u / 2 + (u / 2) ^ 2 / 2 ≤ exp (u / 2) :=
        Real.quadratic_le_exp_of_nonneg (by positivity)
      linarith
    have hu_exp : (u + 1) ^ 2 * exp (u / 2 + 1 / 2) ≤ 24 * exp u := by
      rw [exp_add]
      have hmul : (u + 1) ^ 2 * (exp (u / 2) * exp (1 / 2)) ≤
          (8 * exp (u / 2)) * (exp (u / 2) * 3) := by
        refine mul_le_mul hu_quad ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hexp_half_le (exp_pos _).le
      have hexp2 : exp (u / 2) * exp (u / 2) = exp u := by
        rw [← exp_add]; congr 1; ring
      linarith
    have hZ_sq : (θ * Z ω) ^ 2 ≤ B ^ 2 * θ ^ 2 * (u + 1) ^ 2 := by
      have h1 : Z ω ^ 2 ≤ (B * (u + 1)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hZ_abs 2
      calc (θ * Z ω) ^ 2 = θ ^ 2 * Z ω ^ 2 := by ring
        _ ≤ θ ^ 2 * (B * (u + 1)) ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg θ)
        _ = B ^ 2 * θ ^ 2 * (u + 1) ^ 2 := by ring
    have hrem : (θ * Z ω) ^ 2 / 2 * exp |θ * Z ω| ≤
        12 * B ^ 2 * θ ^ 2 * exp u := by
      have h1 : (θ * Z ω) ^ 2 / 2 * exp |θ * Z ω| ≤
          (B ^ 2 * θ ^ 2 * (u + 1) ^ 2 / 2) * exp (u / 2 + 1 / 2) := by
        refine mul_le_mul (by linarith) (exp_le_exp.2 hθZ_abs) (exp_pos _).le ?_
        positivity
      have h2 : (B ^ 2 * θ ^ 2 * (u + 1) ^ 2 / 2) * exp (u / 2 + 1 / 2) =
          (B ^ 2 * θ ^ 2 / 2) * ((u + 1) ^ 2 * exp (u / 2 + 1 / 2)) := by ring
      rw [h2] at h1
      have h3 := mul_le_mul_of_nonneg_left hu_exp (by positivity : 0 ≤ B ^ 2 * θ ^ 2 / 2)
      linarith
    exact (Real.exp_le_one_add_add_sq_div_two_mul_exp_abs (θ * Z ω)).trans (by linarith)
  have hdom : Integrable (fun ω ↦ 1 + θ * Z ω + 12 * B ^ 2 * θ ^ 2 * exp (Y ω / B)) μ :=
    ((integrable_const 1).add (hZ_int.const_mul θ)).add
      (hY_int_exp.const_mul (12 * B ^ 2 * θ ^ 2))
  have haesm : AEStronglyMeasurable (fun ω ↦ exp (θ * Z ω)) μ := by
    have hZ_meas : AEMeasurable Z μ := hY_meas.sub_const m
    exact (Real.measurable_exp.comp_aemeasurable (hZ_meas.const_mul θ)).aestronglyMeasurable
  have hint : Integrable (fun ω ↦ exp (θ * Z ω)) μ :=
    hdom.mono' haesm (hpt.mono fun ω hω ↦ by
      rw [Real.norm_of_nonneg (exp_pos _).le]
      exact hω)
  refine ⟨hint, ?_⟩
  rw [mgf]
  calc ∫ ω, exp (θ * Z ω) ∂μ
      ≤ ∫ ω, (1 + θ * Z ω + 12 * B ^ 2 * θ ^ 2 * exp (Y ω / B)) ∂μ :=
        integral_mono_ae hint hdom hpt
    _ = 1 + θ * ∫ ω, Z ω ∂μ + 12 * B ^ 2 * θ ^ 2 * ∫ ω, exp (Y ω / B) ∂μ := by
        have hf1 : Integrable (fun ω ↦ 1 + θ * Z ω) μ :=
          (integrable_const 1).add (hZ_int.const_mul θ)
        rw [integral_add hf1 (hY_int_exp.const_mul _),
          integral_add (integrable_const 1) (hZ_int.const_mul θ),
          integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul]
    _ ≤ 1 + 24 * B ^ 2 * θ ^ 2 := by
        rw [hZ_mean, mul_zero, add_zero]
        nlinarith [sq_nonneg (B * θ)]
    _ ≤ exp (24 * B ^ 2 * θ ^ 2) := by
        linarith [add_one_le_exp (24 * B ^ 2 * θ ^ 2)]

namespace HasSubgaussianMGF

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- Monotonicity of `HasSubgaussianMGF` in the variance proxy. -/
theorem mono {c₁ c₂ : ℝ≥0} (h : HasSubgaussianMGF X c₁ μ) (hle : c₁ ≤ c₂) :
    HasSubgaussianMGF X c₂ μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans <| by gcongr

/-- Scalar multiplication scales the sub-Gaussian variance proxy by `‖r‖₊ ^ 2`. -/
theorem const_mul_nnnorm (h : HasSubgaussianMGF X c μ) (r : ℝ) :
    HasSubgaussianMGF (fun ω ↦ r * X ω) (‖r‖₊ ^ 2 * c) μ where
  integrable_exp_mul t := by
    simpa only [← mul_assoc] using h.integrable_exp_mul (t * r)
  mgf_le t := by
    rw [mgf_const_mul]
    refine (h.mgf_le (r * t)).trans_eq ?_
    congr 1
    push_cast
    simp only [Real.norm_eq_abs, sq_abs]
    ring

/-- Under a zero or probability measure, every random variable with a sub-Gaussian
moment-generating function has expectation zero. -/
theorem integral_eq_zero [IsZeroOrProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ) :
    μ[X] = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hprob
  · simp
  · let m : ℝ := μ[X]
    have hquad : ∀ t : ℝ, t * m ≤ (c : ℝ) * t ^ 2 / 2 := by
      intro t
      have hX_int : Integrable X μ := h.integrable
      have hdiff_int : Integrable (fun ω ↦ X ω - m) μ := hX_int.sub (integrable_const m)
      have hmul_int : Integrable (fun ω ↦ t * (X ω - m)) μ := hdiff_int.const_mul t
      have hf_int : Integrable (fun ω ↦ 1 + t * (X ω - m)) μ := (integrable_const 1).add hmul_int
      have hg_int : Integrable (fun ω ↦ exp (-t * m) * exp (t * X ω)) μ :=
        (h.integrable_exp_mul t).const_mul (exp (-t * m))
      have hpt : ∀ ω, 1 + t * (X ω - m) ≤ exp (-t * m) * exp (t * X ω) := by
        intro ω
        have h1 : 1 + t * (X ω - m) ≤ exp (t * (X ω - m)) := by
          linarith [add_one_le_exp (t * (X ω - m))]
        have h2 : exp (t * (X ω - m)) = exp (-t * m) * exp (t * X ω) := by
          rw [← exp_add]; congr 1; ring
        linarith
      have hint_le : ∫ ω, (1 + t * (X ω - m)) ∂μ ≤
          ∫ ω, exp (-t * m) * exp (t * X ω) ∂μ := integral_mono hf_int hg_int hpt
      have hlhs : ∫ ω, (1 + t * (X ω - m)) ∂μ = 1 := by
        rw [integral_add (integrable_const 1) hmul_int,
          integral_const, probReal_univ, one_smul, integral_const_mul,
          integral_sub hX_int (integrable_const m), integral_const, probReal_univ, one_smul]
        dsimp only [m]
        simp
      have hrhs : ∫ ω, exp (-t * m) * exp (t * X ω) ∂μ ≤ exp (-t * m + (c : ℝ) * t ^ 2 / 2) := by
        rw [integral_const_mul, ← mgf, exp_add]
        exact mul_le_mul_of_nonneg_left (h.mgf_le t) (exp_pos _).le
      have hexp : 1 ≤ exp (-t * m + (c : ℝ) * t ^ 2 / 2) := by linarith
      have h0 : 0 ≤ -t * m + (c : ℝ) * t ^ 2 / 2 := Real.one_le_exp_iff.mp hexp
      linarith
    have hstep := mul_le_mul_of_nonneg_left (hquad (m / ((c : ℝ) + 1)))
      (by positivity : (0 : ℝ) ≤ 2 * ((c : ℝ) + 1) ^ 2)
    have hc1 : (c : ℝ) + 1 ≠ 0 := by positivity
    have hsimp1 : 2 * ((c : ℝ) + 1) ^ 2 * (m / ((c : ℝ) + 1) * m) =
        2 * ((c : ℝ) + 1) * m ^ 2 := by field_simp
    have hsimp2 : 2 * ((c : ℝ) + 1) ^ 2 * ((c : ℝ) * (m / ((c : ℝ) + 1)) ^ 2 / 2) =
        (c : ℝ) * m ^ 2 := by field_simp
    rw [hsimp1, hsimp2] at hstep
    have hm_nonpos : ((c : ℝ) + 2) * m ^ 2 ≤ 0 := by linarith
    have hm_nonneg : 0 ≤ ((c : ℝ) + 2) * m ^ 2 := by positivity
    have hm_zero : ((c : ℝ) + 2) * m ^ 2 = 0 := le_antisymm hm_nonpos hm_nonneg
    have hc2 : (c : ℝ) + 2 ≠ 0 := by positivity
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hm_zero).resolve_left hc2)

private theorem lintegral_ofReal_exp_mul_sq_le (h : HasSubgaussianMGF X c μ) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : 2 * (c : ℝ) * s < 1) :
    ∫⁻ ω, ENNReal.ofReal (exp (s * X ω ^ 2)) ∂μ ≤
      ENNReal.ofReal ((1 - 2 * (c : ℝ) * s) ^ (-1 / 2 : ℝ)) := by
  have : IsFiniteMeasure μ :=
    TauCeti.isFiniteMeasure_of_zero_mem_integrableExpSet (X := X)
      (by simpa [integrableExpSet] using h.integrable_exp_mul 0)
  let X₀ : Ω → ℝ := h.aemeasurable.mk X
  have hX₀_meas : Measurable X₀ := h.aemeasurable.measurable_mk
  have hX₀_eq : X =ᵐ[μ] X₀ := h.aemeasurable.ae_eq_mk
  have h₀ : HasSubgaussianMGF X₀ c μ := h.congr hX₀_eq
  let γ : Measure ℝ := gaussianReal 0 1
  let F : Ω × ℝ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (exp (Real.sqrt (2 * s) * X₀ p.1 * p.2))
  have hF_meas : Measurable F := by fun_prop
  have hleft : ∀ ω : Ω, ∫⁻ g, F (ω, g) ∂γ = ENNReal.ofReal (exp (s * X₀ ω ^ 2)) := by
    intro ω
    let u : ℝ := Real.sqrt (2 * s) * X₀ ω
    have hu_int : Integrable (fun g : ℝ ↦ exp (u * g)) γ := integrable_exp_mul_gaussianReal u
    have hu_eq : ∫⁻ g, F (ω, g) ∂γ = ENNReal.ofReal (mgf (fun g ↦ g) γ u) := by
      simpa [F, u, mgf] using
        (ofReal_integral_eq_lintegral_ofReal hu_int (ae_of_all _ fun _ ↦ (exp_pos _).le)).symm
    rw [hu_eq, mgf_fun_id_gaussianReal]
    congr 1
    simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
    congr 1
    have hsq : Real.sqrt (2 * s) ^ 2 = 2 * s := Real.sq_sqrt (by positivity)
    calc (Real.sqrt (2 * s) * X₀ ω) ^ 2 / 2
        = Real.sqrt (2 * s) ^ 2 * X₀ ω ^ 2 / 2 := by ring
      _ = s * X₀ ω ^ 2 := by rw [hsq]; ring
  have hright : ∀ g : ℝ, ∫⁻ ω, F (ω, g) ∂μ ≤ ENNReal.ofReal (exp (((c : ℝ) * s) * g ^ 2)) := by
    intro g
    let t : ℝ := Real.sqrt (2 * s) * g
    have ht_eq : ∫⁻ ω, F (ω, g) ∂μ = ENNReal.ofReal (mgf X₀ μ t) := by
      have hrew : (fun ω ↦ F (ω, g)) = fun ω ↦ ENNReal.ofReal (exp (t * X₀ ω)) := by
        ext ω; dsimp [F, t]; ring_nf
      rw [hrew, mgf, ofReal_integral_eq_lintegral_ofReal (h₀.integrable_exp_mul t)
        (ae_of_all _ fun _ ↦ (exp_pos _).le)]
    rw [ht_eq]
    refine ENNReal.ofReal_le_ofReal ((h₀.mgf_le t).trans_eq ?_)
    congr 1
    have hsq : Real.sqrt (2 * s) ^ 2 = 2 * s := Real.sq_sqrt (by positivity)
    calc (c : ℝ) * (Real.sqrt (2 * s) * g) ^ 2 / 2
        = (c : ℝ) * (Real.sqrt (2 * s) ^ 2 * g ^ 2) / 2 := by ring
      _ = ((c : ℝ) * s) * g ^ 2 := by rw [hsq]; ring
  have hw : 2 * (1 : ℝ) * ((c : ℝ) * s) < 1 := by linarith
  have hg_int : Integrable (fun g : ℝ ↦ exp (((c : ℝ) * s) * g ^ 2)) γ := by
    have hmem := (TauCeti.Probability.mem_integrableExpSet_mul_sq_gaussianReal_iff
      ((c : ℝ) * s) 1).2 hw
    simpa [integrableExpSet] using hmem
  have hg_mgf : ∫ g : ℝ, exp (((c : ℝ) * s) * g ^ 2) ∂γ =
      (1 - 2 * (c : ℝ) * s) ^ (-1 / 2 : ℝ) := by
    have hval := TauCeti.Probability.mgf_mul_sq_gaussianReal hw
    simpa [mgf, mul_assoc] using hval
  have hae : (fun ω ↦ ENNReal.ofReal (exp (s * X ω ^ 2))) =ᵐ[μ]
      fun ω ↦ ENNReal.ofReal (exp (s * X₀ ω ^ 2)) :=
    hX₀_eq.mono fun ω hω ↦ by simp [hω]
  calc ∫⁻ ω, ENNReal.ofReal (exp (s * X ω ^ 2)) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (exp (s * X₀ ω ^ 2)) ∂μ := lintegral_congr_ae hae
    _ = ∫⁻ ω, ∫⁻ g, F (ω, g) ∂γ ∂μ := by simp_rw [hleft]
    _ = ∫⁻ p, F p ∂(μ.prod γ) := (lintegral_prod F hF_meas.aemeasurable).symm
    _ = ∫⁻ g, ∫⁻ ω, F (ω, g) ∂μ ∂γ := lintegral_prod_symm' F hF_meas
    _ ≤ ∫⁻ g, ENNReal.ofReal (exp (((c : ℝ) * s) * g ^ 2)) ∂γ := lintegral_mono hright
    _ = ENNReal.ofReal (∫ g, exp (((c : ℝ) * s) * g ^ 2) ∂γ) :=
        (ofReal_integral_eq_lintegral_ofReal hg_int
          (ae_of_all _ fun _ ↦ (exp_pos _).le)).symm
    _ = ENNReal.ofReal ((1 - 2 * (c : ℝ) * s) ^ (-1 / 2 : ℝ)) := by rw [hg_mgf]

/-- For a `c`-sub-Gaussian random variable `X`, `exp (s * X ^ 2)` is integrable whenever
`2 * c * s < 1`. -/
theorem integrable_exp_mul_sq (h : HasSubgaussianMGF X c μ) {s : ℝ}
    (hs : 2 * (c : ℝ) * s < 1) :
    Integrable (fun ω ↦ exp (s * X ω ^ 2)) μ := by
  have : IsFiniteMeasure μ :=
    TauCeti.isFiniteMeasure_of_zero_mem_integrableExpSet (X := X)
      (by simpa [integrableExpSet] using h.integrable_exp_mul 0)
  have haesm : AEStronglyMeasurable (fun ω ↦ exp (s * X ω ^ 2)) μ :=
    (Real.measurable_exp.comp_aemeasurable
      ((h.aemeasurable.pow_const 2).const_mul s)).aestronglyMeasurable
  by_cases hs0 : 0 ≤ s
  · refine ⟨haesm, ?_⟩
    rw [hasFiniteIntegral_def]
    have hnorm : (fun ω ↦ ‖exp (s * X ω ^ 2)‖ₑ) =
        fun ω ↦ ENNReal.ofReal (exp (s * X ω ^ 2)) :=
      funext fun ω ↦ Real.enorm_eq_ofReal (exp_pos _).le
    rw [hnorm]
    exact (h.lintegral_ofReal_exp_mul_sq_le hs0 hs).trans_lt ENNReal.ofReal_lt_top
  · push Not at hs0
    refine Integrable.of_bound haesm 1 (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (exp_pos _).le, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hs0.le (sq_nonneg _)

/-- **Gaussian-comparison bound for squared sub-Gaussian exponential moments.** For `0 ≤ s` and
`2 * c * s < 1`, `∫ ω, exp (s * X ω ^ 2) ∂μ ≤ (1 - 2 * c * s) ^ (-1 / 2)`. -/
theorem integral_exp_mul_sq_le (h : HasSubgaussianMGF X c μ) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : 2 * (c : ℝ) * s < 1) :
    ∫ ω, exp (s * X ω ^ 2) ∂μ ≤ (1 - 2 * (c : ℝ) * s) ^ (-1 / 2 : ℝ) := by
  have hint := h.integrable_exp_mul_sq hs
  have hpos : 0 ≤ (1 - 2 * (c : ℝ) * s) ^ (-1 / 2 : ℝ) := by
    have : 0 < 1 - 2 * (c : ℝ) * s := by linarith
    positivity
  rw [← ENNReal.ofReal_le_ofReal_iff hpos,
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ (exp_pos _).le)]
  exact h.lintegral_ofReal_exp_mul_sq_le hs0 hs

/-- **Sub-exponential MGF bound for a centred squared sub-Gaussian variable.** Under a zero or
probability measure, if `X` has a `c`-sub-Gaussian MGF and `c * |θ| ≤ 1 / 8`, then
`exp (θ * (X ^ 2 - μ[X ^ 2]))` is integrable and
`mgf (fun ω ↦ X ω ^ 2 - μ[fun ω' ↦ X ω' ^ 2]) μ θ ≤ exp (384 * c ^ 2 * θ ^ 2)`. -/
theorem mgf_sq_sub_integral_le [IsZeroOrProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ)
    {θ : ℝ} (hθ : (c : ℝ) * |θ| ≤ 1 / 8) :
    Integrable (fun ω ↦ exp (θ * (X ω ^ 2 - μ[fun ω' ↦ X ω' ^ 2]))) μ ∧
      mgf (fun ω ↦ X ω ^ 2 - μ[fun ω' ↦ X ω' ^ 2]) μ θ ≤ exp (384 * (c : ℝ) ^ 2 * θ ^ 2) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hprob
  · refine ⟨integrable_zero_measure, ?_⟩
    simp only [mgf, integral_zero_measure]
    exact (exp_pos _).le
  · by_cases hc : c = 0
    · subst hc
      have hX0 := h.ae_eq_zero_of_hasSubgaussianMGF_zero
      have hsq0 : (fun ω ↦ X ω ^ 2) =ᵐ[μ] 0 := hX0.mono fun ω hω ↦ by simp [hω]
      have hm0 : μ[fun ω' ↦ X ω' ^ 2] = 0 := by
        rw [integral_congr_ae hsq0]
        simp
      have hexp1 : (fun ω ↦ exp (θ * (X ω ^ 2 - μ[fun ω' ↦ X ω' ^ 2]))) =ᵐ[μ] fun _ ↦ 1 := by
        filter_upwards [hX0] with ω hω
        simp only [Pi.zero_apply] at hω
        simp [hω, hm0]
      refine ⟨(integrable_const 1).congr hexp1.symm, ?_⟩
      rw [mgf, integral_congr_ae hexp1, integral_const, probReal_univ, one_smul]
      exact Real.one_le_exp (by positivity)
    · have hc_pos : 0 < (c : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
      let B : ℝ := 4 * (c : ℝ)
      have hB : 0 < B := by positivity
      have hs_lt : 2 * (c : ℝ) * B⁻¹ < 1 := by
        dsimp [B]
        field_simp
        norm_num
      have hexp_int : Integrable (fun ω ↦ exp (X ω ^ 2 / B)) μ := by
        simpa [div_eq_inv_mul] using h.integrable_exp_mul_sq hs_lt
      have hexp_le : ∫ ω, exp (X ω ^ 2 / B) ∂μ ≤ 2 := by
        have h1 : ∫ ω, exp (B⁻¹ * X ω ^ 2) ∂μ ≤ (1 - 2 * (c : ℝ) * B⁻¹) ^ (-1 / 2 : ℝ) :=
          h.integral_exp_mul_sq_le (by positivity) hs_lt
        have hval : 1 - 2 * (c : ℝ) * B⁻¹ = 1 / 2 := by
          dsimp [B]
          field_simp
          norm_num
        have hrpow : (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) ≤ 2 := by
          have hneg : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by norm_num
          rw [hneg, Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
          have hinv : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
          rw [hinv]
          calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        rw [hval] at h1
        simpa [div_eq_inv_mul] using h1.trans hrpow
      have hBθ : B * |θ| ≤ 1 / 2 := by dsimp [B]; linarith
      obtain ⟨hint, hmgf⟩ := mgf_sub_integral_le_of_nonneg_exp_le_two
        (h.aemeasurable.pow_const 2) (ae_of_all _ fun ω ↦ sq_nonneg _) hB hexp_int hexp_le hBθ
      refine ⟨hint, hmgf.trans_eq ?_⟩
      dsimp [B]
      ring_nf

end HasSubgaussianMGF

section ComplexSubGaussian

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → ℂ} {K : ℝ≥0}

/-- Real-part projection of a directionally `K`-sub-Gaussian complex random variable. -/
theorem hasSubgaussianMGF_re_of_star_mul
    (hZ : ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ) :
    HasSubgaussianMGF (fun ω ↦ (Z ω).re) K μ := by
  simpa using hZ 1

/-- Imaginary-part projection of a directionally `K`-sub-Gaussian complex random variable. -/
theorem hasSubgaussianMGF_im_of_star_mul
    (hZ : ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ) :
    HasSubgaussianMGF (fun ω ↦ (Z ω).im) K μ := by
  have hI := hZ Complex.I
  have hre : (fun ω ↦ (star Complex.I * Z ω).re) = fun ω ↦ (Z ω).im := by
    ext ω
    simp [Complex.mul_re]
  simpa [hre] using hI

/-- Every directionally sub-Gaussian complex random variable is Bochner integrable. -/
theorem integrable_of_hasSubgaussianMGF_re_star_mul
    (hZ : ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ) :
    Integrable Z μ := by
  have hre := (hasSubgaussianMGF_re_of_star_mul hZ).integrable
  have him := (hasSubgaussianMGF_im_of_star_mul hZ).integrable
  have hdecomp : Z = fun ω ↦ ((Z ω).re : ℂ) + ((Z ω).im : ℂ) * Complex.I :=
    funext fun ω ↦ (Complex.re_add_im (Z ω)).symm
  rw [hdecomp]
  exact hre.ofReal.add (him.ofReal.mul_const Complex.I)

/-- Under a zero or probability measure, every directionally sub-Gaussian complex random variable
has expectation zero. -/
theorem integral_eq_zero_of_hasSubgaussianMGF_re_star_mul [IsZeroOrProbabilityMeasure μ]
    (hZ : ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ) :
    ∫ ω, Z ω ∂μ = 0 := by
  have hZ_int := integrable_of_hasSubgaussianMGF_re_star_mul hZ
  have hre := (hasSubgaussianMGF_re_of_star_mul hZ).integral_eq_zero
  have him := (hasSubgaussianMGF_im_of_star_mul hZ).integral_eq_zero
  apply Complex.ext
  · simpa using (Complex.reCLM.integral_comp_comm hZ_int).symm.trans hre
  · simpa using (Complex.imCLM.integral_comp_comm hZ_int).symm.trans him

/-- **Sub-exponential MGF bound for the centred squared norm of a directionally `K`-sub-Gaussian
complex variable.** For `K * |θ| ≤ 1 / 16`, `exp (θ * (‖Z‖ ^ 2 - μ[‖Z‖ ^ 2]))` is integrable and
bounded in MGF by `exp (1536 * K ^ 2 * θ ^ 2)`. -/
theorem mgf_norm_sq_sub_integral_le_of_hasSubgaussianMGF_re_star_mul
    [IsZeroOrProbabilityMeasure μ]
    (hZ : ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ)
    {θ : ℝ} (hθ : (K : ℝ) * |θ| ≤ 1 / 16) :
    Integrable (fun ω ↦ exp (θ * (‖Z ω‖ ^ 2 - μ[fun ω' ↦ ‖Z ω'‖ ^ 2]))) μ ∧
      mgf (fun ω ↦ ‖Z ω‖ ^ 2 - μ[fun ω' ↦ ‖Z ω'‖ ^ 2]) μ θ ≤
        exp (1536 * (K : ℝ) ^ 2 * θ ^ 2) := by
  have hre := hasSubgaussianMGF_re_of_star_mul hZ
  have him := hasSubgaussianMGF_im_of_star_mul hZ
  have h2θ : (K : ℝ) * |2 * θ| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  obtain ⟨hre_int, hre_mgf⟩ := hre.mgf_sq_sub_integral_le h2θ
  obtain ⟨him_int, him_mgf⟩ := him.mgf_sq_sub_integral_le h2θ
  have hnorm_sq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z ↦ by
    rw [Complex.sq_norm, Complex.normSq_apply, sq, sq]
  have hre_sq_int : Integrable (fun ω ↦ (Z ω).re ^ 2) μ := (hre.memLp 2).integrable_sq
  have him_sq_int : Integrable (fun ω ↦ (Z ω).im ^ 2) μ := (him.memLp 2).integrable_sq
  have hsplit_pt : ∀ ω, ‖Z ω‖ ^ 2 - μ[fun ω' ↦ ‖Z ω'‖ ^ 2] =
      ((Z ω).re ^ 2 - μ[fun ω' ↦ (Z ω').re ^ 2]) +
        ((Z ω).im ^ 2 - μ[fun ω' ↦ (Z ω').im ^ 2]) := by
    intro ω
    simp_rw [hnorm_sq]
    rw [integral_add hre_sq_int him_sq_int]
    ring
  simp_rw [hsplit_pt]
  obtain ⟨hint, hle⟩ := mgf_add_le_of_mgf_two_mul_le hre_int him_int hre_mgf him_mgf
  refine ⟨hint, hle.trans_eq ?_⟩
  have hval : 384 * (K : ℝ) ^ 2 * (2 * θ) ^ 2 = 1536 * (K : ℝ) ^ 2 * θ ^ 2 := by ring
  rw [hval]
  ring

/-- **Hoeffding directional sub-Gaussianity for bounded mean-zero complex random variables**
(including Steinhaus / circular unit-modulus variables with `b = 1`). -/
theorem hasSubgaussianMGF_re_star_mul_of_norm_le [IsProbabilityMeasure μ]
    (hZ_meas : AEMeasurable Z μ) {b : ℝ≥0} (hZ_norm : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ b)
    (hZ_mean : ∫ ω, Z ω ∂μ = 0) (u : ℂ) :
    HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * b ^ 2) μ := by
  have hZ_int : Integrable Z μ := Integrable.of_bound hZ_meas.aestronglyMeasurable b hZ_norm
  have hproj_meas : AEMeasurable (fun ω ↦ (star u * Z ω).re) μ :=
    Complex.continuous_re.measurable.comp_aemeasurable (hZ_meas.const_mul (star u))
  have hproj_Icc : ∀ᵐ ω ∂μ,
      (star u * Z ω).re ∈ Set.Icc (-(‖u‖ * (b : ℝ))) (‖u‖ * (b : ℝ)) := by
    filter_upwards [hZ_norm] with ω hω
    rw [Set.mem_Icc, ← abs_le]
    calc |(star u * Z ω).re| ≤ ‖star u * Z ω‖ := Complex.abs_re_le_norm _
      _ = ‖u‖ * ‖Z ω‖ := by rw [norm_mul, norm_star]
      _ ≤ ‖u‖ * (b : ℝ) := mul_le_mul_of_nonneg_left hω (norm_nonneg u)
  have hproj_mean : ∫ ω, (star u * Z ω).re ∂μ = 0 := by
    have hmul_int : Integrable (fun ω ↦ star u * Z ω) μ := hZ_int.const_mul (star u)
    simpa [integral_const_mul, hZ_mean] using Complex.reCLM.integral_comp_comm hmul_int
  have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hproj_meas hproj_Icc hproj_mean
  have hparam : (‖‖u‖ * (b : ℝ) - -(‖u‖ * (b : ℝ))‖₊ / 2) ^ 2 = ‖u‖₊ ^ 2 * b ^ 2 := by
    apply NNReal.coe_injective
    push_cast
    have hnn : 0 ≤ ‖u‖ * (b : ℝ) - -(‖u‖ * (b : ℝ)) := by
      linarith [mul_nonneg (norm_nonneg u) b.coe_nonneg]
    rw [Real.norm_of_nonneg hnn]
    ring
  rwa [hparam] at hsub

/-- A complex random variable whose real and imaginary parts are independent and `K`-sub-Gaussian
is directionally `K`-sub-Gaussian. -/
theorem hasSubgaussianMGF_re_star_mul_of_indepFun_re_im
    (hre : HasSubgaussianMGF (fun ω ↦ (Z ω).re) K μ)
    (him : HasSubgaussianMGF (fun ω ↦ (Z ω).im) K μ)
    (hindep : IndepFun (fun ω ↦ (Z ω).re) (fun ω ↦ (Z ω).im) μ) (u : ℂ) :
    HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ := by
  have hexpand : (fun ω ↦ (star u * Z ω).re) =
      fun ω ↦ u.re * (Z ω).re + u.im * (Z ω).im := by
    ext ω
    simp [Complex.mul_re]
  rw [hexpand]
  have h1 := hre.const_mul_nnnorm u.re
  have h2 := him.const_mul_nnnorm u.im
  have hind : IndepFun (fun ω ↦ u.re * (Z ω).re) (fun ω ↦ u.im * (Z ω).im) μ :=
    hindep.comp (measurable_const_mul u.re) (measurable_const_mul u.im)
  have hsum := h1.add_of_indepFun h2 hind
  refine hsum.mono ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  simp only [Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply]
  exact le_of_eq (by ring)

end ComplexSubGaussian

/-! ### Sub-exponential Chernoff bounds with dual quadratic/linear rate -/

section SubExponentialChernoff

/-- **One-sided sub-exponential Chernoff bound.** If `mgf Y P θ ≤ exp (C₁ * F * θ ^ 2)` for every
`θ` with `C₂ * op * |θ| ≤ 1` (`C₁, C₂ > 0`, `F, op ≥ 0`), then for all `t ≥ 0`,
`P.real {ω | t < Y ω} ≤ exp (-min (1 / (4 * C₁)) (1 / (2 * C₂)) * min (t ^ 2 / F) (t / op))`. -/
theorem measureReal_gt_le_exp_min_of_mgf_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} {C₁ C₂ F op : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hF : 0 ≤ F) (hop : 0 ≤ op)
    (hmgf : ∀ θ : ℝ, C₂ * op * |θ| ≤ 1 →
      Integrable (fun ω ↦ exp (θ * Y ω)) P ∧ mgf Y P θ ≤ exp (C₁ * F * θ ^ 2))
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < Y ω} ≤
      exp (-min (1 / (4 * C₁)) (1 / (2 * C₂)) * min (t ^ 2 / F) (t / op)) := by
  let c : ℝ := min (1 / (4 * C₁)) (1 / (2 * C₂))
  rcases hF.eq_or_lt with rfl | hF_pos
  · have hmin : min (t ^ 2 / (0 : ℝ)) (t / op) = 0 := by
      simp [div_nonneg ht hop]
    rw [hmin, mul_zero, exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  rcases hop.eq_or_lt with rfl | hop_pos
  · have hmin : min (t ^ 2 / F) (t / (0 : ℝ)) = 0 := by
      simp [div_nonneg (sq_nonneg t) hF_pos.le]
    rw [hmin, mul_zero, exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  let θ : ℝ := min (t / (2 * C₁ * F)) (1 / (C₂ * op))
  have hθ_nonneg : 0 ≤ θ := le_min (by positivity) (by positivity)
  have hθ_le_lin : θ ≤ 1 / (C₂ * op) := min_le_right _ _
  have hθ_le_quad : θ ≤ t / (2 * C₁ * F) := min_le_left _ _
  have hθ_dom : C₂ * op * |θ| ≤ 1 := by
    rw [abs_of_nonneg hθ_nonneg]
    have hpos : 0 < C₂ * op := mul_pos hC₂ hop_pos
    calc C₂ * op * θ ≤ C₂ * op * (1 / (C₂ * op)) :=
          mul_le_mul_of_nonneg_left hθ_le_lin hpos.le
      _ = 1 := mul_one_div_cancel hpos.ne'
  obtain ⟨hint, hle⟩ := hmgf θ hθ_dom
  have hquad_term : C₁ * F * θ ^ 2 ≤ θ * t / 2 := by
    have hCF : 0 < 2 * C₁ * F := by positivity
    have h1 : 2 * C₁ * F * θ ≤ t := by
      calc 2 * C₁ * F * θ ≤ 2 * C₁ * F * (t / (2 * C₁ * F)) :=
            mul_le_mul_of_nonneg_left hθ_le_quad hCF.le
        _ = t := mul_div_cancel₀ t hCF.ne'
    nlinarith
  have hrate : c * min (t ^ 2 / F) (t / op) ≤ θ * t / 2 := by
    have hc_nonneg : 0 ≤ c := le_min (by positivity) (by positivity)
    rcases le_total (t / (2 * C₁ * F)) (1 / (C₂ * op)) with hcase | hcase
    · have hθ_eq : θ = t / (2 * C₁ * F) := min_eq_left hcase
      have hc1 : c ≤ 1 / (4 * C₁) := min_le_left _ _
      have hm1 : min (t ^ 2 / F) (t / op) ≤ t ^ 2 / F := min_le_left _ _
      calc c * min (t ^ 2 / F) (t / op)
          ≤ (1 / (4 * C₁)) * (t ^ 2 / F) :=
            mul_le_mul hc1 hm1 (le_min (by positivity) (by positivity)) (by positivity)
        _ = (t / (2 * C₁ * F)) * t / 2 := by field_simp; ring
        _ = θ * t / 2 := by rw [hθ_eq]
    · have hθ_eq : θ = 1 / (C₂ * op) := min_eq_right hcase
      have hc2 : c ≤ 1 / (2 * C₂) := min_le_right _ _
      have hm2 : min (t ^ 2 / F) (t / op) ≤ t / op := min_le_right _ _
      calc c * min (t ^ 2 / F) (t / op)
          ≤ (1 / (2 * C₂)) * (t / op) :=
            mul_le_mul hc2 hm2 (le_min (by positivity) (by positivity)) (by positivity)
        _ = (1 / (C₂ * op)) * t / 2 := by field_simp
        _ = θ * t / 2 := by rw [hθ_eq]
  calc P.real {ω | t < Y ω}
      ≤ P.real {ω | t ≤ Y ω} := measureReal_mono fun ω (hω : t < Y ω) ↦ hω.le
    _ ≤ exp (-θ * t) * mgf Y P θ := measure_ge_le_exp_mul_mgf t hθ_nonneg hint
    _ ≤ exp (-θ * t) * exp (C₁ * F * θ ^ 2) :=
          mul_le_mul_of_nonneg_left hle (exp_pos _).le
    _ = exp (-θ * t + C₁ * F * θ ^ 2) := (exp_add _ _).symm
    _ ≤ exp (-c * min (t ^ 2 / F) (t / op)) := by
          apply exp_le_exp.2
          linarith

/-- **Two-sided sub-exponential Chernoff bound.** Under the same symmetric MGF hypothesis as
`measureReal_gt_le_exp_min_of_mgf_le`,
`P.real {ω | t < |Y ω|} ≤ 2 * exp (-min (1 / (4 * C₁)) (1 / (2 * C₂)) * min (t ^ 2 / F) (t / op))`.
-/
theorem measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ} {C₁ C₂ F op : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hF : 0 ≤ F) (hop : 0 ≤ op)
    (hmgf : ∀ θ : ℝ, C₂ * op * |θ| ≤ 1 →
      Integrable (fun ω ↦ exp (θ * Y ω)) P ∧ mgf Y P θ ≤ exp (C₁ * F * θ ^ 2))
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |Y ω|} ≤
      2 * exp (-min (1 / (4 * C₁)) (1 / (2 * C₂)) * min (t ^ 2 / F) (t / op)) := by
  have hmgf_neg : ∀ θ : ℝ, C₂ * op * |θ| ≤ 1 →
      Integrable (fun ω ↦ exp (θ * (-Y) ω)) P ∧ mgf (-Y) P θ ≤ exp (C₁ * F * θ ^ 2) := by
    intro θ hθ
    have hθ' : C₂ * op * |-θ| ≤ 1 := by simpa only [abs_neg] using hθ
    obtain ⟨hint, hle⟩ := hmgf (-θ) hθ'
    refine ⟨?_, ?_⟩
    · exact hint.congr
        (Filter.Eventually.of_forall fun ω ↦ by simp [Pi.neg_apply, mul_neg, neg_mul])
    · rw [mgf_neg]
      exact hle.trans_eq (by ring_nf)
  have hsub : {ω | t < |Y ω|} ⊆ {ω | t < Y ω} ∪ {ω | t < (-Y) ω} := by
    intro ω hω
    simpa only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply, lt_abs] using hω
  have hpos := measureReal_gt_le_exp_min_of_mgf_le hC₁ hC₂ hF hop hmgf ht
  have hneg := measureReal_gt_le_exp_min_of_mgf_le hC₁ hC₂ hF hop hmgf_neg ht
  calc P.real {ω | t < |Y ω|}
      ≤ P.real ({ω | t < Y ω} ∪ {ω | t < (-Y) ω}) := measureReal_mono hsub
    _ ≤ P.real {ω | t < Y ω} + P.real {ω | t < (-Y) ω} := measureReal_union_le _ _
    _ ≤ _ := by linarith

end SubExponentialChernoff

end ProbabilityTheory
