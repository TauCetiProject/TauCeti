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

We develop squared-variable exponential moment bounds for `ProbabilityTheory.HasSubgaussianMGF`
(`integrable_exp_mul_sq`, `integral_exp_mul_sq_le`, `mgf_sq_sub_integral_le`), AM-GM/GM MGF bounds
for sums without independence, sub-exponential Chernoff tail bounds with dual quadratic/linear
rates, and complex directional sub-Gaussianity (Vershynin 2018, §2.5–2.7; Rudelson–Vershynin 2013).
-/

public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

section CombineMGF

/-- **AM-GM bound for the moment-generating function of a sum** without independence. -/
theorem mgf_add_le_of_mgf_two_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} {θ M₁ M₂ : ℝ} (hX_int : Integrable (fun ω ↦ exp (2 * θ * X ω)) μ)
    (hY_int : Integrable (fun ω ↦ exp (2 * θ * Y ω)) μ)
    (hX_le : mgf X μ (2 * θ) ≤ M₁) (hY_le : mgf Y μ (2 * θ) ≤ M₂) :
    Integrable (fun ω ↦ exp (θ * (X ω + Y ω))) μ ∧
      mgf (fun ω ↦ X ω + Y ω) μ θ ≤ (M₁ + M₂) / 2 := by
  have hsqrt : (fun ω ↦ exp (θ * (X ω + Y ω))) =
      fun ω ↦ Real.sqrt (exp (2 * θ * X ω) * exp (2 * θ * Y ω)) := funext fun ω ↦ by
    rw [show exp (2 * θ * X ω) * exp (2 * θ * Y ω) = exp (θ * (X ω + Y ω)) ^ 2 by
      rw [sq, ← exp_add, ← exp_add]; ring_nf, Real.sqrt_sq (exp_pos _).le]
  have hpt (ω : Ω) : exp (θ * (X ω + Y ω)) ≤ (exp (2 * θ * X ω) + exp (2 * θ * Y ω)) / 2 := by
    rw [mul_add, exp_add, show exp (2 * θ * X ω) = exp (θ * X ω) ^ 2 by rw [sq, ← exp_add]; ring_nf,
      show exp (2 * θ * Y ω) = exp (θ * Y ω) ^ 2 by rw [sq, ← exp_add]; ring_nf]
    linarith [two_mul_le_add_sq (exp (θ * X ω)) (exp (θ * Y ω))]
  have hdom : Integrable (fun ω ↦ (exp (2 * θ * X ω) + exp (2 * θ * Y ω)) / 2) μ :=
    (hX_int.add hY_int).div_const 2
  have hint : Integrable (fun ω ↦ exp (θ * (X ω + Y ω))) μ :=
    hdom.mono' (hsqrt ▸ continuous_sqrt.comp_aestronglyMeasurable (hX_int.1.mul hY_int.1))
      (.of_forall fun ω ↦ by rw [Real.norm_of_nonneg (exp_pos _).le]; exact hpt ω)
  refine ⟨hint, (integral_mono hint hdom hpt).trans ?_⟩
  rw [integral_div, integral_add hX_int hY_int]
  change (mgf X μ (2 * θ) + mgf Y μ (2 * θ)) / 2 ≤ (M₁ + M₂) / 2; linarith

/-- **Geometric-mean bound for the moment-generating function of a sum** without independence. -/
theorem mgf_add_le_exp_half_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} {θ a b : ℝ} (hX_int : Integrable (fun ω ↦ exp (2 * θ * X ω)) μ)
    (hY_int : Integrable (fun ω ↦ exp (2 * θ * Y ω)) μ)
    (hX_le : mgf X μ (2 * θ) ≤ exp a) (hY_le : mgf Y μ (2 * θ) ≤ exp b) :
    Integrable (fun ω ↦ exp (θ * (X ω + Y ω))) μ ∧
      mgf (fun ω ↦ X ω + Y ω) μ θ ≤ exp ((a + b) / 2) := by
  have hint := (mgf_add_le_of_mgf_two_mul_le hX_int hY_int hX_le hY_le).1
  have hpt (ω : Ω) : exp (θ * (X ω + Y ω)) ≤ exp ((a + b) / 2) / 2 *
      (exp (-a) * exp (2 * θ * X ω) + exp (-b) * exp (2 * θ * Y ω)) := by
    have hsq (z c : ℝ) : exp (-c) * exp (2 * θ * z) = exp (θ * z - c / 2) ^ 2 := by
      rw [sq, ← exp_add, ← exp_add]; ring_nf
    rw [show exp (θ * (X ω + Y ω)) = exp ((a + b) / 2) *
        (exp (θ * X ω - a / 2) * exp (θ * Y ω - b / 2)) by rw [← exp_add, ← exp_add]; ring_nf,
      hsq (X ω) a, hsq (Y ω) b]
    nlinarith [two_mul_le_add_sq (exp (θ * X ω - a / 2)) (exp (θ * Y ω - b / 2)),
      exp_pos ((a + b) / 2)]
  have hdom : Integrable (fun ω ↦ exp ((a + b) / 2) / 2 *
      (exp (-a) * exp (2 * θ * X ω) + exp (-b) * exp (2 * θ * Y ω))) μ :=
    ((hX_int.const_mul (exp (-a))).add (hY_int.const_mul (exp (-b)))).const_mul _
  have h1 {Z : Ω → ℝ} {c : ℝ} (hZ : mgf Z μ (2 * θ) ≤ exp c) : exp (-c) * mgf Z μ (2 * θ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hZ (exp_pos _).le).trans_eq (by rw [← exp_add]; simp)
  refine ⟨hint, (integral_mono hint hdom hpt).trans ?_⟩
  rw [integral_const_mul, integral_add (hX_int.const_mul _) (hY_int.const_mul _),
    integral_const_mul, integral_const_mul]
  change exp ((a + b) / 2) / 2 * (exp (-a) * mgf X μ (2 * θ) + exp (-b) * mgf Y μ (2 * θ)) ≤ _
  nlinarith [h1 hX_le, h1 hY_le, exp_pos ((a + b) / 2)]

end CombineMGF

/-- A random variable with centred Gaussian law `gaussianReal 0 v` is `v`-sub-Gaussian. -/
theorem HasLaw.hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ := by
  rw [← HasSubgaussianMGF.id_map_iff hX.aemeasurable, hX.map_eq]
  exact ⟨integrable_exp_mul_gaussianReal, fun t ↦ by simp [mgf_id_gaussianReal]⟩

private theorem mgf_sub_integral_le_of_nonneg_exp_le_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY_meas : AEMeasurable Y μ)
    (hY_nonneg : 0 ≤ᵐ[μ] Y) {B : ℝ} (hB : 0 < B)
    (hY_int_exp : Integrable (fun ω ↦ exp (Y ω / B)) μ)
    (hY_exp : ∫ ω, exp (Y ω / B) ∂μ ≤ 2) {θ : ℝ} (hθ : B * |θ| ≤ 1 / 2) :
    Integrable (fun ω ↦ exp (θ * (Y ω - μ[Y]))) μ ∧
      mgf (fun ω ↦ Y ω - μ[Y]) μ θ ≤ exp (24 * B ^ 2 * θ ^ 2) := by
  have hY_int : Integrable Y μ :=
    (hY_int_exp.const_mul B).mono' hY_meas.aestronglyMeasurable <| by
      filter_upwards [hY_nonneg] with ω hω
      have h2 := mul_le_mul_of_nonneg_left
        (by linarith [add_one_le_exp (Y ω / B)] : Y ω / B ≤ exp (Y ω / B)) hB.le
      rw [Real.norm_of_nonneg hω]; rwa [mul_div_cancel₀ _ hB.ne'] at h2
  let m : ℝ := μ[Y]
  have hm_nonneg : 0 ≤ m := integral_nonneg_of_ae hY_nonneg
  have hm_le : m ≤ B := by
    have hf : Integrable (fun ω ↦ 1 + Y ω / B) μ := (integrable_const 1).add (hY_int.div_const B)
    have h1 := integral_mono hf hY_int_exp fun ω ↦ by linarith [add_one_le_exp (Y ω / B)]
    rw [integral_add (integrable_const 1) (hY_int.div_const B), integral_const, probReal_univ,
      one_smul, integral_div] at h1
    exact (div_le_one hB).mp (by linarith)
  let Z : Ω → ℝ := fun ω ↦ Y ω - m
  have hZ_int : Integrable Z μ := hY_int.sub (integrable_const m)
  have hZ_mean : ∫ ω, Z ω ∂μ = 0 := by
    rw [integral_sub hY_int (integrable_const m), integral_const, probReal_univ, one_smul, sub_self]
  have hexp_half_le : exp (1 / 2 : ℝ) ≤ 3 :=
    (exp_le_exp.2 (by norm_num)).trans (Real.exp_one_lt_d9.le.trans (by norm_num))
  have hpt : ∀ᵐ ω ∂μ, exp (θ * Z ω) ≤ 1 + θ * Z ω + 12 * B ^ 2 * θ ^ 2 * exp (Y ω / B) := by
    filter_upwards [hY_nonneg] with ω hω
    let u : ℝ := Y ω / B; have hu0 : 0 ≤ u := div_nonneg hω hB.le
    have hY_eq : Y ω = B * u := (mul_div_cancel₀ _ hB.ne').symm
    have hZ_abs : |Z ω| ≤ B * (u + 1) := abs_le.2 ⟨by dsimp [Z]; nlinarith, by dsimp [Z]; nlinarith⟩
    have hθZ : |θ * Z ω| ≤ u / 2 + 1 / 2 := (abs_mul θ (Z ω)) ▸
      (mul_le_mul_of_nonneg_left hZ_abs (abs_nonneg θ)).trans
        (by linarith [mul_le_mul_of_nonneg_right hθ (by positivity : 0 ≤ u + 1)])
    have hu_quad : (u + 1) ^ 2 ≤ 8 * exp (u / 2) := by
      linarith [show (u + 1) ^ 2 ≤ 8 * (1 + u / 2 + (u / 2) ^ 2 / 2) by nlinarith,
        Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ u / 2)]
    have hu_exp : (u + 1) ^ 2 * exp (u / 2 + 1 / 2) ≤ 24 * exp u := by
      have hmul := mul_le_mul hu_quad (mul_le_mul_of_nonneg_left hexp_half_le (exp_pos (u / 2)).le)
        (by positivity) (by positivity)
      rw [exp_add]; linarith [show exp (u / 2) * exp (u / 2) = exp u by rw [← exp_add]; ring_nf]
    have hZ_sq : (θ * Z ω) ^ 2 ≤ B ^ 2 * θ ^ 2 * (u + 1) ^ 2 := by
      rw [show (θ * Z ω) ^ 2 = θ ^ 2 * |Z ω| ^ 2 by rw [sq_abs]; ring,
        show B ^ 2 * θ ^ 2 * (u + 1) ^ 2 = θ ^ 2 * (B * (u + 1)) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hZ_abs 2) (sq_nonneg θ)
    have h1 : (θ * Z ω) ^ 2 / 2 * exp |θ * Z ω| ≤
        (B ^ 2 * θ ^ 2 / 2) * ((u + 1) ^ 2 * exp (u / 2 + 1 / 2)) := by
      rw [show (B ^ 2 * θ ^ 2 / 2) * ((u + 1) ^ 2 * exp (u / 2 + 1 / 2)) =
        (B ^ 2 * θ ^ 2 * (u + 1) ^ 2 / 2) * exp (u / 2 + 1 / 2) by ring]
      exact mul_le_mul (by linarith) (exp_le_exp.2 hθZ) (exp_pos _).le (by positivity)
    exact (Real.exp_le_one_add_add_sq_div_two_mul_exp_abs (θ * Z ω)).trans
      (by linarith [mul_le_mul_of_nonneg_left hu_exp (by positivity : 0 ≤ B ^ 2 * θ ^ 2 / 2)])
  have hf1 : Integrable (fun ω ↦ 1 + θ * Z ω) μ := (integrable_const 1).add (hZ_int.const_mul θ)
  have hdom : Integrable (fun ω ↦ 1 + θ * Z ω + 12 * B ^ 2 * θ ^ 2 * exp (Y ω / B)) μ :=
    hf1.add (hY_int_exp.const_mul (12 * B ^ 2 * θ ^ 2))
  have hint : Integrable (fun ω ↦ exp (θ * Z ω)) μ :=
    hdom.mono' (Real.measurable_exp.comp_aemeasurable
      ((hY_meas.sub_const m).const_mul θ)).aestronglyMeasurable
      (hpt.mono fun _ hω ↦ by rwa [Real.norm_of_nonneg (exp_pos _).le])
  refine ⟨hint, (integral_mono_ae hint hdom hpt).trans ?_⟩
  rw [integral_add hf1 (hY_int_exp.const_mul _),
    integral_add (integrable_const 1) (hZ_int.const_mul θ), integral_const, probReal_univ, one_smul,
    integral_const_mul, integral_const_mul, hZ_mean, mul_zero, add_zero]
  exact (show 1 + 12 * B ^ 2 * θ ^ 2 * ∫ ω, exp (Y ω / B) ∂μ ≤ 1 + 24 * B ^ 2 * θ ^ 2 by
      nlinarith [sq_nonneg (B * θ)]).trans (by linarith [add_one_le_exp (24 * B ^ 2 * θ ^ 2)])

namespace HasSubgaussianMGF

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- Monotonicity of `HasSubgaussianMGF` in the variance proxy. -/
theorem mono {c₁ c₂ : ℝ≥0} (h : HasSubgaussianMGF X c₁ μ) (hle : c₁ ≤ c₂) :
    HasSubgaussianMGF X c₂ μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans <| by gcongr

/-- Under a zero or probability measure, every sub-Gaussian random variable has expectation zero. -/
theorem integral_eq_zero [IsZeroOrProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ) :
    μ[X] = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hprob
  · simp
  · let m : ℝ := μ[X]
    have hquad (t : ℝ) : t * m ≤ (c : ℝ) * t ^ 2 / 2 := by
      have hmul : Integrable (fun ω ↦ t * (X ω - m)) μ :=
        (h.integrable.sub (integrable_const m)).const_mul t
      have hf : Integrable (fun ω ↦ 1 + t * (X ω - m)) μ := (integrable_const 1).add hmul
      have hg : Integrable (fun ω ↦ exp (-t * m) * exp (t * X ω)) μ :=
        (h.integrable_exp_mul t).const_mul (exp (-t * m))
      have hpt (ω : Ω) : 1 + t * (X ω - m) ≤ exp (-t * m) * exp (t * X ω) := by
        rw [← exp_add, show -t * m + t * X ω = t * (X ω - m) by ring]
        linarith [add_one_le_exp (t * (X ω - m))]
      have hlhs : ∫ ω, (1 + t * (X ω - m)) ∂μ = 1 := by
        rw [integral_add (integrable_const 1) hmul, integral_const_mul,
          integral_sub h.integrable (integrable_const m)]
        simp [m, probReal_univ]
      have hrhs : ∫ ω, exp (-t * m) * exp (t * X ω) ∂μ ≤ exp (-t * m + (c : ℝ) * t ^ 2 / 2) := by
        rw [integral_const_mul, exp_add]
        exact mul_le_mul_of_nonneg_left (h.mgf_le t) (exp_pos _).le
      linarith [Real.one_le_exp_iff.mp (hlhs ▸ (integral_mono hf hg hpt).trans hrhs)]
    have hc1 : (c : ℝ) + 1 ≠ 0 := by positivity
    have hstep := mul_le_mul_of_nonneg_left (hquad (m / ((c : ℝ) + 1)))
      (by positivity : (0 : ℝ) ≤ 2 * ((c : ℝ) + 1) ^ 2)
    rw [show 2 * ((c : ℝ) + 1) ^ 2 * (m / ((c : ℝ) + 1) * m) = 2 * ((c : ℝ) + 1) * m ^ 2 by
        field_simp,
      show 2 * ((c : ℝ) + 1) ^ 2 * ((c : ℝ) * (m / ((c : ℝ) + 1)) ^ 2 / 2) = (c : ℝ) * m ^ 2 by
        field_simp] at hstep
    have h0 : ((c : ℝ) + 2) * m ^ 2 = 0 := le_antisymm (by linarith) (by positivity)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h0).resolve_left (by positivity))

private theorem lintegral_ofReal_exp_mul_sq_le (h : HasSubgaussianMGF X c μ) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : 2 * (c : ℝ) * s < 1) :
    ∫⁻ ω, ENNReal.ofReal (exp (s * X ω ^ 2)) ∂μ ≤
      ENNReal.ofReal ((1 - 2 * (c : ℝ) * s) ^ (-1 / 2 : ℝ)) := by
  have : IsFiniteMeasure μ := TauCeti.isFiniteMeasure_of_zero_mem_integrableExpSet (X := X)
    (by simpa [integrableExpSet] using h.integrable_exp_mul 0)
  let X₀ : Ω → ℝ := h.aemeasurable.mk X
  have hX₀_meas : Measurable X₀ := h.aemeasurable.measurable_mk
  have hX₀_eq : X =ᵐ[μ] X₀ := h.aemeasurable.ae_eq_mk; have h₀ := h.congr hX₀_eq
  let γ : Measure ℝ := gaussianReal 0 1
  let F : Ω × ℝ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (exp (Real.sqrt (2 * s) * X₀ p.1 * p.2))
  have hF_meas : Measurable F := by fun_prop
  have hsq : Real.sqrt (2 * s) ^ 2 = 2 * s := Real.sq_sqrt (by positivity)
  have hleft (ω : Ω) : ∫⁻ g, F (ω, g) ∂γ = ENNReal.ofReal (exp (s * X₀ ω ^ 2)) := by
    let u : ℝ := Real.sqrt (2 * s) * X₀ ω
    rw [show ∫⁻ g, F (ω, g) ∂γ = ENNReal.ofReal (mgf (fun g ↦ g) γ u) by
      simpa [F, u, mgf] using (ofReal_integral_eq_lintegral_ofReal
        (integrable_exp_mul_gaussianReal u) (.of_forall fun _ ↦ (exp_pos _).le)).symm,
      mgf_fun_id_gaussianReal]
    simp only [zero_mul, zero_add, NNReal.coe_one, one_mul, u]; congr 2; rw [mul_pow, hsq]; ring
  have hright (g : ℝ) : ∫⁻ ω, F (ω, g) ∂μ ≤ ENNReal.ofReal (exp (((c : ℝ) * s) * g ^ 2)) := by
    let t : ℝ := Real.sqrt (2 * s) * g
    rw [show (fun ω ↦ F (ω, g)) = fun ω ↦ ENNReal.ofReal (exp (t * X₀ ω)) from
        funext fun _ ↦ by dsimp [F, t]; ring_nf,
      ← ofReal_integral_eq_lintegral_ofReal (h₀.integrable_exp_mul t)
        (.of_forall fun _ ↦ (exp_pos _).le), ← mgf]
    refine ENNReal.ofReal_le_ofReal ((h₀.mgf_le t).trans_eq ?_)
    congr 1; dsimp [t]; rw [mul_pow, hsq]; ring
  have hw : 2 * (1 : ℝ) * ((c : ℝ) * s) < 1 := by linarith
  have hg_int : Integrable (fun g : ℝ ↦ exp (((c : ℝ) * s) * g ^ 2)) γ := by
    simpa [integrableExpSet] using
      (TauCeti.Probability.mem_integrableExpSet_mul_sq_gaussianReal_iff ((c : ℝ) * s) 1).2 hw
  calc ∫⁻ ω, ENNReal.ofReal (exp (s * X ω ^ 2)) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (exp (s * X₀ ω ^ 2)) ∂μ :=
          lintegral_congr_ae (hX₀_eq.mono fun _ hω ↦ by dsimp only; rw [hω])
    _ = ∫⁻ g, ∫⁻ ω, F (ω, g) ∂μ ∂γ := by
          simp_rw [← hleft]
          exact (lintegral_prod F hF_meas.aemeasurable).symm.trans (lintegral_prod_symm' F hF_meas)
    _ ≤ ∫⁻ g, ENNReal.ofReal (exp (((c : ℝ) * s) * g ^ 2)) ∂γ := lintegral_mono hright
    _ = ENNReal.ofReal ((1 - 2 * (c : ℝ) * s) ^ (-1 / 2 : ℝ)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hg_int (.of_forall fun _ ↦ (exp_pos _).le)]
          exact congrArg ENNReal.ofReal
            (by simpa [γ, mgf, mul_assoc] using TauCeti.Probability.mgf_mul_sq_gaussianReal hw)

/-- For `c`-sub-Gaussian `X`, `exp (s * X ^ 2)` is integrable whenever `2 * c * s < 1`. -/
theorem integrable_exp_mul_sq (h : HasSubgaussianMGF X c μ) {s : ℝ} (hs : 2 * (c : ℝ) * s < 1) :
    Integrable (fun ω ↦ exp (s * X ω ^ 2)) μ := by
  have : IsFiniteMeasure μ := TauCeti.isFiniteMeasure_of_zero_mem_integrableExpSet (X := X)
    (by simpa [integrableExpSet] using h.integrable_exp_mul 0)
  have haesm : AEStronglyMeasurable (fun ω ↦ exp (s * X ω ^ 2)) μ :=
    (Real.measurable_exp.comp_aemeasurable
      ((h.aemeasurable.pow_const 2).const_mul s)).aestronglyMeasurable
  by_cases hs0 : 0 ≤ s
  · refine ⟨haesm, ?_⟩
    rw [hasFiniteIntegral_def, show (fun ω ↦ ‖exp (s * X ω ^ 2)‖ₑ) = fun ω ↦
      ENNReal.ofReal (exp (s * X ω ^ 2)) from funext fun _ ↦ Real.enorm_eq_ofReal (exp_pos _).le]
    exact (h.lintegral_ofReal_exp_mul_sq_le hs0 hs).trans_lt ENNReal.ofReal_lt_top
  · refine Integrable.of_bound haesm 1 (.of_forall fun _ ↦ ?_)
    rw [Real.norm_of_nonneg (exp_pos _).le, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs0) (sq_nonneg _)

/-- **Gaussian-comparison bound for squared sub-Gaussian exponential moments.** -/
theorem integral_exp_mul_sq_le (h : HasSubgaussianMGF X c μ) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : 2 * (c : ℝ) * s < 1) :
    ∫ ω, exp (s * X ω ^ 2) ∂μ ≤ (1 - 2 * (c : ℝ) * s) ^ (-1 / 2 : ℝ) := by
  rw [← ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg (by linarith) _),
    ofReal_integral_eq_lintegral_ofReal (h.integrable_exp_mul_sq hs)
      (.of_forall fun _ ↦ (exp_pos _).le)]
  exact h.lintegral_ofReal_exp_mul_sq_le hs0 hs

/-- **Sub-exponential MGF bound for a centred squared sub-Gaussian variable.** -/
theorem mgf_sq_sub_integral_le [IsZeroOrProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ)
    {θ : ℝ} (hθ : (c : ℝ) * |θ| ≤ 1 / 8) :
    Integrable (fun ω ↦ exp (θ * (X ω ^ 2 - μ[fun ω' ↦ X ω' ^ 2]))) μ ∧
      mgf (fun ω ↦ X ω ^ 2 - μ[fun ω' ↦ X ω' ^ 2]) μ θ ≤ exp (384 * (c : ℝ) ^ 2 * θ ^ 2) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hprob
  · exact ⟨integrable_zero_measure, by simp [mgf, (exp_pos _).le]⟩
  · by_cases hc : c = 0
    · subst hc; have hX0 : ∀ᵐ ω ∂μ, X ω = 0 := h.ae_eq_zero_of_hasSubgaussianMGF_zero
      have hm0 : μ[fun ω' ↦ X ω' ^ 2] = 0 := by
        rw [integral_congr_ae (hX0.mono fun _ hω ↦ show _ ^ 2 = (0 : ℝ) by rw [hω]; ring),
          integral_zero]
      have hexp1 : (fun ω ↦ exp (θ * (X ω ^ 2 - μ[fun ω' ↦ X ω' ^ 2]))) =ᵐ[μ] fun _ ↦ 1 :=
        hX0.mono fun _ hω ↦ by dsimp only; rw [hω, hm0]; simp
      refine ⟨(integrable_const 1).congr hexp1.symm, ?_⟩
      rw [mgf, integral_congr_ae hexp1, integral_const, probReal_univ, one_smul]
      exact Real.one_le_exp (by positivity)
    · have hc_pos : 0 < (c : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
      let B : ℝ := 4 * (c : ℝ); have hB : 0 < B := by positivity
      have hs_lt : 2 * (c : ℝ) * B⁻¹ < 1 := by dsimp [B]; field_simp; norm_num
      have hexp_int : Integrable (fun ω ↦ exp (X ω ^ 2 / B)) μ := by
        simpa [div_eq_inv_mul] using h.integrable_exp_mul_sq hs_lt
      have hexp_le : ∫ ω, exp (X ω ^ 2 / B) ∂μ ≤ 2 := by
        have h1 := h.integral_exp_mul_sq_le (inv_nonneg.2 hB.le) hs_lt
        rw [show 1 - 2 * (c : ℝ) * B⁻¹ = 1 / 2 by dsimp [B]; field_simp; norm_num] at h1
        have hrpow : (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) ≤ 2 := by
          rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg (by norm_num),
            ← Real.inv_rpow (by norm_num), show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
          exact (Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans_eq (Real.rpow_one 2)
        simpa [div_eq_inv_mul] using h1.trans hrpow
      obtain ⟨hint, hmgf⟩ := mgf_sub_integral_le_of_nonneg_exp_le_two (θ := θ)
        (h.aemeasurable.pow_const 2) (.of_forall fun _ ↦ sq_nonneg _) hB hexp_int hexp_le
        (by dsimp [B]; linarith)
      exact ⟨hint, hmgf.trans_eq (by dsimp [B]; ring_nf)⟩

end HasSubgaussianMGF

section ComplexSubGaussian

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → ℂ} {K : ℝ≥0}

/-- Real-part projection of a directionally `K`-sub-Gaussian complex random variable. -/
theorem hasSubgaussianMGF_re_of_star_mul
    (hZ : ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ) :
    HasSubgaussianMGF (fun ω ↦ (Z ω).re) K μ := by simpa using hZ 1

/-- Imaginary-part projection of a directionally `K`-sub-Gaussian complex random variable. -/
theorem hasSubgaussianMGF_im_of_star_mul
    (hZ : ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ) :
    HasSubgaussianMGF (fun ω ↦ (Z ω).im) K μ := by
  have hre : (fun ω ↦ (star Complex.I * Z ω).re) = fun ω ↦ (Z ω).im :=
    funext fun _ ↦ by simp [Complex.mul_re]
  simpa [hre] using hZ Complex.I

/-- Every directionally sub-Gaussian complex random variable is Bochner integrable. -/
theorem integrable_of_hasSubgaussianMGF_re_star_mul
    (hZ : ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ) :
    Integrable Z μ := by
  rw [show Z = fun ω ↦ ((Z ω).re : ℂ) + ((Z ω).im : ℂ) * Complex.I from
    funext fun ω ↦ (Complex.re_add_im (Z ω)).symm]
  exact (hasSubgaussianMGF_re_of_star_mul hZ).integrable.ofReal.add
    ((hasSubgaussianMGF_im_of_star_mul hZ).integrable.ofReal.mul_const Complex.I)

/-- Under a zero or probability measure, every directionally sub-Gaussian complex random variable
has expectation zero. -/
theorem integral_eq_zero_of_hasSubgaussianMGF_re_star_mul [IsZeroOrProbabilityMeasure μ]
    (hZ : ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ) :
    ∫ ω, Z ω ∂μ = 0 := by
  have hZ_int := integrable_of_hasSubgaussianMGF_re_star_mul hZ
  apply Complex.ext
  · simpa using (Complex.reCLM.integral_comp_comm hZ_int).symm.trans
      (hasSubgaussianMGF_re_of_star_mul hZ).integral_eq_zero
  · simpa using (Complex.imCLM.integral_comp_comm hZ_int).symm.trans
      (hasSubgaussianMGF_im_of_star_mul hZ).integral_eq_zero

/-- **Sub-exponential MGF bound for the centred squared norm of a directionally `K`-sub-Gaussian
complex variable.** -/
theorem mgf_norm_sq_sub_integral_le_of_hasSubgaussianMGF_re_star_mul [IsZeroOrProbabilityMeasure μ]
    (hZ : ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ)
    {θ : ℝ} (hθ : (K : ℝ) * |θ| ≤ 1 / 16) :
    Integrable (fun ω ↦ exp (θ * (‖Z ω‖ ^ 2 - μ[fun ω' ↦ ‖Z ω'‖ ^ 2]))) μ ∧
      mgf (fun ω ↦ ‖Z ω‖ ^ 2 - μ[fun ω' ↦ ‖Z ω'‖ ^ 2]) μ θ ≤ exp (1536 * (K : ℝ) ^ 2 * θ ^ 2) := by
  have hre := hasSubgaussianMGF_re_of_star_mul hZ
  have him := hasSubgaussianMGF_im_of_star_mul hZ
  have h2θ : (K : ℝ) * |2 * θ| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith
  obtain ⟨hre_int, hre_mgf⟩ := hre.mgf_sq_sub_integral_le h2θ
  obtain ⟨him_int, him_mgf⟩ := him.mgf_sq_sub_integral_le h2θ
  have hnorm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sq, sq]
  have hsplit (ω : Ω) : ‖Z ω‖ ^ 2 - μ[fun ω' ↦ ‖Z ω'‖ ^ 2] =
      ((Z ω).re ^ 2 - μ[fun ω' ↦ (Z ω').re ^ 2]) + ((Z ω).im ^ 2 - μ[fun ω' ↦ (Z ω').im ^ 2]) := by
    simp_rw [hnorm_sq]
    rw [integral_add (hre.memLp 2).integrable_sq (him.memLp 2).integrable_sq]; ring
  simp_rw [hsplit]
  obtain ⟨hint, hle⟩ := mgf_add_le_of_mgf_two_mul_le hre_int him_int hre_mgf him_mgf
  exact ⟨hint, hle.trans_eq (by
    rw [show 384 * (K : ℝ) ^ 2 * (2 * θ) ^ 2 = 1536 * (K : ℝ) ^ 2 * θ ^ 2 by ring]; ring)⟩

/-- **Hoeffding directional sub-Gaussianity for bounded mean-zero complex random variables.** -/
theorem hasSubgaussianMGF_re_star_mul_of_norm_le [IsProbabilityMeasure μ]
    (hZ_meas : AEMeasurable Z μ) {b : ℝ≥0} (hZ_norm : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ b)
    (hZ_mean : ∫ ω, Z ω ∂μ = 0) (u : ℂ) :
    HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * b ^ 2) μ := by
  have hZ_int : Integrable Z μ := Integrable.of_bound hZ_meas.aestronglyMeasurable b hZ_norm
  have hproj_meas : AEMeasurable (fun ω ↦ (star u * Z ω).re) μ :=
    Complex.continuous_re.measurable.comp_aemeasurable (hZ_meas.const_mul (star u))
  have hproj_Icc : ∀ᵐ ω ∂μ, (star u * Z ω).re ∈ Set.Icc (-(‖u‖ * (b : ℝ))) (‖u‖ * (b : ℝ)) :=
    hZ_norm.mono fun _ hω ↦ Set.mem_Icc.2 <| abs_le.1 <| (Complex.abs_re_le_norm _).trans <| by
      rw [norm_mul, norm_star]; exact mul_le_mul_of_nonneg_left hω (norm_nonneg u)
  have hproj_mean : ∫ ω, (star u * Z ω).re ∂μ = 0 := by
    simpa [integral_const_mul, hZ_mean] using
      Complex.reCLM.integral_comp_comm (hZ_int.const_mul (star u))
  have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hproj_meas hproj_Icc hproj_mean
  have hparam : (‖‖u‖ * (b : ℝ) - -(‖u‖ * (b : ℝ))‖₊ / 2) ^ 2 = ‖u‖₊ ^ 2 * b ^ 2 := by
    apply NNReal.coe_injective; push_cast
    rw [Real.norm_of_nonneg (by linarith [mul_nonneg (norm_nonneg u) b.coe_nonneg])]; ring
  rwa [hparam] at hsub

/-- Independent `K`-sub-Gaussian real and imaginary parts yield directional `K`-sub-Gaussianity. -/
theorem hasSubgaussianMGF_re_star_mul_of_indepFun_re_im
    (hre : HasSubgaussianMGF (fun ω ↦ (Z ω).re) K μ)
    (him : HasSubgaussianMGF (fun ω ↦ (Z ω).im) K μ)
    (hindep : IndepFun (fun ω ↦ (Z ω).re) (fun ω ↦ (Z ω).im) μ) (u : ℂ) :
    HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ := by
  rw [show (fun ω ↦ (star u * Z ω).re) = fun ω ↦ u.re * (Z ω).re + u.im * (Z ω).im from
    funext fun _ ↦ by simp [Complex.mul_re]]
  refine ((hre.const_mul u.re).add_of_indepFun (him.const_mul u.im)
    (hindep.comp (measurable_const_mul u.re) (measurable_const_mul u.im))).mono ?_
  rw [← NNReal.coe_le_coe]
  change u.re ^ 2 * (K : ℝ) + u.im ^ 2 * (K : ℝ) ≤ ↑(‖u‖₊ ^ 2 * K)
  push_cast; rw [Complex.sq_norm, Complex.normSq_apply]; exact le_of_eq (by ring)

end ComplexSubGaussian

section SubExponentialChernoff

/-- **One-sided sub-exponential Chernoff bound.** -/
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
  · rw [show min (t ^ 2 / (0 : ℝ)) (t / op) = 0 by simp [div_nonneg ht hop], mul_zero, exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  rcases hop.eq_or_lt with rfl | hop_pos
  · rw [show min (t ^ 2 / F) (t / (0 : ℝ)) = 0 by simp [div_nonneg (sq_nonneg t) hF_pos.le],
      mul_zero, exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  let θ : ℝ := min (t / (2 * C₁ * F)) (1 / (C₂ * op))
  have hθ0 : 0 ≤ θ := le_min (by positivity) (by positivity)
  have hpos : 0 < C₂ * op := mul_pos hC₂ hop_pos
  obtain ⟨hint, hle⟩ := hmgf θ (by
    rw [abs_of_nonneg hθ0]
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hpos.le).trans_eq
      (mul_one_div_cancel hpos.ne'))
  have hCF : 0 < 2 * C₁ * F := by positivity
  have hquad : C₁ * F * θ ^ 2 ≤ θ * t / 2 := by
    nlinarith [(mul_le_mul_of_nonneg_left (min_le_left _ _ : θ ≤ _) hCF.le).trans_eq
      (mul_div_cancel₀ t hCF.ne')]
  have hrate : c * min (t ^ 2 / F) (t / op) ≤ θ * t / 2 := by
    rcases le_total (t / (2 * C₁ * F)) (1 / (C₂ * op)) with hcase | hcase
    · rw [show θ = t / (2 * C₁ * F) from min_eq_left hcase]
      exact (mul_le_mul (min_le_left _ _) (min_le_left _ _)
        (le_min (by positivity) (by positivity)) (by positivity)).trans_eq (by field_simp; ring)
    · rw [show θ = 1 / (C₂ * op) from min_eq_right hcase]
      exact (mul_le_mul (min_le_right _ _) (min_le_right _ _)
        (le_min (by positivity) (by positivity)) (by positivity)).trans_eq (by field_simp)
  have hsub : {ω | t < Y ω} ⊆ {ω | t ≤ Y ω} := fun _ (hω : t < _) ↦ hω.le
  exact ((measureReal_mono hsub).trans (measure_ge_le_exp_mul_mgf t hθ0 hint)).trans
    ((mul_le_mul_of_nonneg_left hle (exp_pos _).le).trans
      ((exp_add _ _).symm.trans_le (exp_le_exp.2 (by linarith))))

/-- **Two-sided sub-exponential Chernoff bound.** -/
theorem measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ} {C₁ C₂ F op : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hF : 0 ≤ F) (hop : 0 ≤ op)
    (hmgf : ∀ θ : ℝ, C₂ * op * |θ| ≤ 1 →
      Integrable (fun ω ↦ exp (θ * Y ω)) P ∧ mgf Y P θ ≤ exp (C₁ * F * θ ^ 2))
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |Y ω|} ≤
      2 * exp (-min (1 / (4 * C₁)) (1 / (2 * C₂)) * min (t ^ 2 / F) (t / op)) := by
  have hmgf_neg (θ : ℝ) (hθ : C₂ * op * |θ| ≤ 1) :
      Integrable (fun ω ↦ exp (θ * (-Y) ω)) P ∧ mgf (-Y) P θ ≤ exp (C₁ * F * θ ^ 2) := by
    obtain ⟨hint, hle⟩ := hmgf (-θ) (by simpa only [abs_neg] using hθ)
    exact ⟨hint.congr (.of_forall fun _ ↦ by simp [Pi.neg_apply, mul_neg, neg_mul]),
      by rw [mgf_neg]; exact hle.trans_eq (by ring_nf)⟩
  have hsub : {ω | t < |Y ω|} ⊆ {ω | t < Y ω} ∪ {ω | t < (-Y) ω} := fun _ hω ↦ by
    simpa only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply, lt_abs] using hω
  have hpos := measureReal_gt_le_exp_min_of_mgf_le hC₁ hC₂ hF hop hmgf ht
  have hneg := measureReal_gt_le_exp_min_of_mgf_le hC₁ hC₂ hF hop hmgf_neg ht
  exact (measureReal_mono hsub).trans <| (measureReal_union_le _ _).trans (by linarith)

end SubExponentialChernoff

end ProbabilityTheory
