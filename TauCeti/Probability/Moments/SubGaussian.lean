/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Probability.Distributions.Gaussian.ChiSquared
import TauCeti.Probability.Moments.Basic

/-!
# Squared, linear, and directional exponential moments of sub-Gaussian random variables

We develop squared-variable exponential moment bounds for `ProbabilityTheory.HasSubgaussianMGF`
(`integrable_exp_mul_sq`, `integral_exp_mul_sq_le`, `mgf_sq_sub_integral_le`), complex directional
sub-Gaussianity, and dot-product sub-Gaussian bounds for independent real and complex vectors
(Vershynin 2018, §2.5–2.7; Rudelson–Vershynin 2013).
-/

public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- A random variable with centred Gaussian law `gaussianReal 0 v` is `v`-sub-Gaussian. -/
theorem HasLaw.hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ := by
  rw [← HasSubgaussianMGF.id_map_iff hX.aemeasurable, hX.map_eq]
  exact ⟨integrable_exp_mul_gaussianReal, fun t ↦ by simp [mgf_id_gaussianReal]⟩

namespace HasSubgaussianMGF

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- Monotonicity of `HasSubgaussianMGF` in the variance proxy. -/
theorem mono {c₁ c₂ : ℝ≥0} (h : HasSubgaussianMGF X c₁ μ) (hle : c₁ ≤ c₂) :
    HasSubgaussianMGF X c₂ μ :=
  ⟨h.integrable_exp_mul, fun t ↦ (h.mgf_le t).trans <| by gcongr⟩

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
          integral_sub h.integrable (integrable_const m)]; simp [m, probReal_univ]
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
    rw [show ∫⁻ g, F (ω, g) ∂γ = ENNReal.ofReal (mgf (fun g ↦ g) γ u) from
      (ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal u)
        (.of_forall fun _ ↦ (exp_pos _).le)).symm, mgf_fun_id_gaussianReal]
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
          exact (Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)).trans_eq (rpow_one 2)
        simpa [div_eq_inv_mul] using h1.trans hrpow
      obtain ⟨hint, hmgf⟩ := TauCeti.mgf_sub_integral_le_of_nonneg_exp_le_two (θ := θ)
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
  simpa [show (fun ω ↦ (star Complex.I * Z ω).re) = fun ω ↦ (Z ω).im from
    funext fun _ ↦ by simp [Complex.mul_re]] using hZ Complex.I

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
  have hre := hasSubgaussianMGF_re_of_star_mul hZ; have him := hasSubgaussianMGF_im_of_star_mul hZ
  have h2θ : (K : ℝ) * |2 * θ| ≤ 1 / 8 := by rw [abs_mul, abs_of_nonneg zero_le_two]; linarith
  obtain ⟨hre_int, hre_mgf⟩ := hre.mgf_sq_sub_integral_le h2θ
  obtain ⟨him_int, him_mgf⟩ := him.mgf_sq_sub_integral_le h2θ
  have hsplit (ω : Ω) : ‖Z ω‖ ^ 2 - μ[fun ω' ↦ ‖Z ω'‖ ^ 2] =
      ((Z ω).re ^ 2 - μ[fun ω' ↦ (Z ω').re ^ 2]) + ((Z ω).im ^ 2 - μ[fun ω' ↦ (Z ω').im ^ 2]) := by
    simp_rw [fun z : ℂ ↦ (Complex.sq_norm z).trans (by rw [Complex.normSq_apply, ← sq, ← sq])]
    rw [integral_add (hre.memLp 2).integrable_sq (him.memLp 2).integrable_sq]; ring
  simp_rw [hsplit]
  obtain ⟨hint, hle⟩ := TauCeti.mgf_add_le_of_mgf_two_mul_le hre_int him_int hre_mgf him_mgf
  exact ⟨hint, hle.trans_eq (by rw [add_self_div_two]; congr 1; ring)⟩

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

private theorem mk_sq_eq_nnnorm_sq (x : ℝ) : (⟨x ^ 2, sq_nonneg x⟩ : ℝ≥0) = ‖x‖₊ ^ 2 :=
  Subtype.ext <| (sq_abs x).symm.trans <| (congrArg (· ^ 2) (Real.norm_eq_abs x).symm).trans
    (NNReal.coe_pow ‖x‖₊ 2).symm

/-- Independent `K`-sub-Gaussian real and imaginary parts yield directional `K`-sub-Gaussianity. -/
theorem hasSubgaussianMGF_re_star_mul_of_indepFun_re_im
    (hre : HasSubgaussianMGF (fun ω ↦ (Z ω).re) K μ)
    (him : HasSubgaussianMGF (fun ω ↦ (Z ω).im) K μ)
    (hindep : IndepFun (fun ω ↦ (Z ω).re) (fun ω ↦ (Z ω).im) μ) (u : ℂ) :
    HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ := by
  rw [show (fun ω ↦ (star u * Z ω).re) = fun ω ↦ u.re * (Z ω).re + u.im * (Z ω).im from
    funext fun _ ↦ by simp [Complex.mul_re]]
  refine ((hre.const_mul u.re).add_of_indepFun (him.const_mul u.im)
    (hindep.comp (measurable_const_mul u.re) (measurable_const_mul u.im))).mono (le_of_eq ?_)
  exact Subtype.ext <| show u.re ^ 2 * (K : ℝ) + u.im ^ 2 * (K : ℝ) =
      ((‖u‖₊ ^ 2 : ℝ≥0) : ℝ) * (K : ℝ) by
    push_cast; rw [Complex.sq_norm, Complex.normSq_apply]; ring

end ComplexSubGaussian

namespace iIndepFun
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}

/-- The dot product of independent sub-Gaussian random variables with a deterministic vector `w`
is sub-Gaussian with variance proxy `∑ i, ‖w i‖₊ ^ 2 * K i`. -/
theorem hasSubgaussianMGF_dotProduct {X : ι → Ω → ℝ} (hindep : iIndepFun X P) {K : ι → ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) (K i) P) (w : ι → ℝ) :
    HasSubgaussianMGF (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ w) (∑ i, ‖w i‖₊ ^ 2 * K i) P := by
  have hsum : HasSubgaussianMGF (fun ω ↦ ∑ i, w i * X i ω) (∑ i, ‖w i‖₊ ^ 2 * K i) P :=
    HasSubgaussianMGF.sum_of_iIndepFun
      (hindep.comp (fun i x ↦ w i * x) fun i ↦ measurable_const_mul (w i))
      fun i _ ↦ mk_sq_eq_nnnorm_sq (w i) ▸ (hX i).const_mul (w i)
  simpa only [dotProduct, mul_comm] using hsum

/-- Exponential moment bound for the dot product of independent `K`-sub-Gaussian random variables
with a deterministic vector `w`. -/
theorem integral_exp_mul_dotProduct_le {X : ι → Ω → ℝ} (hindep : iIndepFun X P) {K : ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) K P) (w : ι → ℝ) (r : ℝ) :
    Integrable (fun ω ↦ exp (r * ((fun i ↦ X i ω) ⬝ᵥ w))) P ∧
      ∫ ω, exp (r * ((fun i ↦ X i ω) ⬝ᵥ w)) ∂P ≤ exp ((K : ℝ) * r ^ 2 / 2 * ∑ i, w i ^ 2) := by
  have hsub := hindep.hasSubgaussianMGF_dotProduct hX w
  refine ⟨hsub.integrable_exp_mul r, ?_⟩; rw [← mgf]; refine (hsub.mgf_le r).trans_eq ?_
  congr 1; push_cast; simp only [Real.norm_eq_abs, sq_abs, ← Finset.sum_mul]; ring

/-- Exponential moment bound for the split-coordinate dot product of independent directionally
`K`-sub-Gaussian complex random variables with `w : ι ⊕ ι → ℝ`. -/
theorem integral_exp_mul_sum_elim_re_im_dotProduct_le {Z : ι → Ω → ℂ} (hindep : iIndepFun Z P)
    {K : ℝ≥0}
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (w : ι ⊕ ι → ℝ) (r : ℝ) :
    Integrable (fun ω ↦ exp (r * (Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w))) P ∧
      ∫ ω, exp (r * (Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w)) ∂P ≤
        exp ((K : ℝ) * r ^ 2 / 2 * ∑ q, w q ^ 2) := by
  let u : ι → ℂ := fun i ↦ ⟨w (.inl i), w (.inr i)⟩
  have hsum : HasSubgaussianMGF (fun ω ↦ ∑ i, (star (u i) * Z i ω).re)
      (∑ i, ‖u i‖₊ ^ 2 * K) P :=
    HasSubgaussianMGF.sum_of_iIndepFun
      (hindep.comp (fun i z ↦ (star (u i) * z).re) fun _ ↦ by fun_prop) fun i _ ↦ hZ i (u i)
  have hdot (ω : Ω) : Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w =
      ∑ i, (star (u i) * Z i ω).re := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      ← Finset.sum_add_distrib, u, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hsub : HasSubgaussianMGF
      (fun ω ↦ Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w)
      (∑ i, ‖u i‖₊ ^ 2 * K) P := by simpa only [hdot] using hsum
  refine ⟨hsub.integrable_exp_mul r, ?_⟩; rw [← mgf]; refine (hsub.mgf_le r).trans_eq ?_
  congr 1; push_cast
  simp only [Complex.sq_norm, Complex.normSq_apply, u, Fintype.sum_sum_type, ← sq,
    Finset.sum_add_distrib, ← Finset.sum_mul]; ring

end iIndepFun
end ProbabilityTheory
