/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Probability.Moments.SubGaussian.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.QuadraticForm
import TauCeti.Probability.Moments.SubExponential

/-!
# Sub-Gaussian linear forms and squared and directional exponential moments

For independent sub-Gaussian coordinates, a fixed linear form has a sub-Gaussian tail with
variance proxy equal to the sum of the coordinate proxies weighted by the squared coefficients.
Applying this to coefficients of the form `u i * v j` gives the fixed-bilinear-form estimate
used in the operator-norm tail bound for random matrices.

We also develop squared-variable exponential moment bounds for
`ProbabilityTheory.HasSubgaussianMGF` (`integrable_exp_mul_sq`, `integral_exp_mul_sq_le`,
`mgf_sq_sub_integral_le`), complex directional sub-Gaussianity, dot-product sub-Gaussian bounds for
independent real and complex vectors, and Gaussianization and decoupled bilinear MGF bounds for
jointly sub-Gaussian vectors (`TauCeti.integral_exp_half_mul_sum_mulVec_sq_le`,
`TauCeti.mgf_dotProduct_mulVec_prod_le`; Vershynin 2018, §2.5–2.7, §6.2; Rudelson–Vershynin 2013).
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator

namespace ProbabilityTheory

/-- A random variable with centred Gaussian law `gaussianReal 0 v` is `v`-sub-Gaussian. -/
theorem HasLaw.hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ := by
  rw [← HasSubgaussianMGF.id_map_iff hX.aemeasurable, hX.map_eq]
  exact ⟨integrable_exp_mul_gaussianReal, fun t ↦ by simp [mgf_id_gaussianReal]⟩

namespace HasSubgaussianMGF

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

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
    have hmgf_u : ∫⁻ g, F (ω, g) ∂γ = ENNReal.ofReal (mgf (fun g ↦ g) γ u) :=
      (ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal u)
        (.of_forall fun _ ↦ (exp_pos _).le)).symm
    rw [hmgf_u, mgf_fun_id_gaussianReal]
    simp only [zero_mul, zero_add, NNReal.coe_one, one_mul, u]; congr 2; rw [mul_pow, hsq]; ring
  have hright (g : ℝ) : ∫⁻ ω, F (ω, g) ∂μ ≤ ENNReal.ofReal (exp (((c : ℝ) * s) * g ^ 2)) := by
    let t : ℝ := Real.sqrt (2 * s) * g
    have hF_slice : (fun ω ↦ F (ω, g)) = fun ω ↦ ENNReal.ofReal (exp (t * X₀ ω)) :=
      funext fun _ ↦ by dsimp [F, t]; ring_nf
    rw [hF_slice, ← ofReal_integral_eq_lintegral_ofReal (h₀.integrable_exp_mul t)
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
    have henorm : (fun ω ↦ ‖exp (s * X ω ^ 2)‖ₑ) = fun ω ↦ ENNReal.ofReal (exp (s * X ω ^ 2)) :=
      funext fun _ ↦ Real.eNorm_eq_ofReal (exp_pos _).le
    rw [hasFiniteIntegral_def, henorm]
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
      have hsq0 : (fun ω' ↦ X ω' ^ 2) =ᵐ[μ] fun _ ↦ 0 :=
        hX0.mono fun _ hω ↦ by dsimp only; rw [hω]; ring
      have hm0 : μ[fun ω' ↦ X ω' ^ 2] = 0 := by rw [integral_congr_ae hsq0, integral_zero]
      have hexp1 : (fun ω ↦ exp (θ * (X ω ^ 2 - μ[fun ω' ↦ X ω' ^ 2]))) =ᵐ[μ] fun _ ↦ 1 :=
        hX0.mono fun _ hω ↦ by dsimp only; rw [hω, hm0]; simp
      refine ⟨(integrable_const 1).congr hexp1.symm, ?_⟩
      rw [mgf, integral_congr_ae hexp1, integral_const, probReal_univ, one_smul]
      exact Real.one_le_exp (by positivity)
    · have : 0 < (c : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
      let B : ℝ := 4 * (c : ℝ); have hB : 0 < B := by positivity
      have hs_lt : 2 * (c : ℝ) * B⁻¹ < 1 := by dsimp [B]; field_simp; norm_num
      have hexp_int : Integrable (fun ω ↦ exp (X ω ^ 2 / B)) μ := by
        simpa [div_eq_inv_mul] using h.integrable_exp_mul_sq hs_lt
      have hexp_le : ∫ ω, exp (X ω ^ 2 / B) ∂μ ≤ 2 := by
        have h1 := h.integral_exp_mul_sq_le (inv_nonneg.2 hB.le) hs_lt
        have hhalf : 1 - 2 * (c : ℝ) * B⁻¹ = 1 / 2 := by dsimp [B]; field_simp; norm_num
        rw [hhalf] at h1
        have hneg_half : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by norm_num
        have hinv_half : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
        have hrpow : (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) ≤ 2 := by
          rw [hneg_half, Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num), hinv_half]
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
  have him : (fun ω ↦ (star Complex.I * Z ω).re) = fun ω ↦ (Z ω).im :=
    funext fun _ ↦ by simp [Complex.mul_re]
  simpa [him] using hZ Complex.I

/-- Every directionally sub-Gaussian complex random variable is Bochner integrable. -/
theorem integrable_of_hasSubgaussianMGF_re_star_mul
    (hZ : ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ) :
    Integrable Z μ := by
  have hZ_eq : Z = fun ω ↦ ((Z ω).re : ℂ) + ((Z ω).im : ℂ) * Complex.I :=
    funext fun ω ↦ (Complex.re_add_im (Z ω)).symm
  rw [hZ_eq]
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

/-- Independent `K`-sub-Gaussian real and imaginary parts yield directional `K`-sub-Gaussianity. -/
theorem hasSubgaussianMGF_re_star_mul_of_indepFun_re_im
    (hre : HasSubgaussianMGF (fun ω ↦ (Z ω).re) K μ)
    (him : HasSubgaussianMGF (fun ω ↦ (Z ω).im) K μ)
    (hindep : IndepFun (fun ω ↦ (Z ω).re) (fun ω ↦ (Z ω).im) μ) (u : ℂ) :
    HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ := by
  have hproj : (fun ω ↦ (star u * Z ω).re) = fun ω ↦ u.re * (Z ω).re + u.im * (Z ω).im :=
    funext fun _ ↦ by simp [Complex.mul_re]
  rw [hproj]
  refine ((hre.const_mul u.re).add_of_indepFun (him.const_mul u.im)
    (hindep.comp (measurable_const_mul u.re) (measurable_const_mul u.im))).mono (le_of_eq ?_)
  have hcoe : u.re ^ 2 * (K : ℝ) + u.im ^ 2 * (K : ℝ) = ((‖u‖₊ ^ 2 : ℝ≥0) : ℝ) * (K : ℝ) := by
    push_cast; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  exact Subtype.ext hcoe

end ComplexSubGaussian

namespace iIndepFun

/-- Two-sided sub-Gaussian tail bound for a linear combination of independent coordinates. -/
theorem measureReal_abs_sum_mul_ge_le_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ι → ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) (c i) μ) (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
      2 * Real.exp
        (-t ^ 2 / (2 * ∑ i, (a i) ^ 2 * (c i : ℝ))) := by
  let Y : ι → Ω → ℝ := fun i ω ↦ a i * X i ω
  let a2 : ι → ℝ≥0 := fun i ↦ ⟨(a i) ^ 2, sq_nonneg (a i)⟩
  let S : Ω → ℝ := fun ω ↦ ∑ i, Y i ω
  have hY_indep : iIndepFun Y μ :=
    h_indep.comp (fun i x ↦ a i * x) (by intro i; fun_prop)
  have hY : ∀ i, HasSubgaussianMGF (Y i) (a2 i * c i) μ := by
    intro i
    exact (hX i).const_mul (a i)
  have hS : HasSubgaussianMGF S (∑ i, a2 i * c i) μ := by
    exact HasSubgaussianMGF.sum_of_iIndepFun hY_indep
      (c := fun i ↦ a2 i * c i) (s := Finset.univ) (by
        intro i _
        exact hY i)
  have hset : {ω | t ≤ |S ω|} =
      {ω | t ≤ S ω} ∪ {ω | t ≤ -S ω} := by
    ext ω
    simpa only [Set.mem_ofPred_eq, Set.mem_union] using (le_abs : t ≤ |S ω| ↔ _)
  have hset' : {ω | t ≤ |∑ i, a i * X i ω|} =
      {ω | t ≤ S ω} ∪ {ω | t ≤ -S ω} := hset
  have hbound : μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ∑ i, a2 i * c i)) := by
    calc
      μ.real {ω | t ≤ |∑ i, a i * X i ω|} =
          μ.real ({ω | t ≤ S ω} ∪ {ω | t ≤ -S ω}) := by
            rw [hset']
      _ ≤ μ.real {ω | t ≤ S ω} + μ.real {ω | t ≤ -S ω} :=
        measureReal_union_le _ _
      _ ≤ Real.exp (-t ^ 2 / (2 * ∑ i, a2 i * c i)) +
          Real.exp (-t ^ 2 / (2 * ∑ i, a2 i * c i)) :=
        add_le_add (hS.measure_ge_le ht) (hS.neg.measure_ge_le ht)
      _ = 2 * Real.exp (-t ^ 2 / (2 * ∑ i, a2 i * c i)) := by ring
  have hproxy : ((∑ i, a2 i * c i : ℝ≥0) : ℝ) =
      ∑ i, (a i) ^ 2 * (c i : ℝ) := by
    rw [NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [NNReal.coe_mul]
    rfl
  simpa only [hproxy] using hbound

/-- The linear-form tail bound when all coordinates have the same variance proxy. -/
theorem measureReal_abs_sum_mul_ge_le_of_iIndepFun_const
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) c μ) (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ((c : ℝ) * ∑ i, (a i) ^ 2))) := by
  simpa only [Finset.mul_sum, mul_comm] using
    h_indep.measureReal_abs_sum_mul_ge_le_of_iIndepFun hX a ht

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}

/-- The dot product of independent sub-Gaussian random variables with a deterministic vector `w`
is sub-Gaussian with variance proxy `∑ i, ‖w i‖₊ ^ 2 * K i`. -/
theorem hasSubgaussianMGF_dotProduct {X : ι → Ω → ℝ} (hindep : iIndepFun X P) {K : ι → ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) (K i) P) (w : ι → ℝ) :
    HasSubgaussianMGF (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ w) (∑ i, ‖w i‖₊ ^ 2 * K i) P := by
  have hproxy (i : ι) : (⟨w i ^ 2, sq_nonneg (w i)⟩ : ℝ≥0) = ‖w i‖₊ ^ 2 :=
    Subtype.ext <| (sq_abs (w i)).symm.trans <|
      (congrArg (· ^ 2) (Real.norm_eq_abs (w i)).symm).trans (NNReal.coe_pow ‖w i‖₊ 2).symm
  have hsum : HasSubgaussianMGF (fun ω ↦ ∑ i, w i * X i ω) (∑ i, ‖w i‖₊ ^ 2 * K i) P :=
    HasSubgaussianMGF.sum_of_iIndepFun
      (hindep.comp (fun i x ↦ w i * x) fun i ↦ measurable_const_mul (w i))
      fun i _ ↦ hproxy i ▸ (hX i).const_mul (w i)
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

namespace TauCeti

/-- **Gaussianization bound for Euclidean norms of sub-Gaussian linear images** (Vershynin 2018,
Lemma 6.2.3). -/
theorem integral_exp_half_mul_sum_mulVec_sq_le {Ω γ κ : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [Fintype γ] [Fintype κ] [DecidableEq κ]
    {V : Ω → κ → ℝ} (hV_meas : ∀ q, AEMeasurable (fun ω ↦ V ω q) P) {K : ℝ≥0}
    (hV_subG : ∀ (w : κ → ℝ) (r : ℝ), Integrable (fun ω ↦ exp (r * (V ω ⬝ᵥ w))) P ∧
      ∫ ω, exp (r * (V ω ⬝ᵥ w)) ∂P ≤ exp ((K : ℝ) * r ^ 2 / 2 * ∑ q, w q ^ 2))
    (M : Matrix γ κ ℝ) {a : ℝ} (ha_nonneg : 0 ≤ a) (ha_bound : (K : ℝ) * a * ‖M‖ ^ 2 ≤ 1 / 2) :
    Integrable (fun ω ↦ exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2)) P ∧
      ∫ ω, exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2) ∂P ≤ exp ((K : ℝ) * a * ∑ l, ∑ q, M l q ^ 2) := by
  classical
  let ν : Measure (γ → ℝ) := Measure.pi fun _ : γ ↦ gaussianReal 0 1
  let r : ℝ := Real.sqrt a; have hr_sq : r ^ 2 = a := Real.sq_sqrt ha_nonneg
  let F : Ω × (γ → ℝ) → ℝ := fun p ↦ exp (r * ((M *ᵥ V p.1) ⬝ᵥ p.2))
  have hF_meas : AEStronglyMeasurable F (P.prod ν) := by
    have hcont : Continuous (fun q : (κ → ℝ) × (γ → ℝ) ↦ exp (r * ((M *ᵥ q.1) ⬝ᵥ q.2))) := by
      simp only [dotProduct, Matrix.mulVec]; fun_prop
    have hm : AEMeasurable (fun p : Ω × (γ → ℝ) ↦ (V p.1, p.2)) (P.prod ν) :=
      ((AEMeasurable.of_eval hV_meas).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).prodMk measurable_snd.aemeasurable
    exact (hcont.measurable.comp_aemeasurable hm).aestronglyMeasurable
  have hF_adj (ω : Ω) (g : γ → ℝ) : (M *ᵥ V ω) ⬝ᵥ g = V ω ⬝ᵥ (Mᵀ *ᵥ g) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  have hs_bound : 2 * ((K : ℝ) * a / 2) * ‖Mᵀ‖ ^ 2 ≤ 1 / 2 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial M, Matrix.l2_opNorm_conjTranspose]; linarith
  obtain ⟨hg_int, hg_le⟩ :=
    (Mᵀ).integral_exp_mul_sum_mulVec_sq_pi_gaussianReal_le (by positivity) hs_bound
  have hslice_P (g : γ → ℝ) : Integrable (fun ω ↦ F (ω, g)) P ∧
      ∫ ω, F (ω, g) ∂P ≤ exp (((K : ℝ) * a / 2) * ∑ q, ((Mᵀ *ᵥ g) q) ^ 2) := by
    obtain ⟨hint, hle⟩ := hV_subG (Mᵀ *ᵥ g) r
    have hFeq (ω : Ω) : F (ω, g) = exp (r * (V ω ⬝ᵥ (Mᵀ *ᵥ g))) := by dsimp [F]; rw [hF_adj]
    exact ⟨hint.congr (.of_forall fun ω ↦ (hFeq ω).symm),
      (integral_congr_ae (.of_forall hFeq)).trans_le (by simpa only [hr_sq] using hle)⟩
  obtain ⟨hFs_int, hFs_le⟩ := integrable_and_integral_prod_le hF_meas.prod_swap
    (.of_forall fun _ ↦ (exp_pos _).le) hg_int (.of_forall hslice_P)
  have hF_int : Integrable F (P.prod ν) := hFs_int.swap
  have hgauss_id (ω : Ω) : ∫ g, F (ω, g) ∂ν = exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2) := by
    rw [(integral_exp_mul_dotProduct_pi_gaussianReal (M *ᵥ V ω) 1 r).2,
      NNReal.coe_one, one_mul, hr_sq]
  refine ⟨hF_int.integral_norm_prod_left.congr (.of_forall fun ω ↦
    (integral_congr_ae (.of_forall fun _ ↦ Real.norm_of_nonneg (exp_pos _).le)).trans
      (hgauss_id ω)), ?_⟩
  refine ((integral_congr_ae (.of_forall fun ω ↦ (hgauss_id ω).symm)).trans
    ((integral_prod F hF_int).symm.trans (integral_prod_swap F).symm)).trans_le ?_
  exact (hFs_le.trans hg_le).trans_eq
    (by congr 1; simp only [Matrix.transpose_apply]; rw [Finset.sum_comm]; ring)

/-- **Bilinear MGF bound for independent jointly sub-Gaussian vectors** (Vershynin 2018,
Lemma 6.2.2): if `V₁` and `V₂` have `K₁`- and `K₂`-sub-Gaussian linear-form exponential moments
under `P₁` and `P₂`, then for `B : Matrix γ κ ℝ` and `K₁ * K₂ * u ^ 2 * ‖B‖ ^ 2 ≤ 1 / 2`, the
bilinear form `p ↦ V₁ p.1 ⬝ᵥ B *ᵥ V₂ p.2` on `P₁.prod P₂` has MGF at most
`exp (K₁ * K₂ * u ^ 2 * ∑ i, ∑ j, B i j ^ 2)`. -/
theorem mgf_dotProduct_mulVec_prod_le {Ω₁ Ω₂ γ κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    [Fintype γ] [Fintype κ] [DecidableEq κ]
    {V₁ : Ω₁ → γ → ℝ} (hV₁_meas : ∀ l, AEMeasurable (fun ω₁ ↦ V₁ ω₁ l) P₁)
    {V₂ : Ω₂ → κ → ℝ} (hV₂_meas : ∀ q, AEMeasurable (fun ω₂ ↦ V₂ ω₂ q) P₂) {K₁ K₂ : ℝ≥0}
    (hV₁_subG : ∀ (w : γ → ℝ) (r : ℝ), Integrable (fun ω₁ ↦ exp (r * (V₁ ω₁ ⬝ᵥ w))) P₁ ∧
      ∫ ω₁, exp (r * (V₁ ω₁ ⬝ᵥ w)) ∂P₁ ≤ exp ((K₁ : ℝ) * r ^ 2 / 2 * ∑ l, w l ^ 2))
    (hV₂_subG : ∀ (w : κ → ℝ) (r : ℝ), Integrable (fun ω₂ ↦ exp (r * (V₂ ω₂ ⬝ᵥ w))) P₂ ∧
      ∫ ω₂, exp (r * (V₂ ω₂ ⬝ᵥ w)) ∂P₂ ≤ exp ((K₂ : ℝ) * r ^ 2 / 2 * ∑ q, w q ^ 2))
    (B : Matrix γ κ ℝ) {u : ℝ} (hu : (K₁ : ℝ) * (K₂ : ℝ) * u ^ 2 * ‖B‖ ^ 2 ≤ 1 / 2) :
    Integrable (fun p : Ω₁ × Ω₂ ↦ exp (u * (V₁ p.1 ⬝ᵥ B *ᵥ V₂ p.2))) (P₁.prod P₂) ∧
      mgf (fun p : Ω₁ × Ω₂ ↦ V₁ p.1 ⬝ᵥ B *ᵥ V₂ p.2) (P₁.prod P₂) u ≤
        exp ((K₁ : ℝ) * (K₂ : ℝ) * u ^ 2 * ∑ i, ∑ j, B i j ^ 2) := by
  let G : Ω₁ × Ω₂ → ℝ := fun p ↦ exp (u * (V₁ p.1 ⬝ᵥ B *ᵥ V₂ p.2))
  have hcont : Continuous (fun q : (γ → ℝ) × (κ → ℝ) ↦ exp (u * (q.1 ⬝ᵥ (B *ᵥ q.2)))) := by
    simp only [dotProduct, Matrix.mulVec]; fun_prop
  have hG_meas : AEStronglyMeasurable G (P₁.prod P₂) := by
    have hm := ((AEMeasurable.of_eval hV₁_meas).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).prodMk
      ((AEMeasurable.of_eval hV₂_meas).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd)
    exact (hcont.measurable.comp_aemeasurable hm).aestronglyMeasurable
  obtain ⟨hX2_int, hX2_le⟩ := integral_exp_half_mul_sum_mulVec_sq_le hV₂_meas hV₂_subG B
    (by positivity) (by linarith : (K₂ : ℝ) * ((K₁ : ℝ) * u ^ 2) * ‖B‖ ^ 2 ≤ 1 / 2)
  obtain ⟨hGs_int, hGs_le⟩ := integrable_and_integral_prod_le hG_meas.prod_swap
    (.of_forall fun _ ↦ (exp_pos _).le) hX2_int (.of_forall fun ω₂ ↦ hV₁_subG (B *ᵥ V₂ ω₂) u)
  refine ⟨hGs_int.swap, ?_⟩
  rw [mgf, ← integral_prod_swap G]
  exact (hGs_le.trans hX2_le).trans_eq (by congr 1; ring)

end TauCeti
