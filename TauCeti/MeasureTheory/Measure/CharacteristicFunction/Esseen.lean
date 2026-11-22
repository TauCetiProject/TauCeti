/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.CharacteristicFunction
import TauCeti.Analysis.SpecialFunctions.Integrals.Trigonometric.Triangle

/-!
# Esseen's concentration inequality

A finite measure on `ℝ` gives every closed interval of radius `ε > 0` mass at most
`(24 / 23)² ε ∫_{-1/ε}^{1/ε} ‖φ(θ)‖ dθ`, where `φ = charFun μ` is its characteristic function
(`MeasureTheory.measureReal_closedBall_le_integral_norm_charFun`). The bound is uniform in the
centre of the interval, so it bounds the Lévy concentration function `sup_v μ [v - ε, v + ε]`.

For a weighted sum `S = ∑ aᵢ Xᵢ` of independent real random variables the characteristic
function factors, which gives the small-ball estimate
`P(|S - v| ≤ ε) ≤ (24 / 23)² ε ∫_{-1/ε}^{1/ε} ∏ᵢ ‖φ_{Xᵢ}(aᵢ θ)‖ dθ`
(`ProbabilityTheory.iIndepFun.measureReal_abs_sum_mul_sub_le_integral_prod_norm_charFun`).
This is the starting point of the Fourier-analytic small-ball and Littlewood–Offord estimates
for sums of independent random variables, which bound the probability that a random vector
lies close to a fixed hyperplane and hence the least singular value of a random matrix.

The proof bounds the indicator of `[-1, 1]` by a multiple of the Fejér kernel
`sinc (x / 2)²`, whose cosine transform is the triangle function
(`TauCeti.integral_one_sub_abs_mul_cos_mul`), and exchanges the two integrals.

## References

* C.-G. Esseen, *On the Kolmogorov–Rogozin inequality for the concentration function*,
  Z. Wahrscheinlichkeitstheorie verw. Gebiete 5 (1966), 210–216.
* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), §4.
* T. Tao and V. Vu, *Additive Combinatorics*, Cambridge University Press (2006), §7.
-/

public section

open Metric Set
open scoped Topology

namespace MeasureTheory

/-- The cosine moment `∫ cos ((x - v) θ) dμ` is the real part of the characteristic function
shifted by the phase of `v`. -/
private theorem integral_cos_sub_mul_eq_re (μ : Measure ℝ) [IsFiniteMeasure μ] (v θ : ℝ) :
    ∫ x, Real.cos ((x - v) * θ) ∂μ =
      (Complex.exp (((-(θ * v) : ℝ) : ℂ) * Complex.I) * charFun μ θ).re := by
  have hint : Integrable (fun x : ℝ ↦ Complex.exp (((-(θ * v) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (θ * x * Complex.I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, ← Complex.ofReal_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [charFun_apply_real, ← integral_const_mul]
  refine Eq.trans ?_ (integral_re hint)
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [RCLike.re_to_complex]
  rw [← Complex.exp_add, show ((-(θ * v) : ℝ) : ℂ) * Complex.I + θ * x * Complex.I =
    (((x - v) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact (Complex.exp_ofReal_mul_I_re _).symm

/-- For `|θ| ≤ 1`, the `μ`-average of the triangle-weighted cosine `(1 - |θ|) cos ((x - v) θ)` is
at most `‖charFun μ θ‖`. -/
private theorem integral_one_sub_abs_mul_cos_le_norm_charFun (μ : Measure ℝ)
    [IsFiniteMeasure μ] (v : ℝ) {θ : ℝ} (hθ : |θ| ≤ 1) :
    ∫ x, (1 - |θ|) * Real.cos ((x - v) * θ) ∂μ ≤ ‖charFun μ θ‖ := by
  rw [integral_const_mul, integral_cos_sub_mul_eq_re]
  calc (1 - |θ|) * (Complex.exp (((-(θ * v) : ℝ) : ℂ) * Complex.I) * charFun μ θ).re
      ≤ (1 - |θ|) * ‖Complex.exp (((-(θ * v) : ℝ) : ℂ) * Complex.I) * charFun μ θ‖ :=
        mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sub_nonneg.2 hθ)
    _ ≤ ‖charFun μ θ‖ := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [abs_nonneg θ])

/-- **Esseen's inequality** at unit scale: a finite measure on `ℝ` gives every closed interval
of radius one mass at most `(24 / 23)² ∫_{-1}^{1} ‖charFun μ θ‖ dθ`. -/
private theorem measureReal_closedBall_one_le_integral_norm_charFun (μ : Measure ℝ)
    [IsFiniteMeasure μ] (v : ℝ) :
    μ.real (closedBall v 1) ≤ (24 / 23) ^ 2 * ∫ θ in (-1 : ℝ)..1, ‖charFun μ θ‖ := by
  set ν : Measure ℝ := volume.restrict (Ioc (-1) 1)
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  -- the kernel `(x, θ) ↦ (1 - |θ|) cos ((x - v) θ)` is integrable for `μ ⊗ ν`
  have hF : Integrable (Function.uncurry fun (x θ : ℝ) ↦ (1 - |θ|) * Real.cos ((x - v) * θ))
      (μ.prod ν) := by
    have hw : Integrable (fun θ : ℝ ↦ 1 - |θ|) ν :=
      (Continuous.intervalIntegrable (μ := volume) (by fun_prop) (-1) 1).1
    refine (hw.comp_snd μ).mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun p ↦ ?_)
    simpa using Real.abs_cos_le_one ((p.1 - v) * p.2)
  calc μ.real (closedBall v 1) = ∫ x, (closedBall v 1).indicator 1 x ∂μ :=
        (integral_indicator_one measurableSet_closedBall).symm
    _ ≤ ∫ x, (24 / 23) ^ 2 * Real.sinc ((x - v) / 2) ^ 2 ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x ↦ ?_)
          (Integrable.of_bound (Continuous.aestronglyMeasurable (continuous_const.mul
            ((Real.continuous_sinc.comp ((continuous_id.sub continuous_const).div_const 2)).pow
              2))) ((24 / 23) ^ 2) (ae_of_all _ fun x ↦ ?_))
          (ae_of_all _ fun x ↦ ?_)
        · exact indicator_nonneg (fun _ _ ↦ zero_le_one) x
        · have h1 : |Real.sinc ((x - v) / 2)| ≤ 1 := Real.abs_sinc_le_one _
          have h2 : Real.sinc ((x - v) / 2) ^ 2 ≤ 1 := by
            rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) h1
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          nlinarith
        · by_cases hx : x ∈ closedBall v 1
          · rw [indicator_of_mem hx, Pi.one_apply]
            have := TauCeti.sq_le_sinc_div_two_sq (x := x - v) (by rwa [← Real.dist_eq])
            nlinarith
          · rw [indicator_of_notMem hx]
            positivity
    _ = (24 / 23) ^ 2 * ∫ θ in Ioc (-1 : ℝ) 1,
          ∫ x, (1 - |θ|) * Real.cos ((x - v) * θ) ∂μ := by
        rw [integral_const_mul]
        congr 1
        simp_rw [← TauCeti.integral_one_sub_abs_mul_cos_mul, intervalIntegral.integral_of_le hle]
        exact integral_integral_swap hF
    _ ≤ (24 / 23) ^ 2 * ∫ θ in (-1 : ℝ)..1, ‖charFun μ θ‖ := by
        rw [intervalIntegral.integral_of_le hle]
        exact mul_le_mul_of_nonneg_left (setIntegral_mono_on hF.integral_prod_right
          intervalIntegrable_charFun.norm.1 measurableSet_Ioc fun θ hθ ↦
            integral_one_sub_abs_mul_cos_le_norm_charFun μ v (abs_le.2 ⟨hθ.1.le, hθ.2⟩))
          (by positivity)

/-- **Esseen's inequality**: a finite measure on `ℝ` gives every closed interval of radius
`ε > 0` mass at most `(24 / 23)² ε ∫_{-1/ε}^{1/ε} ‖charFun μ θ‖ dθ`. The bound does not depend
on the centre `v`, so it also bounds the Lévy concentration function of `μ`. -/
theorem measureReal_closedBall_le_integral_norm_charFun (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ) {ε : ℝ} (hε : 0 < ε) :
    μ.real (closedBall v ε) ≤ (24 / 23) ^ 2 * ε * ∫ θ in -ε⁻¹..ε⁻¹, ‖charFun μ θ‖ := by
  have hmeas : Measurable (fun x : ℝ ↦ ε⁻¹ * x) := by fun_prop
  have hpre : (fun x : ℝ ↦ ε⁻¹ * x) ⁻¹' closedBall (ε⁻¹ * v) 1 = closedBall v ε := by
    ext x
    simp only [mem_preimage, mem_closedBall, Real.dist_eq, ← mul_sub, abs_mul,
      abs_inv, abs_of_pos hε]
    rw [inv_mul_le_iff₀ hε, mul_one]
  have h := measureReal_closedBall_one_le_integral_norm_charFun
    (μ.map fun x ↦ ε⁻¹ * x) (ε⁻¹ * v)
  rw [map_measureReal_apply hmeas measurableSet_closedBall, hpre] at h
  simp_rw [charFun_map_mul] at h
  rw [intervalIntegral.integral_comp_mul_left (fun θ ↦ ‖charFun μ θ‖) (inv_ne_zero hε.ne'),
    inv_inv, smul_eq_mul, mul_neg_one, mul_one] at h
  linarith

end MeasureTheory

namespace ProbabilityTheory

open MeasureTheory

/-- **Small-ball estimate for independent sums**: for independent real random variables `Xᵢ`
under a finite measure `P` and real weights `aᵢ`, the `P`-measure of the event that `∑ᵢ aᵢ Xᵢ`
lies within `ε > 0` of a point `v` is at most `(24 / 23)² ε ∫_{-1/ε}^{1/ε} ∏ᵢ ‖φ_{Xᵢ}(aᵢ θ)‖ dθ`,
where `φ_{Xᵢ}` is the characteristic function of the law of `Xᵢ`. -/
theorem iIndepFun.measureReal_abs_sum_mul_sub_le_integral_prod_norm_charFun
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {X : ι → Ω → ℝ} (hX : iIndepFun X P) (mX : ∀ i, AEMeasurable (X i) P) (s : Finset ι)
    (a : ι → ℝ) (v : ℝ) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | |∑ i ∈ s, a i * X i ω - v| ≤ ε} ≤
      (24 / 23) ^ 2 * ε * ∫ θ in -ε⁻¹..ε⁻¹, ∏ i ∈ s, ‖charFun (P.map (X i)) (a i * θ)‖ := by
  have mY : ∀ i, AEMeasurable (fun ω ↦ a i * X i ω) P := fun i ↦ (mX i).const_mul (a i)
  have hY : iIndepFun (fun i ω ↦ a i * X i ω) P :=
    hX.comp (fun i x ↦ a i * x) fun i ↦ measurable_const_mul (a i)
  have hS : AEMeasurable (fun ω ↦ ∑ i ∈ s, a i * X i ω) P :=
    Finset.aemeasurable_fun_sum s fun i _ ↦ mY i
  have h := measureReal_closedBall_le_integral_norm_charFun
    (P.map fun ω ↦ ∑ i ∈ s, a i * X i ω) v hε
  rw [map_measureReal_apply_of_aemeasurable hS measurableSet_closedBall,
    (hY.restrict s).charFun_map_fun_finsetSum_eq_prod fun i _ ↦ mY i] at h
  have hpre : (fun ω ↦ ∑ i ∈ s, a i * X i ω) ⁻¹' closedBall v ε =
      {ω | |∑ i ∈ s, a i * X i ω - v| ≤ ε} := by
    ext ω
    simp [Real.dist_eq]
  rw [hpre] at h
  simpa [Finset.prod_apply, charFun_map_mul_comp (mX _)] using h

end ProbabilityTheory
