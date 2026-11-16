/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Integral.RpowLaplace

/-!
# The Bessel kernel

On a finite-dimensional real inner product space `E` of dimension `n`, the Bessel potential
`J^{-δ}` of order `δ > 0`, the Fourier multiplier with symbol `(1 + ‖ξ‖²) ^ (-δ / 2)` in Mathlib's
normalization `𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`, is convolution with the **Bessel kernel**

`G_δ(x) = Γ(δ/2)⁻¹ ∫₀^∞ t ^ (δ/2 - 1) e^{-t} K_{t / (4π²)}(x) dt`,

where `K_t` is the heat kernel (`TauCeti.heatKernel`). This is the subordination of the Bessel
potential to the heat semigroup: the Gamma integral
`(1 + ‖ξ‖²) ^ (-δ / 2) = Γ(δ/2)⁻¹ ∫₀^∞ t ^ (δ/2 - 1) e^{-t (1 + ‖ξ‖²)} dt` writes the symbol as an
average of the Gaussians `e^{-t ‖ξ‖²} = 𝓕 K_{t / (4π²)}(ξ)`.

The kernel is nonnegative, has mass one, and is the inverse Fourier transform of the Bessel
symbol. For `0 < δ < n` it is dominated by the Riesz kernel of order `δ`:
`G_δ(x) ≤ Γ((n - δ)/2) / Γ(δ/2) · π ^ (δ - n/2) · ‖x‖ ^ (δ - n)` for `x ≠ 0`, obtained by
dropping the factor `e^{-t}` and evaluating the remaining Gamma integral. Together with the
Hardy–Littlewood–Sobolev inequality this gives the Sobolev embedding of Bessel-potential spaces.

## Main declarations

* `TauCeti.besselKernel`: the Bessel kernel `G_δ`.
* `TauCeti.besselKernel_nonneg`, `TauCeti.besselKernel_neg`: it is nonnegative and even.
* `TauCeti.integrable_besselKernel`, `TauCeti.integral_besselKernel`: it is integrable with mass
  one.
* `TauCeti.fourier_besselKernel`: its Fourier transform is `(1 + ‖ξ‖²) ^ (-δ / 2)`.
* `TauCeti.besselKernel_le_mul_norm_rpow`: the bound by the Riesz kernel of order `δ`.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V,
  §3.1.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., §1.2.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real Set
open scoped FourierTransform RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **Bessel kernel** of order `δ` on `E`:
`G_δ(x) = Γ(δ/2)⁻¹ ∫₀^∞ t ^ (δ/2 - 1) e^{-t} K_{t / (4π²)}(x) dt`, where `K_t` is the heat kernel.
For `δ > 0` it is the kernel of the Bessel potential `J^{-δ}` with symbol
`(1 + ‖ξ‖²) ^ (-δ / 2)` (`TauCeti.fourier_besselKernel`); for `δ ≤ 0` its value carries no
meaning. -/
def besselKernel (δ : ℝ) (x : E) : ℝ :=
  (Gamma (δ / 2))⁻¹ *
    ∫ t in Ioi (0 : ℝ), t ^ (δ / 2 - 1) * exp (-t) * heatKernel (t / (4 * π ^ 2)) x

/-- The defining formula of the Bessel kernel. -/
theorem besselKernel_apply (δ : ℝ) (x : E) :
    besselKernel δ x = (Gamma (δ / 2))⁻¹ *
      ∫ t in Ioi (0 : ℝ), t ^ (δ / 2 - 1) * exp (-t) * heatKernel (t / (4 * π ^ 2)) x :=
  (rfl)

/-- The Bessel kernel is even. -/
@[simp]
theorem besselKernel_neg (δ : ℝ) (x : E) : besselKernel δ (-x) = besselKernel δ x := by
  simp [besselKernel_apply]

/-- The integrand `(t, x) ↦ t ^ (δ/2 - 1) e^{-t} K_{t / (4π²)}(x)` of the Bessel kernel. -/
private def integrand (δ : ℝ) (q : ℝ × E) : ℝ :=
  q.1 ^ (δ / 2 - 1) * exp (-q.1) * heatKernel (q.1 / (4 * π ^ 2)) q.2

/-- The Bessel kernel is the integral in `t` of its integrand. -/
private theorem besselKernel_eq_integral_integrand (δ : ℝ) (x : E) :
    besselKernel δ x = (Gamma (δ / 2))⁻¹ * ∫ t in Ioi (0 : ℝ), integrand δ (t, x) :=
  (rfl)

private theorem integrand_nonneg {δ t : ℝ} (ht : 0 < t) (x : E) : 0 ≤ integrand δ (t, x) :=
  mul_nonneg (by positivity) (heatKernel_pos (by positivity) x).le

/-- The Bessel kernel of positive order is nonnegative. -/
theorem besselKernel_nonneg {δ : ℝ} (hδ : 0 < δ) (x : E) : 0 ≤ besselKernel δ x := by
  rw [besselKernel_eq_integral_integrand]
  exact mul_nonneg (inv_nonneg.2 (Gamma_pos_of_pos (half_pos hδ)).le)
    (setIntegral_nonneg measurableSet_Ioi fun t ht ↦ integrand_nonneg ht x)

private theorem measurable_integrand [MeasurableSpace E] [BorelSpace E] (δ : ℝ) :
    Measurable (integrand (E := E) δ) := by
  unfold integrand
  simp_rw [heatKernel_apply]
  fun_prop

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The integrand of the Bessel kernel is integrable on `(0, ∞) × E`: its integral in `x` is
`t ^ (δ/2 - 1) e^{-t}`, the integrand of `Γ(δ/2)`. -/
private theorem integrable_integrand {δ : ℝ} (hδ : 0 < δ) :
    Integrable (integrand (E := E) δ) ((volume.restrict (Ioi 0)).prod volume) := by
  rw [integrable_prod_iff (measurable_integrand (E := E) δ).aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    simpa only [integrand] using (integrable_heatKernel (E := E)
      (show 0 < t / (4 * π ^ 2) by positivity)).const_mul (t ^ (δ / 2 - 1) * exp (-t))
  · refine (GammaIntegral_convergent (half_pos hδ)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : (0 : ℝ) < t := ht
    have hτ : 0 < t / (4 * π ^ 2) := by positivity
    simp_rw [integrand, norm_mul, norm_of_nonneg (heatKernel_pos hτ _).le, integral_const_mul,
      integral_heatKernel hτ, norm_of_nonneg (rpow_nonneg ht.le _),
      norm_of_nonneg (exp_pos _).le, mul_one, mul_comm]

/-- The Bessel kernel of positive order is integrable. -/
theorem integrable_besselKernel {δ : ℝ} (hδ : 0 < δ) : Integrable (besselKernel δ : E → ℝ) := by
  have h := (integrable_integrand (E := E) hδ).integral_prod_right
  exact (h.const_mul (Gamma (δ / 2))⁻¹).congr
    (.of_forall fun x ↦ (besselKernel_eq_integral_integrand δ x).symm)

/-- **The Bessel kernel has mass one.** -/
@[simp]
theorem integral_besselKernel {δ : ℝ} (hδ : 0 < δ) : ∫ x : E, besselKernel δ x = 1 := by
  simp_rw [besselKernel_eq_integral_integrand, integral_const_mul]
  rw [integral_integral_swap (f := fun x t ↦ integrand δ (t, x))
    (integrable_integrand hδ).swap]
  have h : ∀ t ∈ Ioi (0 : ℝ), ∫ x : E, integrand δ (t, x) = exp (-t) * t ^ (δ / 2 - 1) :=
    fun t (ht : 0 < t) ↦ by
      simp only [integrand]
      rw [integral_const_mul, integral_heatKernel (by positivity), mul_one, mul_comm]
  rw [setIntegral_congr_fun measurableSet_Ioi h, ← Gamma_eq_integral (half_pos hδ),
    inv_mul_cancel₀ (Gamma_pos_of_pos (half_pos hδ)).ne']

/-- **The Fourier transform of the Bessel kernel.** In Mathlib's normalization
`𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`, `𝓕 G_δ(ξ) = (1 + ‖ξ‖²) ^ (-δ / 2)` for `δ > 0`: the Bessel
kernel is the kernel of the Bessel potential `J^{-δ}`. -/
theorem fourier_besselKernel {δ : ℝ} (hδ : 0 < δ) (ξ : E) :
    𝓕 (fun x : E ↦ (besselKernel δ x : ℂ)) ξ = ((1 + ‖ξ‖ ^ 2) ^ (-δ / 2) : ℝ) := by
  -- The integrand of the Fourier integral of `G_δ`, before integration in `t`.
  set Φ : E → ℝ → ℂ := fun x t ↦ (𝐞 (-⟪x, ξ⟫) : ℂ) * (integrand δ (t, x) : ℂ)
  have hΦ : Integrable (Function.uncurry Φ)
      ((volume : Measure E).prod (volume.restrict (Ioi 0))) := by
    refine ((integrable_integrand (E := E) hδ).swap.ofReal (𝕜 := ℂ)).mono ?_
      (.of_forall fun q ↦ by simp [Φ, Function.uncurry, Complex.norm_real, Prod.swap])
    exact ((by fun_prop : Continuous fun q : E × ℝ ↦ (𝐞 (-⟪q.1, ξ⟫) : ℂ)).aestronglyMeasurable).mul
      (Complex.measurable_ofReal.comp
        ((measurable_integrand δ).comp measurable_swap)).aestronglyMeasurable
  -- For fixed `t`, the integral in `x` is `t ^ (δ/2 - 1) e^{-t} 𝓕 K_{t / (4π²)}(ξ)`.
  have hinner : ∀ t ∈ Ioi (0 : ℝ),
      ∫ x, Φ x t = ((t ^ (δ / 2 - 1) * exp (-((1 + ‖ξ‖ ^ 2) * t)) : ℝ) : ℂ) := by
    intro t (ht : 0 < t)
    have hτ : 0 < t / (4 * π ^ 2) := by positivity
    have h : ∫ x, Φ x t = ((t ^ (δ / 2 - 1) * exp (-t) : ℝ) : ℂ) *
        𝓕 (fun x : E ↦ (heatKernel (t / (4 * π ^ 2)) x : ℂ)) ξ := by
      rw [Real.fourier_eq, ← integral_const_mul]
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      simp only [Φ, integrand, Circle.smul_def, smul_eq_mul]
      push_cast
      ring
    rw [h, fourier_heatKernel hτ, ← Complex.ofReal_mul, mul_assoc, ← exp_add]
    congr 4
    field_simp
    ring
  calc 𝓕 (fun x : E ↦ (besselKernel δ x : ℂ)) ξ
      = ((Gamma (δ / 2))⁻¹ : ℝ) * ∫ x, ∫ t in Ioi 0, Φ x t := by
        rw [Real.fourier_eq, ← integral_const_mul]
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        -- Move the constants and the character inside the integral in `t`.
        simp only [besselKernel_eq_integral_integrand, Circle.smul_def, smul_eq_mul,
          Complex.ofReal_mul, ← integral_complex_ofReal, ← integral_const_mul, Φ]
        refine integral_congr_ae (.of_forall fun t ↦ ?_)
        ring
    _ = ((Gamma (δ / 2))⁻¹ : ℝ) * ∫ t in Ioi 0, ∫ x, Φ x t := by
        rw [integral_integral_swap hΦ]
    _ = ((1 + ‖ξ‖ ^ 2) ^ (-δ / 2) : ℝ) := by
        rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_complex_ofReal,
          integral_rpow_mul_exp_neg_mul_Ioi (half_pos hδ) (by positivity), ← Complex.ofReal_mul]
        congr 1
        rw [one_div, inv_rpow (by positivity), ← rpow_neg (by positivity), mul_left_comm,
          inv_mul_cancel₀ (Gamma_pos_of_pos (half_pos hδ)).ne', mul_one, neg_div]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The heat kernel at time `t / (4π²)`: `K_{t / (4π²)}(x) = (t / π) ^ (-n/2) e^{-π² ‖x‖² / t}`. -/
private theorem heatKernel_div_four_mul_pi_sq {t : ℝ} (ht : 0 < t) (x : E) :
    heatKernel (t / (4 * π ^ 2)) x =
      (t / π) ^ (-(Module.finrank ℝ E : ℝ) / 2) * exp (-((π * ‖x‖) ^ 2 / t)) := by
  rw [heatKernel_apply]
  congr 2
  · field_simp
  · field_simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Dropping the factor `e^{-t} ≤ 1`, the integrand of the Bessel kernel is at most
`π ^ (n/2) t ^ (-((n - δ)/2 + 1)) e^{-π² ‖x‖² / t}`. -/
private theorem integrand_le {δ : ℝ} {t : ℝ} (ht : 0 < t) (x : E) :
    integrand δ (t, x) ≤ π ^ ((Module.finrank ℝ E : ℝ) / 2) *
      (t ^ (-((Module.finrank ℝ E - δ) / 2 + 1)) * exp (-((π * ‖x‖) ^ 2 / t))) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have e : t ^ (δ / 2 - 1) * t ^ (-(n / 2)) = t ^ (-((n - δ) / 2 + 1)) := by
    rw [← rpow_add ht]
    ring_nf
  simp only [integrand]
  rw [heatKernel_div_four_mul_pi_sq ht, neg_div, div_rpow ht.le pi_pos.le, rpow_neg pi_pos.le,
    div_inv_eq_mul, ← e]
  calc t ^ (δ / 2 - 1) * exp (-t) * (t ^ (-(n / 2)) * π ^ (n / 2) *
        exp (-((π * ‖x‖) ^ 2 / t)))
      = exp (-t) * (π ^ (n / 2) * (t ^ (δ / 2 - 1) * t ^ (-(n / 2)) *
          exp (-((π * ‖x‖) ^ 2 / t)))) := by ring
    _ ≤ 1 * (π ^ (n / 2) * (t ^ (δ / 2 - 1) * t ^ (-(n / 2)) *
          exp (-((π * ‖x‖) ^ 2 / t)))) := by
        gcongr
        exact exp_le_one_iff.2 (by linarith)
    _ = _ := one_mul _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The Bessel kernel is dominated by the Riesz kernel.** For `0 < δ < n`, where `n` is the
dimension of `E`, and `x ≠ 0`,
`G_δ(x) ≤ Γ((n - δ)/2) / Γ(δ/2) · π ^ (δ - n/2) · ‖x‖ ^ (δ - n)`. -/
theorem besselKernel_le_mul_norm_rpow {δ : ℝ} (hδ : 0 < δ)
    (hδn : δ < Module.finrank ℝ E) {x : E} (hx : x ≠ 0) :
    besselKernel δ x ≤ Gamma ((Module.finrank ℝ E - δ) / 2) / Gamma (δ / 2) *
      π ^ (δ - Module.finrank ℝ E / 2) * ‖x‖ ^ (δ - Module.finrank ℝ E) := by
  borelize E
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  set a : ℝ := (n - δ) / 2
  have ha : 0 < a := by simp only [a]; linarith
  have hr : 0 < (π * ‖x‖) ^ 2 := by positivity
  -- Integrate the bound of `TauCeti.integrand_le` with Euler's integral in `1 / t`.
  have hdom := (integrableOn_rpow_mul_exp_neg_div_Ioi ha hr).const_mul (π ^ (n / 2))
  have hle : ∫ t in Ioi (0 : ℝ), integrand δ (t, x) ≤
      ∫ t in Ioi (0 : ℝ), π ^ (n / 2) * (t ^ (-(a + 1)) * exp (-((π * ‖x‖) ^ 2 / t))) := by
    refine setIntegral_mono_on ?_ hdom measurableSet_Ioi fun t (ht : 0 < t) ↦ integrand_le ht x
    refine hdom.mono' ((measurable_integrand (E := E) δ).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [norm_of_nonneg (integrand_nonneg ht x)]
    exact integrand_le ht x
  rw [besselKernel_eq_integral_integrand]
  calc (Gamma (δ / 2))⁻¹ * ∫ t in Ioi (0 : ℝ), integrand δ (t, x)
      ≤ (Gamma (δ / 2))⁻¹ * ∫ t in Ioi (0 : ℝ),
          π ^ (n / 2) * (t ^ (-(a + 1)) * exp (-((π * ‖x‖) ^ 2 / t))) :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (Gamma_pos_of_pos (half_pos hδ)).le)
    _ = Gamma a / Gamma (δ / 2) * π ^ (δ - n / 2) * ‖x‖ ^ (δ - n) := by
        -- Euler's integral is `((π ‖x‖)²)^(-a) Γ(a)`, and `-2a = δ - n`.
        have he : (2 : ℝ) * -a = δ - n := by
          simp only [a]
          ring
        have hpow : (1 / (π * ‖x‖) ^ 2) ^ a = π ^ (δ - n) * ‖x‖ ^ (δ - n) := by
          rw [one_div, inv_rpow hr.le, ← rpow_neg hr.le, ← rpow_two, ← rpow_mul (by positivity),
            he, mul_rpow pi_pos.le (norm_nonneg _)]
        rw [integral_const_mul, integral_rpow_mul_exp_neg_div_Ioi ha hr, hpow,
          show δ - n / 2 = n / 2 + (δ - n) by ring, rpow_add pi_pos]
        field_simp

end TauCeti
