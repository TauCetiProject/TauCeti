/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.PDE.HeatKernel.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.ComplexOrder
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import TauCeti.MeasureTheory.Integral.RieszPotential
import TauCeti.MeasureTheory.Integral.RpowLaplace

/-!
# The Bessel kernel and the Sobolev embedding of Bessel-potential spaces

On a finite-dimensional real inner product space `E` of dimension `n`, the Bessel potential
`J^(-δ)`, `δ > 0`, is the Fourier multiplier with symbol `(1 + ‖ξ‖²)^(-δ/2)` in Mathlib's
normalization `𝓕 f(ξ) = ∫ e^(-2πi⟪x, ξ⟫) f(x) dx`. This file identifies it as convolution with an
explicit nonnegative kernel, the **Bessel kernel** `G_δ` (`TauCeti.besselKernel`), and deduces the
Sobolev embedding of the Bessel-potential spaces `H^{s,p} = H^{s,p}(E; F)`:

`H^{s + δ, p} ⊆ H^{s, q}` for `1 < p`, `0 < δ` and `1 / q = 1 / p - δ / n`.

## The Bessel kernel

Euler's Gamma integral gives the subordination formula
`(1 + ‖ξ‖²)^(-δ/2) = (4π²)^(δ/2) Γ(δ/2)⁻¹ ∫₀^∞ t^(δ/2 - 1) e^(-4π² t) e^(-4π² t ‖ξ‖²) dt`.
The heat symbol `e^(-4π² t ‖ξ‖²)` is the
Fourier transform of the heat kernel `K_t` (`TauCeti.heatKernel`), so `J^(-δ)` is convolution with
the same average of heat kernels,

`G_δ(x) = (4π²)^(δ/2) Γ(δ/2)⁻¹ ∫₀^∞ t^(δ/2 - 1) e^(-4π² t) K_t(x) dt`,

first on Schwartz functions (`SchwartzMap.besselPotentialCLM_neg_apply_eq_integral`), by Fubini's
theorem on the Fourier side and in space. Dropping the factor `e^(-4π² t) ≤ 1` and evaluating the
remaining inverted Gamma integral bounds the kernel by the Riesz kernel: for `0 < δ < n`,
`G_δ(x) ≤ C ‖x‖^(δ - n)` (`TauCeti.besselKernel_le`).

## The embedding

By this bound, `|G_δ ⋆ f| ≤ C I_δ |f|` pointwise, where `I_δ` is the Riesz potential of order `δ`,
and the Hardy–Littlewood–Sobolev inequality (`TauCeti.exists_eLpNorm_rieszPotential_le`) bounds
`I_δ` from `Lᵖ` to `L^q`. Pairing with a test function and using Hölder's inequality makes the
convolution integral absolutely convergent, so `J^(-δ) f = G_δ ⋆ f` also for `f ∈ Lᵖ`, as tempered
distributions. Since `J^s = J^(-δ) J^(s + δ)`, this gives the embedding.

## Main declarations

* `TauCeti.besselKernel`: the Bessel kernel `G_δ`, nonnegative and even
  (`TauCeti.besselKernel_nonneg`, `TauCeti.besselKernel_neg`).
* `TauCeti.besselKernel_le`, `TauCeti.exists_enorm_besselKernel_le`: `G_δ(x) ≤ C ‖x‖^(δ - n)`.
* `SchwartzMap.besselPotentialCLM_neg_apply_eq_integral`: `J^(-δ) u = G_δ ⋆ u` on Schwartz
  functions.
* `TemperedDistribution.exists_besselPotential_neg_eq_and_norm_le`: `J^(-δ)` maps `Lᵖ` to `L^q`,
  `1 / q = 1 / p - δ / n`, as convolution with `G_δ`.
* `TemperedDistribution.MemSobolev.of_add_of_inv_eq`: `H^{s + δ, p} ⊆ H^{s, q}`.
* `BesselPotentialSpace.sobolevInclusion`: the same embedding as a continuous linear map.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V,
  §1 (fractional integration) and §3 (Bessel potentials, the kernel as an average of Gaussians);
  the normalization here is adapted to Mathlib's Fourier transform and Bessel potential.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Chapter 1 (Riesz and Bessel potentials,
  Sobolev spaces).
-/

public section

noncomputable section

open MeasureTheory Real Set Module
open scoped ENNReal NNReal FourierTransform SchwartzMap RealInnerProductSpace Convolution

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **Bessel kernel** `G_δ` of order `δ` on a real inner product space `E`, the heat kernel
`K_t` averaged against the Gamma density:

`G_δ(x) = (4π²)^(δ/2) / Γ(δ/2) ∫₀^∞ t^(δ/2 - 1) e^(-4π² t) K_t(x) dt`.

For `0 < δ` it is the kernel of the Bessel potential `J^(-δ)`, the Fourier multiplier with symbol
`(1 + ‖ξ‖²)^(-δ/2)` in Mathlib's normalization of the Fourier transform
(`SchwartzMap.besselPotentialCLM_neg_apply_eq_integral`). For `0 < δ` the integral converges at
every `x ≠ 0`, and at `x = 0` exactly when `δ > dim E`; where it diverges, the value is the junk
value of the Bochner integral. -/
def besselKernel (δ : ℝ) (x : E) : ℝ :=
  (4 * π ^ 2) ^ (δ / 2) / Gamma (δ / 2) *
    ∫ t in Ioi (0 : ℝ), t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * heatKernel t x

/-- The defining formula of the Bessel kernel. -/
theorem besselKernel_apply (δ : ℝ) (x : E) :
    besselKernel δ x = (4 * π ^ 2) ^ (δ / 2) / Gamma (δ / 2) *
      ∫ t in Ioi (0 : ℝ), t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * heatKernel t x :=
  (rfl)

/-- The Bessel kernel is radial; in particular it is even. -/
@[simp]
theorem besselKernel_neg (δ : ℝ) (x : E) : besselKernel δ (-x) = besselKernel δ x := by
  simp [besselKernel_apply]

/-- The Bessel kernel of positive order is nonnegative. -/
theorem besselKernel_nonneg {δ : ℝ} (hδ : 0 < δ) (x : E) : 0 ≤ besselKernel δ x := by
  rw [besselKernel_apply]
  refine mul_nonneg (div_nonneg (by positivity) (Gamma_pos_of_pos (by positivity)).le)
    (setIntegral_nonneg measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_)
  exact mul_nonneg (by positivity) (heatKernel_pos ht x).le

/-- The integrand of the Bessel kernel is at most `(4π)^(-n/2) t^(-((n - δ)/2 + 1)) e^(-‖x‖²/(4t))`,
the integrand of an inverted Gamma integral. -/
private theorem besselKernel_integrand_le {δ : ℝ} {t : ℝ} (ht : 0 < t) (x : E) :
    t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * heatKernel t x ≤
      (4 * π) ^ (-(finrank ℝ E : ℝ) / 2) *
        (t ^ (-((finrank ℝ E - δ) / 2 + 1)) * exp (-((‖x‖ ^ 2 / 4) / t))) := by
  have hexp : exp (-(4 * π ^ 2 * t)) ≤ 1 := exp_le_one_iff.2 (by nlinarith [pi_pos])
  have hpow : t ^ (δ / 2 - 1) * t ^ (-(finrank ℝ E : ℝ) / 2) =
      t ^ (-((finrank ℝ E - δ) / 2 + 1)) := by
    rw [← rpow_add ht]
    ring_nf
  have hgauss : exp (-‖x‖ ^ 2 / (4 * t)) = exp (-((‖x‖ ^ 2 / 4) / t)) := by
    ring_nf
  rw [heatKernel_apply, mul_rpow (by positivity) ht.le, hgauss]
  calc t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) *
        ((4 * π) ^ (-(finrank ℝ E : ℝ) / 2) * t ^ (-(finrank ℝ E : ℝ) / 2) *
          exp (-((‖x‖ ^ 2 / 4) / t)))
      ≤ t ^ (δ / 2 - 1) * 1 *
        ((4 * π) ^ (-(finrank ℝ E : ℝ) / 2) * t ^ (-(finrank ℝ E : ℝ) / 2) *
          exp (-((‖x‖ ^ 2 / 4) / t))) := by gcongr
    _ = _ := by
        rw [mul_one, ← hpow]
        ring

/-- **Size of the Bessel kernel.** For `0 < δ < n = dim E`, the Bessel kernel is bounded by a
multiple of the Riesz kernel: `G_δ(x) ≤ C ‖x‖^(δ - n)` for `x ≠ 0`, with
`C = (4π²)^(δ/2) Γ(δ/2)⁻¹ (4π)^(-n/2) 4^((n - δ)/2) Γ((n - δ)/2)`. -/
theorem besselKernel_le {δ : ℝ} (hδ : 0 < δ) (hδn : δ < finrank ℝ E) {x : E} (hx : x ≠ 0) :
    besselKernel δ x ≤ (4 * π ^ 2) ^ (δ / 2) / Gamma (δ / 2) * (4 * π) ^ (-(finrank ℝ E : ℝ) / 2) *
      (4 ^ ((finrank ℝ E - δ) / 2) * Gamma ((finrank ℝ E - δ) / 2)) *
        ‖x‖ ^ (δ - finrank ℝ E) := by
  set n : ℝ := (finrank ℝ E : ℝ)
  have hb : 0 < (n - δ) / 2 := by linarith
  have hr : 0 < ‖x‖ ^ 2 / 4 := by positivity
  have hint := integrableOn_rpow_mul_exp_neg_div_Ioi hb hr
  have hle : ∫ t in Ioi (0 : ℝ), t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * heatKernel t x ≤
      (4 * π) ^ (-n / 2) * ((1 / (‖x‖ ^ 2 / 4)) ^ ((n - δ) / 2) * Gamma ((n - δ) / 2)) := by
    rw [← integral_rpow_mul_exp_neg_div_Ioi hb hr, ← integral_const_mul]
    exact setIntegral_mono_of_nonneg
      (fun t (ht : 0 < t) ↦ mul_nonneg (by positivity) (heatKernel_pos ht x).le)
      (fun t ht ↦ besselKernel_integrand_le ht x) (hint.const_mul _)
  have hx2 : (1 / (‖x‖ ^ 2 / 4)) ^ ((n - δ) / 2) = 4 ^ ((n - δ) / 2) * ‖x‖ ^ (δ - n) := by
    rw [one_div_div, div_rpow (by norm_num) (by positivity), ← rpow_natCast,
      ← rpow_mul (norm_nonneg _), div_eq_mul_inv, ← rpow_neg (by positivity)]
    congr 2
    push_cast
    ring
  rw [besselKernel_apply]
  calc _ ≤ (4 * π ^ 2) ^ (δ / 2) / Gamma (δ / 2) *
        ((4 * π) ^ (-n / 2) * ((1 / (‖x‖ ^ 2 / 4)) ^ ((n - δ) / 2) * Gamma ((n - δ) / 2))) :=
        mul_le_mul_of_nonneg_left hle
          (div_nonneg (by positivity) (Gamma_pos_of_pos (by positivity)).le)
    _ = _ := by
        rw [hx2]
        ring

/-- The Bessel kernel is measurable. -/
theorem measurable_besselKernel [MeasurableSpace E] [BorelSpace E]
    (δ : ℝ) : Measurable (besselKernel δ : E → ℝ) := by
  have h : StronglyMeasurable fun x : E ↦
      ∫ t in Ioi (0 : ℝ), t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * heatKernel t x :=
    StronglyMeasurable.integral_prod_right (f := fun (x : E) (t : ℝ) ↦
      t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * heatKernel t x)
      (by simp only [heatKernel_apply]; exact (by fun_prop : Measurable _).stronglyMeasurable)
  rw [show (besselKernel δ : E → ℝ) = fun x ↦ (4 * π ^ 2) ^ (δ / 2) / Gamma (δ / 2) *
      ∫ t in Ioi (0 : ℝ), t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * heatKernel t x from
    funext (besselKernel_apply δ)]
  exact h.measurable.const_mul _

/-- **Size of the Bessel kernel, in `ℝ≥0∞`.** For `0 < δ < dim E` there is `C` with
`‖G_δ(x)‖ₑ ≤ C ‖x‖ₑ^(δ - n)` at every point, including `x = 0`, where the right side is `∞`. -/
theorem exists_enorm_besselKernel_le {δ : ℝ} (hδ : 0 < δ) (hδn : δ < finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ x : E, ‖besselKernel δ x‖ₑ ≤ C * ‖x‖ₑ ^ (δ - finrank ℝ E) := by
  set C : ℝ := (4 * π ^ 2) ^ (δ / 2) / Gamma (δ / 2) * (4 * π) ^ (-(finrank ℝ E : ℝ) / 2) *
      (4 ^ ((finrank ℝ E - δ) / 2) * Gamma ((finrank ℝ E - δ) / 2))
  have hC : 0 < C := by
    have := Gamma_pos_of_pos (half_pos hδ)
    have := Gamma_pos_of_pos (show 0 < ((finrank ℝ E : ℝ) - δ) / 2 by linarith)
    positivity
  refine ⟨C.toNNReal, fun x ↦ ?_⟩
  rw [ENNReal.ofNNReal_toNNReal]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [eNorm_zero, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hC).ne']
    exact le_top
  rw [Real.eNorm_eq_ofReal (besselKernel_nonneg hδ x), ← ofReal_norm,
    ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 hx), ← ENNReal.ofReal_mul hC.le]
  exact ENNReal.ofReal_le_ofReal (besselKernel_le hδ hδn hx)

/-! ### The Bessel kernel as the kernel of `J^(-δ)` -/

omit [InnerProductSpace ℝ E] in
/-- **Subordination.** The Bessel symbol `(1 + ‖ξ‖²)^(-δ/2)` is the average of the heat symbols
`exp(-4π² t ‖ξ‖²)` against the Gamma density defining the Bessel kernel. -/
private theorem one_add_norm_sq_rpow_neg_eq_integral {δ : ℝ} (hδ : 0 < δ) (ξ : E) :
    (1 + ‖ξ‖ ^ 2) ^ (-δ / 2) = (4 * π ^ 2) ^ (δ / 2) / Gamma (δ / 2) *
      ∫ t in Ioi (0 : ℝ), t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) *
        exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) := by
  have hr : 0 < 4 * π ^ 2 * (1 + ‖ξ‖ ^ 2) := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun t ↦ t ^ (δ / 2 - 1) * exp (-((4 * π ^ 2 * (1 + ‖ξ‖ ^ 2)) * t)))
      fun t _ ↦ by rw [mul_assoc, ← exp_add]; ring_nf,
    integral_rpow_mul_exp_neg_mul_Ioi (half_pos hδ) hr, one_div, inv_rpow hr.le,
    mul_rpow (x := 4 * π ^ 2) (y := 1 + ‖ξ‖ ^ 2) (by positivity) (by positivity), neg_div,
    rpow_neg (by positivity)]
  have hΓ : Gamma (δ / 2) ≠ 0 := (Gamma_pos_of_pos (half_pos hδ)).ne'
  have h4 : (4 * π ^ 2) ^ (δ / 2) ≠ 0 := (rpow_pos_of_pos (by positivity) _).ne'
  field_simp

/-- The Gamma density `t^(δ/2 - 1) e^(-4π² t)` of the Bessel kernel is integrable. -/
private theorem integrableOn_besselWeight {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ ↦ t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t))) (Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_mul_Ioi (half_pos hδ) (by positivity)

end TauCeti

namespace SchwartzMap

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The heat multiplier with symbol `exp(-4π² t ‖ξ‖²)`, written as an inverse Fourier integral, is
convolution with the heat kernel `K_t`. -/
private theorem integral_fourierChar_smul_exp_smul_fourier_eq {t : ℝ} (ht : 0 < t)
    (u : 𝓢(E, F)) (x : E) :
    ∫ ξ, 𝐞 ⟪ξ, x⟫ • ((exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℂ) • 𝓕 u ξ) =
      ∫ y, heatKernel t (x - y) • u y := by
  have hb : 0 < ((4 * π ^ 2 * t : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    positivity
  have hK : 𝓕⁻ (gaussian (V := E) hb : E → ℂ) = fun x ↦ (heatKernel t x : ℂ) := by
    rw [coe_gaussian_ofReal, fourierInv_exp_neg_mul_norm_sq ht]
  have h := fourierMultiplierCLM_apply_eq_integral (gaussian (V := E) hb) u x
  simp only [fourierInv_coe] at h
  rw [hK, fourierMultiplierCLM_apply, fourierInv_coe, Real.fourierInv_eq] at h
  simp only [smulLeftCLM_apply_apply (gaussian hb).hasTemperateGrowth] at h
  simpa only [coe_gaussian_ofReal, Complex.coe_smul] using h

/-- The integrand of the Bessel multiplier on the Fourier side, split along the Gamma density
`w(t) = t^(δ/2 - 1) e^(-4π² t)`: `(t, ξ) ↦ w(t) e^(2πi⟪ξ, x⟫) exp(-4π² t ‖ξ‖²) 𝓕 u(ξ)`. Its norm
is at most `w(t) ‖𝓕 u(ξ)‖`. -/
private theorem integrable_besselFourierIntegrand {δ : ℝ} (hδ : 0 < δ) (u : 𝓢(E, F)) (x : E) :
    Integrable (fun z : ℝ × E ↦ (z.1 ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * z.1))) •
        (𝐞 ⟪z.2, x⟫ • ((exp (-(4 * π ^ 2 * z.1 * ‖z.2‖ ^ 2)) : ℂ) • 𝓕 u z.2)))
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hw := integrableOn_besselWeight hδ
  have hm : AEStronglyMeasurable (fun z : ℝ × E ↦ (z.1 ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * z.1)))
      • (𝐞 ⟪z.2, x⟫ • ((exp (-(4 * π ^ 2 * z.1 * ‖z.2‖ ^ 2)) : ℂ) • 𝓕 u z.2)))
      ((volume.restrict (Ioi 0)).prod volume) := by
    refine ((by fun_prop : Measurable fun z : ℝ × E ↦
      z.1 ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * z.1))).aestronglyMeasurable).smul
      (Continuous.aestronglyMeasurable ?_)
    fun_prop
  refine (hw.mul_prod (𝓕 u).integrable.norm).mono' hm ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)]
    with z (hz : 0 < z.1)
  have hexp : exp (-(4 * π ^ 2 * z.1 * ‖z.2‖ ^ 2)) ≤ 1 :=
    exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
  rw [norm_smul, Circle.norm_smul, norm_smul, Complex.norm_real, norm_of_nonneg (by positivity),
    norm_of_nonneg (exp_pos _).le]
  gcongr
  exact mul_le_of_le_one_left (norm_nonneg _) hexp

/-- The integrand of the Bessel kernel convolution, split along the Gamma density
`w(t) = t^(δ/2 - 1) e^(-4π² t)`: `(t, y) ↦ w(t) K_t(x - y) u(y)`. For `t > 0` its `y`-integral of
norms is at most `w(t) sup ‖u‖`. -/
private theorem integrable_besselSpaceIntegrand {δ : ℝ} (hδ : 0 < δ) (u : 𝓢(E, F)) (x : E) :
    Integrable (fun z : ℝ × E ↦
        (z.1 ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * z.1)) * heatKernel z.1 (x - z.2)) • u z.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hw := integrableOn_besselWeight hδ
  have hm : AEStronglyMeasurable (fun z : ℝ × E ↦
      (z.1 ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * z.1)) * heatKernel z.1 (x - z.2)) • u z.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
    refine ((by simp only [heatKernel_apply]; fun_prop : Measurable fun z : ℝ × E ↦
      z.1 ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * z.1)) * heatKernel z.1 (x - z.2)
      ).aestronglyMeasurable).smul (u.continuous.comp continuous_snd).aestronglyMeasurable
  set S : ℝ := SchwartzMap.seminorm ℝ 0 0 u
  rw [integrable_prod_iff hm]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    exact (((integrable_heatKernel ht).comp_sub_left x).const_mul _).smul_of_top_left
      (u.memLp ⊤)
  · refine (hw.mul_const S).mono' hm.norm.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    have hK : Integrable fun y : E ↦ heatKernel t (x - y) :=
      (integrable_heatKernel ht).comp_sub_left x
    rw [norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    calc ∫ y, ‖(t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * heatKernel t (x - y)) • u y‖
        ≤ ∫ y, t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * S * heatKernel t (x - y) := by
          refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
            (hK.const_mul _) (.of_forall fun y ↦ ?_)
          dsimp only
          rw [norm_smul, norm_of_nonneg (mul_nonneg (by positivity) (heatKernel_pos ht _).le)]
          have := norm_le_seminorm ℝ u y
          calc _ ≤ t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * heatKernel t (x - y) * S := by
                gcongr
                exact mul_nonneg (by positivity) (heatKernel_pos ht _).le
            _ = _ := by ring
      _ = t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * S := by
          rw [integral_const_mul, integral_sub_left_eq_self (fun y ↦ heatKernel t y) volume x,
            integral_heatKernel ht, mul_one]

variable [CompleteSpace F]

/-- **`J^(-δ)` is convolution with the Bessel kernel.** For `0 < δ` and a Schwartz function `u`,
the Bessel potential `J^(-δ)`, the Fourier multiplier with symbol `(1 + ‖ξ‖²)^(-δ/2)`, is
`J^(-δ) u (x) = ∫ G_δ(x - y) u(y) dy`. -/
theorem besselPotentialCLM_neg_apply_eq_integral {δ : ℝ} (hδ : 0 < δ) (u : 𝓢(E, F)) (x : E) :
    besselPotentialCLM ((-δ : ℝ) : ℂ) u x = ∫ y, besselKernel δ (x - y) • u y := by
  set c : ℝ := (4 * π ^ 2) ^ (δ / 2) / Gamma (δ / 2)
  -- On the Fourier side, the symbol is the Gamma average of the heat symbols.
  have hA : besselPotentialCLM ((-δ : ℝ) : ℂ) u x = c • ∫ t in Ioi (0 : ℝ),
      ∫ ξ, (t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t))) •
        (𝐞 ⟪ξ, x⟫ • ((exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℂ) • 𝓕 u ξ)) := by
    rw [integral_integral_swap (integrable_besselFourierIntegrand hδ u x), ← integral_smul,
      besselPotentialCLM_ofReal, fourierMultiplierCLM_apply, fourierInv_coe, Real.fourierInv_eq]
    refine integral_congr_ae (.of_forall fun ξ ↦ ?_)
    have hI : ∫ t in Ioi (0 : ℝ), (t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t))) •
          (𝐞 ⟪ξ, x⟫ • ((exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℂ) • 𝓕 u ξ)) =
        (∫ t in Ioi (0 : ℝ), t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) *
          exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2))) • (𝐞 ⟪ξ, x⟫ • 𝓕 u ξ) := by
      rw [← integral_smul_const]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
      simp only [Circle.smul_def, ← Complex.coe_smul, smul_smul]
      push_cast
      ring_nf
    dsimp only
    rw [hI, smul_smul, ← one_add_norm_sq_rpow_neg_eq_integral hδ ξ,
      smulLeftCLM_apply_apply (by fun_prop)]
    simp only [Circle.smul_def, ← Complex.coe_smul, smul_smul, mul_comm]
  -- In space, the Bessel kernel is the Gamma average of the heat kernels.
  have hB : ∫ y, besselKernel δ (x - y) • u y = c • ∫ t in Ioi (0 : ℝ), ∫ y,
      (t ^ (δ / 2 - 1) * exp (-(4 * π ^ 2 * t)) * heatKernel t (x - y)) • u y := by
    rw [integral_integral_swap (integrable_besselSpaceIntegrand hδ u x), ← integral_smul]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    dsimp only
    rw [besselKernel_apply, integral_smul_const, smul_smul]
  rw [hA, hB]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  rw [integral_smul, integral_fourierChar_smul_exp_smul_fourier_eq ht, ← integral_smul]
  simp_rw [smul_smul]

end SchwartzMap

namespace TemperedDistribution

open TauCeti ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [NormedSpace ℂ F] in
/-- A bound `‖G_δ(x)‖ₑ ≤ C ‖x‖ₑ^(δ - n)` dominates convolution with the Bessel kernel by the Riesz
potential of order `δ`. -/
private theorem lintegral_enorm_besselKernel_sub_mul_le {δ : ℝ} {C : ℝ≥0}
    (hC : ∀ x : E, ‖besselKernel δ x‖ₑ ≤ C * ‖x‖ₑ ^ (δ - finrank ℝ E)) (f : E → F) (x : E) :
    ∫⁻ y, ‖besselKernel δ (x - y)‖ₑ * ‖f y‖ₑ ≤ C * rieszPotential volume δ f x := by
  rw [rieszPotential_def, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun y ↦ ?_
  rw [← mul_assoc]
  gcongr
  exact hC _

/-- The integrand `(y, x) ↦ (G_δ(y - x) φ(x)) • f(y)` of the pairing of `J^(-δ) f` with a test
function is integrable on `E × E` when the Riesz potential of `f` lies in `L^q`, `1 ≤ q`: its
`y`-integral is at most `‖φ(x)‖` times a multiple of that potential, and Hölder's inequality pairs
`L^q` with the conjugate space, which contains `φ`. -/
private theorem integrable_besselKernel_sub_smul_smul {δ : ℝ} {C : ℝ≥0}
    (hC : ∀ x : E, ‖besselKernel δ x‖ₑ ≤ C * ‖x‖ₑ ^ (δ - finrank ℝ E)) {q : ℝ≥0∞}
    [hq : Fact (1 ≤ q)] {f : E → F} (hf : AEStronglyMeasurable f volume)
    (hI : eLpNorm (rieszPotential volume δ f) q volume ≠ ∞) (φ : 𝓢(E, ℂ)) :
    Integrable (fun z : E × E ↦ (besselKernel δ (z.1 - z.2) • φ z.2) • f z.1)
      ((volume : Measure E).prod volume) := by
  have hm : AEStronglyMeasurable (fun z : E × E ↦ (besselKernel δ (z.1 - z.2) • φ z.2) • f z.1)
      ((volume : Measure E).prod volume) :=
    (((measurable_besselKernel δ).comp
      (measurable_fst.sub measurable_snd)).aestronglyMeasurable.smul
      (φ.continuous.comp continuous_snd).aestronglyMeasurable).smul hf.comp_fst
  refine ⟨hm, ?_⟩
  set I := rieszPotential volume δ f
  have hIm : AEMeasurable I volume := aemeasurable_rieszPotential hf.eNorm
  -- Hölder's inequality with the conjugate exponent `q'` of `q`.
  set q' : ℝ≥0∞ := (1 - q⁻¹)⁻¹
  have hqq' : q.HolderConjugate q' := ENNReal.HolderConjugate.inv_one_sub_inv' hq.out
  have hHolder : ∫⁻ x, I x * ‖φ x‖ₑ ≤ eLpNorm I q volume * eLpNorm φ q' volume := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_eNorm (p := q) (q := q') (r := 1)
      (fun (i : ℝ≥0∞) (v : ℂ) ↦ i * ‖v‖ₑ) 1
      (fun hI hφ ↦ (hI.aemeasurable.mul hφ.eNorm).aestronglyMeasurable) hIm.aestronglyMeasurable
      φ.continuous.aestronglyMeasurable (.of_forall fun _ ↦ by simp)
    have hm' : AEStronglyMeasurable (fun x ↦ I x * ‖φ x‖ₑ) volume :=
      (hIm.mul φ.continuous.eNorm.aemeasurable).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_eNorm hm', one_mul] at h
    simpa only [eNorm_eq_self] using h
  rw [HasFiniteIntegral, lintegral_prod_symm _ hm.eNorm]
  calc ∫⁻ x, ∫⁻ y, ‖(besselKernel δ (y - x) • φ x) • f y‖ₑ
      = ∫⁻ x, ‖φ x‖ₑ * ∫⁻ y, ‖besselKernel δ (x - y)‖ₑ * ‖f y‖ₑ := by
        refine lintegral_congr fun x ↦ ?_
        rw [← lintegral_const_mul' _ _ eNorm_ne_top]
        refine lintegral_congr fun y ↦ ?_
        rw [eNorm_smul, eNorm_smul, ← neg_sub, besselKernel_neg]
        ring
    _ ≤ ∫⁻ x, ‖φ x‖ₑ * (C * I x) := by
        gcongr with x
        exact lintegral_enorm_besselKernel_sub_mul_le hC f x
    _ = C * ∫⁻ x, I x * ‖φ x‖ₑ := by
        rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
        exact lintegral_congr fun x ↦ by ring
    _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (hHolder.trans_lt
        (ENNReal.mul_lt_top hI.lt_top (φ.eLpNorm_lt_top q' volume)))

variable [CompleteSpace F]

/-- The pairing of `J^(-δ) f` with a test function `φ`, for `f` whose Riesz potential of order `δ`
lies in `L^q`, is the pairing of `φ` with the convolution `G_δ ⋆ f`. -/
private theorem besselPotential_neg_toTemperedDistribution_apply {δ : ℝ} (hδ : 0 < δ)
    {C : ℝ≥0} (hC : ∀ x : E, ‖besselKernel δ x‖ₑ ≤ C * ‖x‖ₑ ^ (δ - finrank ℝ E))
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (f : Lp F p (volume : Measure E))
    (hI : eLpNorm (rieszPotential volume δ (f : E → F)) q volume ≠ ∞) (φ : 𝓢(E, ℂ)) :
    besselPotential E F (-δ) (f : 𝓢'(E, F)) φ =
      ∫ x, φ x • ∫ y, besselKernel δ (x - y) • f y := by
  rw [besselPotential, fourierMultiplierCLM_apply_apply,
    SchwartzMap.fourier_smulLeftCLM_fourierInv_eq (by fun_prop), Lp.toTemperedDistribution_apply]
  simp only [norm_neg]
  rw [← SchwartzMap.besselPotentialCLM_ofReal]
  simp_rw [SchwartzMap.besselPotentialCLM_neg_apply_eq_integral hδ]
  calc ∫ y, (∫ x, besselKernel δ (y - x) • φ x) • f y
      = ∫ y, ∫ x, (besselKernel δ (y - x) • φ x) • f y := by simp_rw [integral_smul_const]
    _ = ∫ x, ∫ y, (besselKernel δ (y - x) • φ x) • f y :=
        integral_integral_swap
          (integrable_besselKernel_sub_smul_smul hC (Lp.aestronglyMeasurable f) hI φ)
    _ = ∫ x, φ x • ∫ y, besselKernel δ (x - y) • f y := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [← integral_smul]
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        dsimp only
        rw [← neg_sub, besselKernel_neg, smul_assoc, smul_comm]

omit [MeasurableSpace E] [BorelSpace E] in
/-- In positive dimension the exponent relation `1 / q = 1 / p - δ / n` with `1 ≤ q` and `1 < p`
forces `δ < n`. -/
private theorem lt_finrank_of_inv_eq [Nontrivial E] {δ : ℝ} {p q : ℝ≥0} (hq : 1 ≤ (q : ℝ≥0∞))
    (hp : 1 < p) (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / finrank ℝ E) : δ < finrank ℝ E := by
  have hn : (0 : ℝ) < finrank ℝ E := by exact_mod_cast finrank_pos
  have hq0 : (0 : ℝ) < (q : ℝ)⁻¹ :=
    inv_pos.2 (zero_lt_one.trans_le (by exact_mod_cast ENNReal.one_le_coe_iff.1 hq))
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp)
  rw [← div_lt_one hn]
  linarith

/-- **The Hardy–Littlewood–Sobolev theorem for Bessel potentials.** On a space `E` of positive
dimension `n`, for `0 < δ`, `1 < p` and `1 / q = 1 / p - δ / n` (so that `δ < n / p`), the
Bessel potential `J^(-δ)` maps `Lᵖ(E; F)` boundedly to `L^q(E; F)`: for `f ∈ Lᵖ` the tempered
distribution `J^(-δ) f` is the `L^q` function `G_δ ⋆ f`, with `‖J^(-δ) f‖_q ≤ C ‖f‖_p` for a
constant `C` independent of `f`. -/
theorem exists_besselPotential_neg_eq_and_norm_le [Nontrivial E] {δ : ℝ} (hδ : 0 < δ)
    {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    (hp : 1 < p) (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / finrank ℝ E) :
    ∃ C : ℝ, ∀ f : Lp F p (volume : Measure E), ∃ g : Lp F q (volume : Measure E),
      besselPotential E F (-δ) (f : 𝓢'(E, F)) = g ∧
        g =ᵐ[volume] besselKernel δ ⋆[lsmul ℝ ℝ] (f : E → F) ∧ ‖g‖ ≤ C * ‖f‖ := by
  obtain ⟨K, hK⟩ := exists_enorm_besselKernel_le (E := E) hδ
    (lt_finrank_of_inv_eq (E := E) Fact.out hp hpq)
  obtain ⟨H, hH⟩ := exists_eLpNorm_rieszPotential_le (F := F) (volume : Measure E) hδ hp hpq
  refine ⟨K * H, fun f ↦ ?_⟩
  set h : E → F := fun x ↦ ∫ y, besselKernel δ (x - y) • f y
  have hconv : besselKernel δ ⋆[lsmul ℝ ℝ] (f : E → F) = h := funext fun x ↦ by
    simp only [convolution_eq_swap, lsmul_apply, h]
  have hIfin : eLpNorm (rieszPotential volume δ (f : E → F)) q volume ≠ ∞ :=
    ((hH f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (Lp.eLpNorm_lt_top f))).ne
  have hmeas : AEStronglyMeasurable h volume :=
    (((measurable_besselKernel δ).comp
      (measurable_fst.sub measurable_snd)).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f).comp_snd).integral_prod_right'
  -- Pointwise, `G_δ ⋆ f` is dominated by a multiple of the Riesz potential of `f`.
  have hbound : eLpNorm h q volume ≤ K * (H * eLpNorm f p volume) := by
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hmeas (.of_forall fun x ↦ ?_) _).trans
      (by gcongr; exact hH f)
    rw [eNorm_eq_self]
    refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
    simp_rw [eNorm_smul]
    exact lintegral_enorm_besselKernel_sub_mul_le hK f x
  have hfin : K * (H * eLpNorm f p volume) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_lt_top f).ne)
  have hmem : MemLp h q volume := memLp_iff.2 (lt_of_le_of_lt hbound (Ne.lt_top hfin))
  refine ⟨hmem.toLp h, ?_, by rw [hconv]; exact hmem.coeFn_toLp, ?_⟩
  · ext φ
    rw [besselPotential_neg_toTemperedDistribution_apply hδ hK f hIfin,
      Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx]
  · rw [Lp.norm_toLp, Lp.norm_def]
    calc (eLpNorm h q volume).toReal ≤ (K * (H * eLpNorm f p volume)).toReal :=
          ENNReal.toReal_mono hfin hbound
      _ = K * H * (eLpNorm f p volume).toReal := by
          simp [ENNReal.toReal_mul, mul_assoc]

/-- **Sobolev embedding of Bessel-potential spaces.** On a space of positive dimension `n`, for
`0 < δ`, `1 < p` and `1 / q = 1 / p - δ / n`, every tempered distribution in `H^{s + δ, p}` lies in
`H^{s, q}`. -/
theorem MemSobolev.of_add_of_inv_eq [Nontrivial E] {s δ : ℝ} (hδ : 0 < δ) {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hp : 1 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / finrank ℝ E) {f : 𝓢'(E, F)}
    (hf : MemSobolev (s + δ) p f) : MemSobolev s q f := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨C, hC⟩ := exists_besselPotential_neg_eq_and_norm_le (F := F) hδ hp hpq
  obtain ⟨g, hg, -, -⟩ := hC f'
  refine ⟨g, ?_⟩
  rw [← hg, ← hf', besselPotential_besselPotential_apply, add_neg_cancel_right]

end TemperedDistribution

namespace BesselPotentialSpace

open TauCeti TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {s δ : ℝ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]

/-- The Bessel potential of order `s` of an element of `H^{s + δ, p}` is an `L^q` function, with a
bound uniform in the element. -/
private theorem exists_besselPotential_toDistr_eq_and_norm_le [Nontrivial E] (hδ : 0 < δ)
    (hp : 1 < p) (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / finrank ℝ E) :
    ∃ C : ℝ, ∀ u : H^{s + δ, p}(E, F), ∃ g : Lp F q (volume : Measure E),
      besselPotential E F s u.toDistr = g ∧ ‖g‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC⟩ := exists_besselPotential_neg_eq_and_norm_le (F := F) hδ hp hpq
  refine ⟨C, fun u ↦ ?_⟩
  obtain ⟨g, hg, -, hgn⟩ := hC u.toLp
  refine ⟨g, ?_, by rwa [norm_toLp_eq] at hgn⟩
  rw [← hg, ← u.bessel_toDistr_eq_toLp, besselPotential_besselPotential_apply,
    add_neg_cancel_right]

/-- **The Sobolev embedding** `H^{s + δ, p}(E, F) → H^{s, q}(E, F)` on a space of positive
dimension `n`, for `0 < δ`, `1 < p` and `1 / q = 1 / p - δ / n`, as a continuous linear map. It
keeps the underlying tempered distribution (`BesselPotentialSpace.toDistr_sobolevInclusion`). -/
def sobolevInclusion [Nontrivial E] (hδ : 0 < δ) (hp : 1 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / finrank ℝ E) :
    H^{s + δ, p}(E, F) →L[ℂ] H^{s, q}(E, F) :=
  let hC := exists_besselPotential_toDistr_eq_and_norm_le (s := s) (F := F) hδ hp hpq
  LinearMap.mkContinuous
    { toFun := fun u ↦
        { toDistr := u.toDistr
          toLp := (hC.choose_spec u).choose
          bessel_toDistr_eq_toLp := (hC.choose_spec u).choose_spec.1 }
      map_add' := fun u v ↦ ext (toDistr_add u v)
      map_smul' := fun c u ↦ ext (toDistr_smul c u) }
    hC.choose fun u ↦ (norm_toLp_eq _).symm.trans_le (hC.choose_spec u).choose_spec.2

/-- The Sobolev embedding keeps the underlying tempered distribution. -/
@[simp]
theorem toDistr_sobolevInclusion [Nontrivial E] (hδ : 0 < δ) (hp : 1 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / finrank ℝ E) (u : H^{s + δ, p}(E, F)) :
    (sobolevInclusion hδ hp hpq u).toDistr = u.toDistr :=
  (rfl)

end BesselPotentialSpace
