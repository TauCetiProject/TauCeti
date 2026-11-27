/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic

/-!
# Poisson and Schwarz integrals of functions on the upper half-plane

For a complex function `h` on `ℝ` that is integrable for the Poisson measure
`Π = dx / (1 + x ^ 2)`, the **Poisson integral** `P[h](z) = ∫ P(z, x) h(x) dx` is defined on the
upper half-plane `ℂ₊`: the measure `|h(x)| dx` is Poisson-finite. Its real and imaginary parts are
the Poisson integrals of the real and imaginary parts of `h`, and for a nonnegative `h` it is the
Poisson integral of the measure `h dx`.

The **Schwarz integral** of `h` is
`S[h](z) = (1 / (π i)) ∫ (1 / (x - z) - x / (1 + x ^ 2)) h(x) dx`, and for `h ∈ L¹(ℝ)` the
Schwarz integral **normalized at infinity** is
`S⁰[h](z) = (1 / (π i)) ∫ h(x) / (x - z) dx`. Off the real axis `S[h]` converges for
`h ∈ L¹(Π)`, and for a real `h` its real part is `P[h]`. For a nonnegative `h` it is the Schwarz
integral of the measure `h dx`. Off the real axis both integrals converge for `h ∈ L¹(ℝ)`, and they
differ by the imaginary constant
`S⁰[h] - S[h] = -(i / π) ∫ x h(x) / (1 + x ^ 2) dx`.

The Cayley transform `z ↦ (z - i) / (z + i)` carries `ℂ₊` to the unit disc and `ℝ` to the unit
circle minus `1`. Under it the half-plane Poisson kernel is the disc Poisson kernel times `1 / π`
times the density of the Poisson measure:
`P(z, x) = poissonKernel 0 w ζ / (π (1 + x ^ 2))` with `w = (z - i) / (z + i)` and
`ζ = (x - i) / (x + i)`, where Mathlib's `poissonKernel 0 w ζ = (|ζ| ^ 2 - |w| ^ 2) / |ζ - w| ^ 2`.

## Main declarations

* `TauCeti.upperHalfPlanePoissonIntegralFun`: the Poisson integral `P[h]` of a complex function.
* `TauCeti.upperHalfPlanePoissonIntegralFun_const`: `P[c] = c` on the upper half-plane.
* `TauCeti.enorm_upperHalfPlanePoissonIntegralFun_le`: `P[h]` is dominated by the Poisson integral
  of the measure `|h| dx`.
* `TauCeti.integrable_upperHalfPlanePoissonKernel_smul`: for `h ∈ L¹(Π)` the integrand of `P[h]` is
  integrable.
* `TauCeti.re_upperHalfPlanePoissonIntegralFun`, `TauCeti.im_upperHalfPlanePoissonIntegralFun`:
  `P[h]` is taken componentwise.
* `TauCeti.upperHalfPlanePoissonIntegralFun_eq_upperHalfPlanePoissonIntegral_withDensity`: for a
  nonnegative `h`, `P[h]` is the Poisson integral of the measure `h dx`.
* `TauCeti.upperHalfPlaneSchwarzIntegralFun`,
  `TauCeti.upperHalfPlaneSchwarzIntegralFunNormalized`: the Schwarz integrals `S[h]` and `S⁰[h]`
  of a complex function.
* `TauCeti.integrable_subtractedResolventKernel_mul`: for `h ∈ L¹(Π)` the integrand of `S[h]` is
  integrable off the real axis.
* `TauCeti.re_upperHalfPlaneSchwarzIntegralFun`: `Re S[h] = P[h]` for a real `h ∈ L¹(Π)`.
* `TauCeti.upperHalfPlaneSchwarzIntegralFun_eq_upperHalfPlaneSchwarzIntegral_withDensity`: for a
  nonnegative `h`, `S[h]` is the Schwarz integral of the measure `h dx`.
* `TauCeti.upperHalfPlaneSchwarzIntegralFunNormalized_sub_upperHalfPlaneSchwarzIntegralFun`:
  `S⁰[h] - S[h] = -(i / π) ∫ x h(x) / (1 + x ^ 2) dx` for `h ∈ L¹(ℝ)`.
* `TauCeti.upperHalfPlanePoissonKernel_eq_poissonKernel_cayley`: the Cayley comparison of the
  half-plane and disc Poisson kernels.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. **200**
  (2024), Section 2.
-/

public section

noncomputable section

open Complex MeasureTheory

open scoped Real ENNReal NNReal

namespace TauCeti

/-! ### The Poisson integral of a function -/

/-- The **Poisson integral** `P[h](z) = ∫ P(z, x) h(x) dx` of a complex function `h` on `ℝ`. It is
meaningful for `h` integrable for the Poisson measure `dx / (1 + x ^ 2)`
(`TauCeti.integrable_upperHalfPlanePoissonKernel_smul`); its real and imaginary parts are the
Poisson integrals of the real and imaginary parts of `h`
(`TauCeti.re_upperHalfPlanePoissonIntegralFun`, `TauCeti.im_upperHalfPlanePoissonIntegralFun`). -/
def upperHalfPlanePoissonIntegralFun (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x, upperHalfPlanePoissonKernel z x • h x

/-- The defining formula of `TauCeti.upperHalfPlanePoissonIntegralFun`. -/
theorem upperHalfPlanePoissonIntegralFun_def (h : ℝ → ℂ) (z : ℂ) :
    upperHalfPlanePoissonIntegralFun h z = ∫ x, upperHalfPlanePoissonKernel z x • h x := by
  rw [upperHalfPlanePoissonIntegralFun]

/-- Poisson integrals of almost everywhere equal functions agree. -/
theorem upperHalfPlanePoissonIntegralFun_congr_ae {h g : ℝ → ℂ} (hhg : h =ᵐ[volume] g) (z : ℂ) :
    upperHalfPlanePoissonIntegralFun h z = upperHalfPlanePoissonIntegralFun g z := by
  rw [upperHalfPlanePoissonIntegralFun_def, upperHalfPlanePoissonIntegralFun_def]
  exact integral_congr_ae (hhg.mono fun x hx ↦ congrArg _ hx)

/-- **The Poisson integral reproduces constants**: `P[c](z) = c` on the upper half-plane. -/
theorem upperHalfPlanePoissonIntegralFun_const (c : ℂ) {z : ℂ} (hz : 0 < z.im) :
    upperHalfPlanePoissonIntegralFun (fun _ ↦ c) z = c := by
  rw [upperHalfPlanePoissonIntegralFun_def, integral_smul_const,
    integral_upperHalfPlanePoissonKernel hz, one_smul]

/-- For `h` integrable for the Poisson measure, the measure `|h(x)| dx` is Poisson-finite. -/
theorem isPoissonFinite_withDensity_enorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ → E} (hh : Integrable h upperHalfPlanePoissonMeasure) :
    IsPoissonFinite (volume.withDensity fun x ↦ ‖h x‖ₑ) := by
  simp_rw [isPoissonFinite_iff, eNorm_eq_nnNorm]
  rw [integrable_withDensity_iff_integrable_smul₀
      (aestronglyMeasurable_of_integrable_upperHalfPlanePoissonMeasure hh).nnNorm.aemeasurable]
  refine (integrable_upperHalfPlanePoissonMeasure_iff_integrable_smul.1 hh).norm.congr
    (.of_forall fun x ↦ ?_)
  dsimp only
  rw [norm_smul, Real.norm_of_nonneg (by positivity), NNReal.smul_def, smul_eq_mul, coe_nnNorm,
    mul_comm]

/-- **`P[h]` is dominated by the Poisson integral of `|h| dx`.** On the open upper half-plane,
`‖P[h](z)‖ₑ ≤ ∫ P(z, x) |h(x)| dx`. -/
theorem enorm_upperHalfPlanePoissonIntegralFun_le (h : ℝ → ℂ) {z : ℂ} (hz : 0 < z.im) :
    ‖upperHalfPlanePoissonIntegralFun h z‖ₑ ≤
      upperHalfPlanePoissonLIntegral (volume.withDensity fun s => ‖h s‖ₑ) z := by
  by_cases hint : Integrable fun s => upperHalfPlanePoissonKernel z s • h s
  · -- `h` is recovered from the integrand by dividing by the positive kernel.
    have hmeas : AEStronglyMeasurable h := by
      refine (((measurable_upperHalfPlanePoissonKernel z).inv.aestronglyMeasurable).smul
        hint.aestronglyMeasurable).congr (.of_forall fun s => ?_)
      simp only [Pi.smul_apply', Pi.inv_apply]
      rw [smul_smul, inv_mul_cancel₀ (upperHalfPlanePoissonKernel_pos hz s).ne', one_smul]
    rw [upperHalfPlanePoissonIntegralFun_def,
      upperHalfPlanePoissonLIntegral_withDensity hmeas.eNorm]
    refine (eNorm_integral_le_lintegral_eNorm _).trans_eq (lintegral_congr fun s => ?_)
    rw [eNorm_smul, Real.eNorm_of_nonneg (upperHalfPlanePoissonKernel_nonneg hz.le s), mul_comm]
  · rw [upperHalfPlanePoissonIntegralFun_def, integral_undef hint, eNorm_zero]
    exact zero_le

/-- **The Poisson integral of an `L¹(Π)` function converges**: for `h` integrable for the Poisson
measure, `x ↦ P(z, x) h(x)` is integrable for every pole `z`. -/
theorem integrable_upperHalfPlanePoissonKernel_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {h : ℝ → E} (hh : Integrable h upperHalfPlanePoissonMeasure) (z : ℂ) :
    Integrable fun x ↦ upperHalfPlanePoissonKernel z x • h x :=
  integrable_smul_of_integrable_withDensity_enorm
    ((isPoissonFinite_withDensity_enorm hh).integrable_upperHalfPlanePoissonKernel z)
    (measurable_upperHalfPlanePoissonKernel z).aestronglyMeasurable
    (aestronglyMeasurable_of_integrable_upperHalfPlanePoissonMeasure hh)

/-- **The Poisson integral of a difference**: `P[h - g] = P[h] - P[g]` for `h, g ∈ L¹(Π)`. -/
theorem upperHalfPlanePoissonIntegralFun_sub {h g : ℝ → ℂ}
    (hh : Integrable h upperHalfPlanePoissonMeasure)
    (hg : Integrable g upperHalfPlanePoissonMeasure) (z : ℂ) :
    upperHalfPlanePoissonIntegralFun (fun s => h s - g s) z =
      upperHalfPlanePoissonIntegralFun h z - upperHalfPlanePoissonIntegralFun g z := by
  simp only [upperHalfPlanePoissonIntegralFun_def, smul_sub]
  exact integral_sub (integrable_upperHalfPlanePoissonKernel_smul hh z)
    (integrable_upperHalfPlanePoissonKernel_smul hg z)

/-- The Poisson integral of `h - c` is `P[h] - c` on the upper half-plane, for `h ∈ L¹(Π)`. -/
theorem upperHalfPlanePoissonIntegralFun_sub_const {h : ℝ → ℂ}
    (hh : Integrable h upperHalfPlanePoissonMeasure) (c : ℂ) {z : ℂ} (hz : 0 < z.im) :
    upperHalfPlanePoissonIntegralFun (fun s => h s - c) z =
      upperHalfPlanePoissonIntegralFun h z - c := by
  rw [upperHalfPlanePoissonIntegralFun_sub hh (integrable_const c),
    upperHalfPlanePoissonIntegralFun_const c hz]

/-- The real part of `P[h]` is the Poisson integral of the real part of `h`. -/
theorem re_upperHalfPlanePoissonIntegralFun {h : ℝ → ℂ}
    (hh : Integrable h upperHalfPlanePoissonMeasure) (z : ℂ) :
    (upperHalfPlanePoissonIntegralFun h z).re =
      ∫ x, upperHalfPlanePoissonKernel z x * (h x).re := by
  have := integral_re (𝕜 := ℂ) (integrable_upperHalfPlanePoissonKernel_smul hh z)
  simp only [RCLike.re_to_complex, smul_re, smul_eq_mul] at this
  rw [upperHalfPlanePoissonIntegralFun_def, ← this]

/-- The imaginary part of `P[h]` is the Poisson integral of the imaginary part of `h`. -/
theorem im_upperHalfPlanePoissonIntegralFun {h : ℝ → ℂ}
    (hh : Integrable h upperHalfPlanePoissonMeasure) (z : ℂ) :
    (upperHalfPlanePoissonIntegralFun h z).im =
      ∫ x, upperHalfPlanePoissonKernel z x * (h x).im := by
  have := integral_im (𝕜 := ℂ) (integrable_upperHalfPlanePoissonKernel_smul hh z)
  simp only [RCLike.im_to_complex, smul_im, smul_eq_mul] at this
  rw [upperHalfPlanePoissonIntegralFun_def, ← this]

/-- **For a nonnegative density, `P[h]` is the Poisson integral of the measure `h dx`.** -/
theorem upperHalfPlanePoissonIntegralFun_eq_upperHalfPlanePoissonIntegral_withDensity
    {h : ℝ → ℝ≥0} (hh : AEMeasurable h) (z : ℂ) :
    upperHalfPlanePoissonIntegralFun (fun x ↦ ((h x : ℝ) : ℂ)) z =
      upperHalfPlanePoissonIntegral (volume.withDensity fun x ↦ (h x : ℝ≥0∞)) z := by
  rw [upperHalfPlanePoissonIntegralFun_def, upperHalfPlanePoissonIntegral_def,
    integral_withDensity_eq_integral_smul₀ hh, ← integral_complex_ofReal]
  congr 1
  funext x
  rw [NNReal.smul_def, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-! ### Schwarz integrals of a function -/

/-- The **Schwarz integral** `S[h](z) = (1 / (π i)) ∫ (1 / (x - z) - x / (1 + x ^ 2)) h(x) dx` of a
complex function `h` on `ℝ`. It is meaningful off the real axis for `h` integrable for the Poisson
measure (`TauCeti.integrable_subtractedResolventKernel_mul`). -/
def upperHalfPlaneSchwarzIntegralFun (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  ((π : ℂ) * I)⁻¹ * ∫ x, subtractedResolventKernel z x * h x

/-- The defining formula of `TauCeti.upperHalfPlaneSchwarzIntegralFun`. -/
theorem upperHalfPlaneSchwarzIntegralFun_def (h : ℝ → ℂ) (z : ℂ) :
    upperHalfPlaneSchwarzIntegralFun h z =
      ((π : ℂ) * I)⁻¹ * ∫ x, subtractedResolventKernel z x * h x := by
  rw [upperHalfPlaneSchwarzIntegralFun]

/-- **The Schwarz integral of an `L¹(Π)` function converges**: for `h` integrable for the Poisson
measure and `z` off the real axis, `x ↦ (1 / (x - z) - x / (1 + x ^ 2)) h(x)` is integrable. -/
theorem integrable_subtractedResolventKernel_mul {h : ℝ → ℂ}
    (hh : Integrable h upperHalfPlanePoissonMeasure) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable fun x ↦ subtractedResolventKernel z x * h x :=
  integrable_smul_of_integrable_withDensity_enorm
    (integrable_subtractedResolventKernel
      ((isPoissonFinite_iff_lintegral_lt_top _).1 (isPoissonFinite_withDensity_enorm hh)) hz)
    (measurable_subtractedResolventKernel z).aestronglyMeasurable
    (aestronglyMeasurable_of_integrable_upperHalfPlanePoissonMeasure hh)

/-- **The Poisson integral is the real part of the Schwarz integral**: `Re S[h] = P[h]` for a real
function `h` integrable for the Poisson measure. On the real axis both sides vanish. -/
theorem re_upperHalfPlaneSchwarzIntegralFun {h : ℝ → ℝ}
    (hh : Integrable h upperHalfPlanePoissonMeasure) (z : ℂ) :
    (upperHalfPlaneSchwarzIntegralFun (fun x ↦ (h x : ℂ)) z).re =
      (upperHalfPlanePoissonIntegralFun (fun x ↦ (h x : ℂ)) z).re := by
  have hre (w : ℂ) : (((π : ℂ) * I)⁻¹ * w).re = π⁻¹ * w.im := by
    simp [← ofReal_inv]
  rw [upperHalfPlaneSchwarzIntegralFun_def,
    re_upperHalfPlanePoissonIntegralFun (h := fun x ↦ (h x : ℂ)) hh.ofReal, hre]
  simp only [ofReal_re]
  by_cases hK : Integrable fun x ↦ subtractedResolventKernel z x * h x
  · have him := integral_im (𝕜 := ℂ) hK
    simp only [RCLike.im_to_complex, im_mul_ofReal,
      subtractedResolventKernel_im_eq_pi_mul_upperHalfPlanePoissonKernel, mul_assoc,
      integral_const_mul] at him
    rw [← him]
    field_simp
  · rw [integral_undef hK, zero_im, mul_zero]
    rcases eq_or_ne z.im 0 with hz | hz
    · simp [upperHalfPlanePoissonKernel_eq, hz]
    · exact absurd (integrable_subtractedResolventKernel_mul hh.ofReal hz) hK

/-- **For a nonnegative density, `S[h]` is the Schwarz integral of the measure `h dx`.** -/
theorem upperHalfPlaneSchwarzIntegralFun_eq_upperHalfPlaneSchwarzIntegral_withDensity
    {h : ℝ → ℝ≥0} (hh : AEMeasurable h) (z : ℂ) :
    upperHalfPlaneSchwarzIntegralFun (fun x ↦ ((h x : ℝ) : ℂ)) z =
      upperHalfPlaneSchwarzIntegral (volume.withDensity fun x ↦ (h x : ℝ≥0∞)) z := by
  rw [upperHalfPlaneSchwarzIntegralFun_def, upperHalfPlaneSchwarzIntegral_def,
    integral_withDensity_eq_integral_smul₀ hh]
  congr 2
  funext x
  rw [NNReal.smul_def, Complex.real_smul, mul_comm]

/-- The **Schwarz integral normalized at infinity** `S⁰[h](z) = (1 / (π i)) ∫ h(x) / (x - z) dx` of
a complex function `h` on `ℝ`, meaningful for `h ∈ L¹(ℝ)`. -/
def upperHalfPlaneSchwarzIntegralFunNormalized (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  ((π : ℂ) * I)⁻¹ * ∫ x, h x / ((x : ℂ) - z)

/-- The defining formula of `TauCeti.upperHalfPlaneSchwarzIntegralFunNormalized`. -/
theorem upperHalfPlaneSchwarzIntegralFunNormalized_def (h : ℝ → ℂ) (z : ℂ) :
    upperHalfPlaneSchwarzIntegralFunNormalized h z =
      ((π : ℂ) * I)⁻¹ * ∫ x, h x / ((x : ℂ) - z) := by
  rw [upperHalfPlaneSchwarzIntegralFunNormalized]

/-- **The two Schwarz integrals differ by an imaginary constant**: for `h ∈ L¹(ℝ)` and `z` off
the real axis, `S⁰[h](z) - S[h](z) = -(i / π) ∫ x h(x) / (1 + x ^ 2) dx`. -/
theorem upperHalfPlaneSchwarzIntegralFunNormalized_sub_upperHalfPlaneSchwarzIntegralFun {h : ℝ → ℂ}
    (hh : Integrable h) {z : ℂ} (hz : z.im ≠ 0) :
    upperHalfPlaneSchwarzIntegralFunNormalized h z - upperHalfPlaneSchwarzIntegralFun h z =
      -(I / π) * ∫ x : ℝ, (x : ℂ) / (1 + (x : ℂ) ^ 2) * h x := by
  have h1 := integrable_div_ofReal_sub hh hz
  have h2 := integrable_div_one_add_sq_mul hh
  have hK : (fun x : ℝ ↦ subtractedResolventKernel z x * h x) =
      fun x ↦ h x / ((x : ℂ) - z) - (x : ℂ) / (1 + (x : ℂ) ^ 2) * h x := by
    funext x
    rw [subtractedResolventKernel_def]
    ring
  rw [upperHalfPlaneSchwarzIntegralFunNormalized_def, upperHalfPlaneSchwarzIntegralFun_def, hK,
    integral_sub h1 h2, ← mul_sub, sub_sub_cancel]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  rw [I_sq]
  ring

/-! ### The Cayley comparison -/

/-- **The Cayley comparison of Poisson kernels.** For `z` in the upper half-plane and `x ∈ ℝ`,
with `w = (z - i) / (z + i)` in the unit disc and `ζ = (x - i) / (x + i)` on the unit circle, the
half-plane Poisson kernel is the disc Poisson kernel times `1 / π` times the density of the Poisson
measure: `P(z, x) = poissonKernel 0 w ζ / (π (1 + x ^ 2))`. The identity holds for every `z ≠ -i`;
in the lower half-plane both sides are negative. -/
theorem upperHalfPlanePoissonKernel_eq_poissonKernel_cayley {z : ℂ} (hz : z ≠ -I) (x : ℝ) :
    upperHalfPlanePoissonKernel z x =
      poissonKernel 0 ((z - I) / (z + I)) (((x : ℂ) - I) / ((x : ℂ) + I)) / (π * (1 + x ^ 2)) := by
  have hzI : z + I ≠ 0 := fun h ↦ hz (eq_neg_of_add_eq_zero_left h)
  have hxI : (x : ℂ) + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  have hnx : ‖(x : ℂ) + I‖ ^ 2 = 1 + x ^ 2 := by
    simpa [Complex.sq_norm, add_comm] using normSq_add_mul_I x 1
  have hζ : ‖((x : ℂ) - I) / ((x : ℂ) + I)‖ ^ 2 = 1 := by
    rw [norm_div, norm_sub_I_div_norm_add_I_ofReal, one_pow]
  have hw : ‖(z - I) / (z + I)‖ ^ 2 = ‖z - I‖ ^ 2 / ‖z + I‖ ^ 2 := by
    rw [norm_div, div_pow]
  have hd : ‖2 * I * ((x : ℂ) - z) / (((x : ℂ) + I) * (z + I))‖ ^ 2 =
      4 * ‖(x : ℂ) - z‖ ^ 2 / ((1 + x ^ 2) * ‖z + I‖ ^ 2) := by
    simp only [norm_div, norm_mul, norm_I, Complex.norm_two, div_pow, mul_pow, hnx]
    ring
  have him : z.im = (‖z + I‖ ^ 2 - ‖z - I‖ ^ 2) / 4 := by
    linarith [norm_add_I_sq z]
  have : 0 < ‖z + I‖ := norm_pos_iff.2 hzI
  rw [upperHalfPlanePoissonKernel_eq, poissonKernel_def]
  simp only [sub_zero]
  rw [sub_I_div_add_I_sub_sub_I_div_add_I hxI hzI, hζ, hw, hd, normSq_eq_norm_sq, him]
  -- At `z = x` both sides vanish, through division by zero.
  rcases eq_or_ne ((x : ℂ) - z) 0 with hxz | hxz
  · simp [hxz]
  have : 0 < ‖(x : ℂ) - z‖ := norm_pos_iff.2 hxz
  field_simp

end TauCeti
