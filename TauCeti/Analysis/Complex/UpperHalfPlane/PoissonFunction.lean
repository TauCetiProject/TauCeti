/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson

/-!
# Poisson and Schwarz integrals of functions on the upper half-plane

For a complex function `h` on `ℝ` that is integrable for the Poisson measure
`Π = dx / (1 + x ^ 2)`, the **Poisson integral** `P[h](z) = ∫ P(z, x) h(x) dx` is defined on the
upper half-plane `ℂ₊`, since `P(z, x) ≤ C(z) / (1 + x ^ 2)`. For a nonnegative `h` it is the
Poisson integral of the measure `h dx`.

The **Schwarz integral** of `h` is
`S[h](z) = (1 / (π i)) ∫ (1 / (x - z) - x / (1 + x ^ 2)) h(x) dx`, and for `h ∈ L¹(ℝ)` the
Schwarz integral **normalised at infinity** is
`S⁰[h](z) = (1 / (π i)) ∫ h(x) / (x - z) dx`. Off the real axis both integrals converge for
`h ∈ L¹(ℝ)`, and they differ by the imaginary constant
`S⁰[h] - S[h] = -(i / π) ∫ x h(x) / (1 + x ^ 2) dx`.

The Cayley transform `z ↦ (z - i) / (z + i)` carries `ℂ₊` to the unit disc and `ℝ` to the unit
circle minus `1`. Under it the half-plane Poisson kernel is the disc Poisson kernel times the
density of the Poisson measure:
`P(z, x) = poissonKernel 0 w ζ / (π (1 + x ^ 2))` with `w = (z - i) / (z + i)` and
`ζ = (x - i) / (x + i)`, where Mathlib's `poissonKernel 0 w ζ = (|ζ| ^ 2 - |w| ^ 2) / |ζ - w| ^ 2`.

## Main declarations

* `TauCeti.upperHalfPlanePoissonIntegralFun`: the Poisson integral `P[h]` of a complex function.
* `TauCeti.integrable_upperHalfPlanePoissonKernel_smul`: for `h ∈ L¹(Π)` the integrand of `P[h]` is
  integrable.
* `TauCeti.upperHalfPlanePoissonIntegralFun_eq_withDensity`: for a nonnegative `h`, `P[h]` is the
  Poisson integral of the measure `h dx`.
* `TauCeti.upperHalfPlaneSchwarzIntegralFun`, `TauCeti.upperHalfPlaneSchwarzIntegralZero`: the
  Schwarz integrals `S[h]` and `S⁰[h]` of a complex function.
* `TauCeti.upperHalfPlaneSchwarzIntegralZero_sub_upperHalfPlaneSchwarzIntegralFun`:
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
Poisson integrals of the real and imaginary parts of `h`. -/
def upperHalfPlanePoissonIntegralFun (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x, upperHalfPlanePoissonKernel z x • h x

/-- The defining formula of `TauCeti.upperHalfPlanePoissonIntegralFun`. -/
theorem upperHalfPlanePoissonIntegralFun_def (h : ℝ → ℂ) (z : ℂ) :
    upperHalfPlanePoissonIntegralFun h z = ∫ x, upperHalfPlanePoissonKernel z x • h x := by
  rw [upperHalfPlanePoissonIntegralFun]

/-- A function is integrable for the Poisson measure `dx / (1 + x ^ 2)` exactly when
`h(x) / (1 + x ^ 2)` is Lebesgue integrable. -/
theorem integrable_upperHalfPlanePoissonMeasure_iff_integrable_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℝ → E} :
    Integrable h upperHalfPlanePoissonMeasure ↔ Integrable (fun x ↦ (1 + x ^ 2)⁻¹ • h x) := by
  rw [upperHalfPlanePoissonMeasure_eq_withDensity,
    integrable_withDensity_iff_integrable_smul' (by fun_prop) (.of_forall fun _ ↦ by simp)]
  simp_rw [ENNReal.toReal_ofReal (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ 1 + _ ^ 2))]

/-- For `h` integrable for the Poisson measure and a pole `z` in the closed upper half-plane,
`x ↦ P(z, x) h(x)` is integrable. -/
private theorem integrable_upperHalfPlanePoissonKernel_smul_of_nonneg {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℝ → E}
    (hh : Integrable h upperHalfPlanePoissonMeasure) {z : ℂ} (hz : 0 ≤ z.im) :
    Integrable fun x ↦ upperHalfPlanePoissonKernel z x • h x := by
  have h' := integrable_upperHalfPlanePoissonMeasure_iff_integrable_smul.1 hh
  -- `h` is Lebesgue measurable: it is `(1 + x ^ 2) • ((1 + x ^ 2)⁻¹ • h x)`.
  have hm : AEStronglyMeasurable h volume :=
    ((by fun_prop : Continuous fun x : ℝ ↦ 1 + x ^ 2).aestronglyMeasurable.smul
      h'.aestronglyMeasurable).congr (.of_forall fun x ↦ by
        rw [Pi.smul_apply', smul_smul, mul_inv_cancel₀ (by positivity), one_smul])
  refine (h'.norm.const_mul (2 * (1 + z.re ^ 2) * max z.im z.im⁻¹ / π)).mono'
    ((measurable_upperHalfPlanePoissonKernel z).aestronglyMeasurable.smul hm)
    (.of_forall fun x ↦ ?_)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (upperHalfPlanePoissonKernel_nonneg hz x),
    Real.norm_of_nonneg (by positivity), ← mul_assoc]
  gcongr
  rw [← div_eq_mul_inv]
  exact upperHalfPlanePoissonKernel_le hz x

/-- **The Poisson integral of an `L¹(Π)` function converges**: for `h` integrable for the Poisson
measure, `x ↦ P(z, x) h(x)` is integrable for every pole `z`. In the lower half-plane the kernel is
`P(z, x) = -P(conj z, x)`. -/
theorem integrable_upperHalfPlanePoissonKernel_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {h : ℝ → E} (hh : Integrable h upperHalfPlanePoissonMeasure) (z : ℂ) :
    Integrable fun x ↦ upperHalfPlanePoissonKernel z x • h x := by
  rcases le_total 0 z.im with hz | hz
  · exact integrable_upperHalfPlanePoissonKernel_smul_of_nonneg hh hz
  · refine (integrable_upperHalfPlanePoissonKernel_smul_of_nonneg hh
      (z := (starRingEnd ℂ) z) (by simpa using hz)).neg.congr (.of_forall fun x ↦ ?_)
    simp [neg_smul]

/-- **For a nonnegative density, `P[h]` is the Poisson integral of the measure `h dx`.** -/
theorem upperHalfPlanePoissonIntegralFun_eq_withDensity {h : ℝ → ℝ≥0} (hh : Measurable h)
    (z : ℂ) :
    upperHalfPlanePoissonIntegralFun (fun x ↦ ((h x : ℝ) : ℂ)) z =
      upperHalfPlanePoissonIntegral (volume.withDensity fun x ↦ (h x : ℝ≥0∞)) z := by
  rw [upperHalfPlanePoissonIntegralFun_def, upperHalfPlanePoissonIntegral_def,
    integral_withDensity_eq_integral_smul hh, ← integral_complex_ofReal]
  congr 1
  funext x
  rw [NNReal.smul_def, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-! ### Schwarz integrals of a function -/

/-- The **Schwarz integral** `S[h](z) = (1 / (π i)) ∫ (1 / (x - z) - x / (1 + x ^ 2)) h(x) dx` of a
complex function `h` on `ℝ`. -/
def upperHalfPlaneSchwarzIntegralFun (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  ((π : ℂ) * I)⁻¹ * ∫ x, subtractedResolventKernel z x * h x

/-- The defining formula of `TauCeti.upperHalfPlaneSchwarzIntegralFun`. -/
theorem upperHalfPlaneSchwarzIntegralFun_def (h : ℝ → ℂ) (z : ℂ) :
    upperHalfPlaneSchwarzIntegralFun h z =
      ((π : ℂ) * I)⁻¹ * ∫ x, subtractedResolventKernel z x * h x := by
  rw [upperHalfPlaneSchwarzIntegralFun]

/-- The **Schwarz integral normalised at infinity** `S⁰[h](z) = (1 / (π i)) ∫ h(x) / (x - z) dx` of
a complex function `h` on `ℝ`, meaningful for `h ∈ L¹(ℝ)`. -/
def upperHalfPlaneSchwarzIntegralZero (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  ((π : ℂ) * I)⁻¹ * ∫ x, h x / ((x : ℂ) - z)

/-- The defining formula of `TauCeti.upperHalfPlaneSchwarzIntegralZero`. -/
theorem upperHalfPlaneSchwarzIntegralZero_def (h : ℝ → ℂ) (z : ℂ) :
    upperHalfPlaneSchwarzIntegralZero h z = ((π : ℂ) * I)⁻¹ * ∫ x, h x / ((x : ℂ) - z) := by
  rw [upperHalfPlaneSchwarzIntegralZero]

/-- Off the real axis, `h(x) / (x - z)` is integrable for `h ∈ L¹(ℝ)`: `|x - z| ≥ |Im z|`. -/
theorem integrable_div_ofReal_sub {h : ℝ → ℂ} (hh : Integrable h) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable fun x : ℝ ↦ h x / ((x : ℂ) - z) := by
  refine (hh.norm.const_mul |z.im|⁻¹).mono'
    (hh.aemeasurable.div (by fun_prop : Measurable fun x : ℝ ↦ (x : ℂ) - z).aemeasurable
      |>.aestronglyMeasurable) (.of_forall fun x ↦ ?_)
  have hpos : 0 < |z.im| := abs_pos.2 hz
  have hle : |z.im| ≤ ‖(x : ℂ) - z‖ := by
    simpa using Complex.abs_im_le_norm ((x : ℂ) - z)
  rw [norm_div, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hpos hle) (norm_nonneg _)

/-- For `h ∈ L¹(ℝ)`, `x h(x) / (1 + x ^ 2)` is integrable, since `|x| / (1 + x ^ 2) ≤ 1`. -/
theorem integrable_mul_div_one_add_sq {h : ℝ → ℂ} (hh : Integrable h) :
    Integrable fun x : ℝ ↦ (x : ℂ) / (1 + (x : ℂ) ^ 2) * h x := by
  refine hh.norm.mono' (((by fun_prop : Measurable fun x : ℝ ↦ (x : ℂ) / (1 + (x : ℂ) ^ 2))
    |>.aestronglyMeasurable).mul hh.aestronglyMeasurable) (.of_forall fun x ↦ ?_)
  have h1 : (1 + (x : ℂ) ^ 2) = ((1 + x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, h1, ← ofReal_div, norm_real, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  refine mul_le_of_le_one_left (norm_nonneg _) ((div_le_one (by positivity)).2 ?_)
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

/-- **The two Schwarz integrals differ by an imaginary constant**: for `h ∈ L¹(ℝ)` and `z` off
the real axis, `S⁰[h](z) - S[h](z) = -(i / π) ∫ x h(x) / (1 + x ^ 2) dx`. -/
theorem upperHalfPlaneSchwarzIntegralZero_sub_upperHalfPlaneSchwarzIntegralFun {h : ℝ → ℂ}
    (hh : Integrable h) {z : ℂ} (hz : z.im ≠ 0) :
    upperHalfPlaneSchwarzIntegralZero h z - upperHalfPlaneSchwarzIntegralFun h z =
      -(I / π) * ∫ x : ℝ, (x : ℂ) / (1 + (x : ℂ) ^ 2) * h x := by
  have h1 := integrable_div_ofReal_sub hh hz
  have h2 := integrable_mul_div_one_add_sq hh
  have hK : (fun x : ℝ ↦ subtractedResolventKernel z x * h x) =
      fun x ↦ h x / ((x : ℂ) - z) - (x : ℂ) / (1 + (x : ℂ) ^ 2) * h x := by
    funext x
    rw [subtractedResolventKernel_def]
    ring
  rw [upperHalfPlaneSchwarzIntegralZero_def, upperHalfPlaneSchwarzIntegralFun_def, hK,
    integral_sub h1 h2, ← mul_sub, sub_sub_cancel]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  rw [I_sq]
  ring

/-! ### The Cayley comparison -/

/-- **The Cayley comparison of Poisson kernels.** For `z` in the upper half-plane and `x ∈ ℝ`,
with `w = (z - i) / (z + i)` in the unit disc and `ζ = (x - i) / (x + i)` on the unit circle, the
half-plane Poisson kernel is the disc Poisson kernel times the density of the Poisson measure:
`P(z, x) = poissonKernel 0 w ζ / (π (1 + x ^ 2))`. The identity holds for every `z ≠ -i`; in the
lower half-plane both sides are negative. -/
theorem upperHalfPlanePoissonKernel_eq_poissonKernel_cayley {z : ℂ} (hz : z ≠ -I) (x : ℝ) :
    upperHalfPlanePoissonKernel z x =
      poissonKernel 0 ((z - I) / (z + I)) (((x : ℂ) - I) / ((x : ℂ) + I)) / (π * (1 + x ^ 2)) := by
  have hzI : z + I ≠ 0 := fun h ↦ hz (eq_neg_of_add_eq_zero_left h)
  have hxI : (x : ℂ) + I ≠ 0 := fun h ↦ by simpa using congrArg Complex.im h
  have hdiff : ((x : ℂ) - I) / ((x : ℂ) + I) - (z - I) / (z + I) =
      2 * I * ((x : ℂ) - z) / (((x : ℂ) + I) * (z + I)) := by
    field_simp
    ring
  have hnx : ‖(x : ℂ) + I‖ ^ 2 = 1 + x ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp
    ring
  have hnxm : ‖(x : ℂ) - I‖ ^ 2 = 1 + x ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp
    ring
  have hzp : ‖z + I‖ ^ 2 - ‖z - I‖ ^ 2 = 4 * z.im := by
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
    simp
    ring
  have hζ : ‖((x : ℂ) - I) / ((x : ℂ) + I)‖ ^ 2 = 1 := by
    rw [norm_div, div_pow, hnx, hnxm, div_self (by positivity)]
  have hw : ‖(z - I) / (z + I)‖ ^ 2 = ‖z - I‖ ^ 2 / ‖z + I‖ ^ 2 := by
    rw [norm_div, div_pow]
  have hd : ‖2 * I * ((x : ℂ) - z) / (((x : ℂ) + I) * (z + I))‖ ^ 2 =
      4 * ‖(x : ℂ) - z‖ ^ 2 / ((1 + x ^ 2) * ‖z + I‖ ^ 2) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_two, div_pow, mul_pow, mul_pow,
      mul_pow, hnx]
    norm_num
  have him : z.im = (‖z + I‖ ^ 2 - ‖z - I‖ ^ 2) / 4 := by
    rw [hzp]
    ring
  have : 0 < ‖z + I‖ := norm_pos_iff.2 hzI
  rw [upperHalfPlanePoissonKernel_eq, poissonKernel_def]
  simp only [sub_zero]
  rw [hdiff, hζ, hw, hd, normSq_eq_norm_sq, him]
  -- At `z = x` both sides vanish, through division by zero.
  rcases eq_or_ne ((x : ℂ) - z) 0 with hxz | hxz
  · simp [hxz]
  have : 0 < ‖(x : ℂ) - z‖ := norm_pos_iff.2 hxz
  field_simp

end TauCeti
