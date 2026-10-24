/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Probability.Distributions.Cauchy.Affine
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map

/-!
# The wrapped Cauchy distribution

The wrapped Cauchy law is the law on the circle `AddCircle (2 * π)` of a Cauchy angle read modulo
`2 * π`. For a location `m` on the circle and a scale `γ ≥ 0` it is the pushforward of the centred
Cauchy law of scale `γ` along `x ↦ m + x`, where the real number `x` is mapped to its class on the
circle. Zero scale gives the Dirac mass at `m`.

The Fourier moments of the law are the values of the Cauchy characteristic function at the
integers, `E[e^{i n θ}] = e^{i n m} e^{-γ |n|}`. In particular the mean resultant length is
`e^{-γ}`, so the circular variance is `1 - e^{-γ}`. Since the Cauchy family adds locations and
scales under convolution and the quotient map `ℝ → AddCircle (2 * π)` is additive, the wrapped
Cauchy family also adds locations and scales under convolution on the circle.

Writing every member of the family as the image of the standard Cauchy law under the continuous
maps `x ↦ m + γ x` gives joint measurability and weak continuity in the location and the scale,
and the weak limit to the Dirac law at the location as the scale tends to zero.

## Main definitions

* `TauCeti.Probability.wrappedCauchyMeasure m γ`: the wrapped Cauchy law with location `m` and
  scale `γ`.

## Main results

* `TauCeti.Probability.wrappedCauchyMeasure_coe`: at a real representative `r` of the location,
  the law is the image on the circle of the Cauchy law of location `r`.
* `TauCeti.Probability.wrappedCauchyMeasure_zero_scale`: zero scale gives the Dirac law.
* `TauCeti.Probability.map_add_right_wrappedCauchyMeasure`: rotating the circle rotates the
  location.
* `TauCeti.Probability.measurable_wrappedCauchyMeasure` and
  `TauCeti.Probability.continuous_wrappedCauchyMeasure`: measurability and weak continuity in the
  parameters.
* `TauCeti.Probability.integral_fourier_wrappedCauchyMeasure`: the integer Fourier moments.
* `TauCeti.Probability.norm_integral_fourier_one_wrappedCauchyMeasure`: the mean resultant length.
* `TauCeti.Probability.wrappedCauchyMeasure_conv_wrappedCauchyMeasure`: convolution adds locations
  and scales.
* `ProbabilityTheory.HasLaw.coe_wrappedCauchyMeasure` and
  `ProbabilityTheory.IndepFun.hasLaw_add_wrappedCauchyMeasure`: the corresponding statements for
  random angles.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), section 3.5.7.
* N. I. Fisher, *Statistical Analysis of Circular Data*, Cambridge University Press (1993),
  section 3.3.4.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Topology
open scoped NNReal

namespace TauCeti.Probability

/-- The wrapped Cauchy law on `AddCircle (2 * π)` with location `m` and scale `γ`: the image of
the centred Cauchy law of scale `γ` under `x ↦ m + x`, where the real number `x` is read on the
circle. -/
def wrappedCauchyMeasure (m : AddCircle (2 * π)) (γ : ℝ≥0) : Measure (AddCircle (2 * π)) :=
  (cauchyMeasure 0 γ).map fun x : ℝ ↦ m + (x : AddCircle (2 * π))

/-- The defining formula of the wrapped Cauchy law. -/
theorem wrappedCauchyMeasure_def (m : AddCircle (2 * π)) (γ : ℝ≥0) :
    wrappedCauchyMeasure m γ = (cauchyMeasure 0 γ).map fun x : ℝ ↦ m + (x : AddCircle (2 * π)) := by
  rw [wrappedCauchyMeasure]

instance isProbabilityMeasure_wrappedCauchyMeasure (m : AddCircle (2 * π)) (γ : ℝ≥0) :
    IsProbabilityMeasure (wrappedCauchyMeasure m γ) := by
  rw [wrappedCauchyMeasure_def]
  infer_instance

/-- At a real representative `r` of the location, the wrapped Cauchy law is the image on the
circle of the Cauchy law with location `r` and the same scale. -/
theorem wrappedCauchyMeasure_coe (r : ℝ) (γ : ℝ≥0) :
    wrappedCauchyMeasure r γ = (cauchyMeasure r γ).map ((↑) : ℝ → AddCircle (2 * π)) := by
  have h := cauchyMeasure_map_affine 0 γ r 1
  simp only [one_mul, mul_zero, add_zero, nnnorm_one] at h
  rw [← h, Measure.map_map (by fun_prop) (by fun_prop), wrappedCauchyMeasure_def]
  simp only [Function.comp_def, AddCircle.coe_add]

/-- **The standard representation.** Every wrapped Cauchy law is the image of the standard Cauchy
law under `x ↦ m + γ x`, read on the circle. -/
theorem wrappedCauchyMeasure_eq_map_cauchyMeasure_zero_one (m : AddCircle (2 * π)) (γ : ℝ≥0) :
    wrappedCauchyMeasure m γ =
      (cauchyMeasure 0 1).map fun x : ℝ ↦ m + ((γ * x : ℝ) : AddCircle (2 * π)) := by
  have h := cauchyMeasure_map_affine 0 1 0 γ
  simp only [zero_add, mul_zero, mul_one, NNReal.nnnorm_eq] at h
  rw [wrappedCauchyMeasure_def, ← h, Measure.map_map (by fun_prop) (by fun_prop),
    Function.comp_def]

/-- At zero scale the wrapped Cauchy law is the Dirac mass at the location. -/
@[simp]
theorem wrappedCauchyMeasure_zero_scale (m : AddCircle (2 * π)) :
    wrappedCauchyMeasure m 0 = Measure.dirac m := by
  rw [wrappedCauchyMeasure_def, cauchyMeasure_zero_scale, Measure.map_dirac' (by fun_prop)]
  simp

/-- **Rotational equivariance.** Rotating a wrapped Cauchy law by `a` rotates its location by
`a`. -/
@[simp]
theorem map_add_right_wrappedCauchyMeasure (m : AddCircle (2 * π)) (γ : ℝ≥0)
    (a : AddCircle (2 * π)) :
    (wrappedCauchyMeasure m γ).map (· + a) = wrappedCauchyMeasure (m + a) γ := by
  rw [wrappedCauchyMeasure_def, Measure.map_map (by fun_prop) (by fun_prop),
    wrappedCauchyMeasure_def]
  congr 1
  funext x
  simp only [Function.comp_apply, add_right_comm]

/-! ### Dependence on the parameters -/

/-- The wrapped Cauchy family is jointly measurable in the location and the scale. -/
@[fun_prop]
theorem measurable_wrappedCauchyMeasure :
    Measurable fun p : AddCircle (2 * π) × ℝ≥0 ↦ wrappedCauchyMeasure p.1 p.2 := by
  simp only [wrappedCauchyMeasure_eq_map_cauchyMeasure_zero_one]
  exact MeasureTheory.measurable_map_of_measurable_uncurry (by fun_prop)

/-- The wrapped Cauchy laws depend jointly weakly continuously on the location and the scale,
including the zero-scale Dirac boundary. -/
theorem continuous_wrappedCauchyMeasure :
    Continuous fun p : AddCircle (2 * π) × ℝ≥0 ↦
      (wrappedCauchyMeasure p.1 p.2).toProbabilityMeasure := by
  let P := (cauchyMeasure 0 1).toProbabilityMeasure
  have h := P.continuous_map_of_forall_continuous
    (f := fun (p : AddCircle (2 * π) × ℝ≥0) (x : ℝ) ↦ p.1 + ((p.2 * x : ℝ) : AddCircle (2 * π)))
    (fun _ ↦ by fun_prop) (fun _ ↦ by fun_prop)
  refine h.congr fun p ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, P, Measure.coe_toProbabilityMeasure,
    wrappedCauchyMeasure_eq_map_cauchyMeasure_zero_one]

/-- Shrinking the scale to zero gives the Dirac law at the location. -/
theorem tendsto_wrappedCauchyMeasure_nhds_zero_dirac (m : AddCircle (2 * π)) :
    Tendsto (fun γ : ℝ≥0 ↦ (wrappedCauchyMeasure m γ).toProbabilityMeasure) (𝓝 0)
      (𝓝 (Measure.dirac m).toProbabilityMeasure) := by
  have h := (continuous_wrappedCauchyMeasure.comp
    (continuous_const.prodMk continuous_id : Continuous fun γ : ℝ≥0 ↦ (m, γ))).tendsto 0
  simpa only [Function.comp_def, wrappedCauchyMeasure_zero_scale] using h

/-! ### Fourier moments -/

/-- **The Fourier moments of the wrapped Cauchy law.** For every integer `n`,
`E[e^{i n θ}] = e^{i n m} e^{-γ |n|}`. -/
theorem integral_fourier_wrappedCauchyMeasure (m : AddCircle (2 * π)) (γ : ℝ≥0) (n : ℤ) :
    ∫ θ, fourier n θ ∂wrappedCauchyMeasure m γ =
      fourier n m * (Real.exp (-((γ : ℝ) * |(n : ℝ)|)) : ℂ) := by
  have hadd (x : ℝ) :
      fourier n (m + (x : AddCircle (2 * π))) =
        fourier n m * fourier n (x : AddCircle (2 * π)) := by
    rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add,
      Circle.coe_mul]
  have hexp (x : ℝ) :
      fourier n (x : AddCircle (2 * π)) = Complex.exp (((n : ℝ) : ℂ) * x * Complex.I) := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 pi_ne_zero
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  rw [wrappedCauchyMeasure_def, integral_map (by fun_prop) (by fun_prop)]
  simp only [hadd, hexp, integral_const_mul]
  have h := charFun_cauchyMeasure 0 γ n
  rw [charFun_apply_real] at h
  rw [h, Complex.ofReal_exp]
  push_cast
  ring_nf

/-- **The mean resultant length of the wrapped Cauchy law.** The first trigonometric moment
`E[e^{i θ}] = e^{i m} e^{-γ}` has modulus `e^{-γ}`, so the circular variance is `1 - e^{-γ}`. -/
theorem norm_integral_fourier_one_wrappedCauchyMeasure (m : AddCircle (2 * π)) (γ : ℝ≥0) :
    ‖∫ θ, fourier 1 θ ∂wrappedCauchyMeasure m γ‖ = Real.exp (-(γ : ℝ)) := by
  rw [integral_fourier_wrappedCauchyMeasure, norm_mul, fourier_apply, Circle.norm_coe, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  simp

/-! ### Convolution -/

/-- **The wrapped Cauchy family is closed under convolution.** Convolving two wrapped Cauchy laws
adds their locations and their scales. -/
theorem wrappedCauchyMeasure_conv_wrappedCauchyMeasure (m₁ m₂ : AddCircle (2 * π))
    (γ₁ γ₂ : ℝ≥0) :
    wrappedCauchyMeasure m₁ γ₁ ∗ wrappedCauchyMeasure m₂ γ₂ =
      wrappedCauchyMeasure (m₁ + m₂) (γ₁ + γ₂) := by
  induction m₁ using QuotientAddGroup.induction_on with | H r₁ => ?_
  induction m₂ using QuotientAddGroup.induction_on with | H r₂ => ?_
  have hmk : Measurable (QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 * π))) :=
    measurable_quotient_mk''
  rw [← AddCircle.coe_add, wrappedCauchyMeasure_coe, wrappedCauchyMeasure_coe,
    wrappedCauchyMeasure_coe, ← cauchyMeasure_conv_cauchyMeasure]
  exact (Measure.map_conv_addMonoidHom _ hmk).symm

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → AddCircle (2 * π)}
  {m m₁ m₂ : AddCircle (2 * π)} {γ γ₁ γ₂ : ℝ≥0}

/-- Rotating a wrapped Cauchy random angle by `a` gives a wrapped Cauchy angle with location
`m + a`. -/
theorem HasLaw.add_const_wrappedCauchyMeasure (hX : HasLaw X (wrappedCauchyMeasure m γ) P)
    (a : AddCircle (2 * π)) :
    HasLaw (fun ω ↦ X ω + a) (wrappedCauchyMeasure (m + a) γ) P := by
  rw [← map_add_right_wrappedCauchyMeasure]
  exact (hasLaw_map (measurable_add_const a).aemeasurable).comp hX

/-- A real Cauchy variable read modulo `2 * π` is a wrapped Cauchy angle with the same location
and scale. -/
theorem HasLaw.coe_wrappedCauchyMeasure {X : Ω → ℝ} {r : ℝ}
    (hX : HasLaw X (cauchyMeasure r γ) P) :
    HasLaw (fun ω ↦ (X ω : AddCircle (2 * π))) (wrappedCauchyMeasure r γ) P := by
  rw [wrappedCauchyMeasure_coe]
  exact (hasLaw_map (by fun_prop)).comp hX

/-- The sum of independent wrapped Cauchy angles is wrapped Cauchy, with the locations and the
scales added. -/
theorem IndepFun.hasLaw_add_wrappedCauchyMeasure (hXY : IndepFun X Y P)
    (hX : HasLaw X (wrappedCauchyMeasure m₁ γ₁) P) (hY : HasLaw Y (wrappedCauchyMeasure m₂ γ₂) P) :
    HasLaw (X + Y) (wrappedCauchyMeasure (m₁ + m₂) (γ₁ + γ₂)) P := by
  have := hX.isProbabilityMeasure
  rw [← wrappedCauchyMeasure_conv_wrappedCauchyMeasure]
  exact hXY.hasLaw_add hX hY

end ProbabilityTheory
