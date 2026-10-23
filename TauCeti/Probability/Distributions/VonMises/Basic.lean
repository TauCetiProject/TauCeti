/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Probability.HasLaw
public import TauCeti.Analysis.SpecialFunctions.BesselI
public import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The von Mises distribution

The von Mises law is the circular analogue of the Gaussian law. For a location `m` on the circle
`AddCircle (2 * π)` and a concentration `κ ≥ 0`, it has density
`θ ↦ e^{κ cos (θ - m)} / I₀(κ)` with respect to the Haar probability measure
`AddCircle.haarAddCircle`, where `I₀` is the modified Bessel function of order zero. Integrating
against `haarAddCircle` is integrating over one period of the angle against `dθ / (2π)`, so the
normalizer is the circle integral `(2π)⁻¹ ∫_{-π}^{π} e^{κ cos θ} dθ = I₀(κ)`.

This file defines the law, proves that it is a probability measure with full support, identifies
its density and Radon–Nikodym derivative, and proves joint measurability in the location and the
concentration, rotational equivariance, and the reduction to Haar measure at zero concentration.
It computes the integer Fourier moments `E[e^{i n θ}] = e^{i n m} I_{|n|}(κ) / I₀(κ)`. The first
of these gives the mean resultant length `I₁(κ) / I₀(κ)`, so the circular variance is
`1 - I₁(κ) / I₀(κ)`.

Since the location lives on the circle itself, the law does not depend on a choice of real
representative of the location; `vonMisesPDFReal_coe_coe` evaluates the density at real
representatives.

## Main definitions

* `TauCeti.Probability.vonMisesPDFReal`, `TauCeti.Probability.vonMisesPDF`: the density with
  respect to `AddCircle.haarAddCircle`.
* `TauCeti.Probability.vonMisesMeasure m κ`: the von Mises law, totalized to zero for `κ < 0`.

## Main results

* `TauCeti.Probability.isProbabilityMeasure_vonMisesMeasure`: for `0 ≤ κ` it is a probability
  measure; `TauCeti.Probability.support_vonMisesMeasure`: its topological support is the whole
  circle.
* `TauCeti.Probability.vonMisesMeasure_zero_concentration`: at zero concentration it is Haar
  measure.
* `TauCeti.Probability.map_add_right_vonMisesMeasure`: rotating the circle rotates the location.
* `TauCeti.Probability.integral_fourier_vonMisesMeasure`: the integer Fourier moments.
* `TauCeti.Probability.norm_integral_fourier_one_vonMisesMeasure`: the mean resultant length.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), section 3.5.4.
* N. I. Fisher, *Statistical Analysis of Circular Data*, Cambridge University Press (1993),
  section 3.3.6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real AddCircle
open scoped ENNReal

namespace TauCeti.Probability

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {m : AddCircle (2 * π)} {κ : ℝ}

/-! ### The density -/

/-- The von Mises density `θ ↦ e^{κ cos (θ - m)} / I₀(κ)` with respect to the Haar probability
measure `AddCircle.haarAddCircle` on `AddCircle (2 * π)`. The cosine of a point of the circle is
the cosine of any of its real representatives. -/
def vonMisesPDFReal (m : AddCircle (2 * π)) (κ : ℝ) (θ : AddCircle (2 * π)) : ℝ :=
  exp (κ * cos_periodic.lift (θ - m)) / besselI 0 κ

/-- The von Mises density as an extended nonnegative real function. -/
def vonMisesPDF (m : AddCircle (2 * π)) (κ : ℝ) (θ : AddCircle (2 * π)) : ℝ≥0∞ :=
  ENNReal.ofReal (vonMisesPDFReal m κ θ)

/-- The defining formula of the von Mises density. -/
theorem vonMisesPDFReal_def (m : AddCircle (2 * π)) (κ : ℝ) :
    vonMisesPDFReal m κ = fun θ => exp (κ * cos_periodic.lift (θ - m)) / besselI 0 κ := by
  funext θ
  rw [vonMisesPDFReal]

/-- The extended von Mises density is the extended nonnegative real lift of the real density. -/
theorem vonMisesPDF_def (m : AddCircle (2 * π)) (κ : ℝ) :
    vonMisesPDF m κ = fun θ => ENNReal.ofReal (vonMisesPDFReal m κ θ) := by
  funext θ
  rw [vonMisesPDF]

/-- At real representatives `x` of the angle and `μ` of the location, the von Mises density is
`e^{κ cos (x - μ)} / I₀(κ)`. -/
@[simp]
theorem vonMisesPDFReal_coe_coe (μ κ x : ℝ) :
    vonMisesPDFReal μ κ x = exp (κ * cos (x - μ)) / besselI 0 κ := by
  rw [vonMisesPDFReal, ← AddCircle.coe_sub, Function.Periodic.lift_coe]

/-- The von Mises density is positive everywhere, for every real concentration. -/
theorem vonMisesPDFReal_pos (m : AddCircle (2 * π)) (κ : ℝ) (θ : AddCircle (2 * π)) :
    0 < vonMisesPDFReal m κ θ :=
  div_pos (exp_pos _) (besselI_zero_left_pos κ)

/-- The real part of the extended von Mises density is the real von Mises density. -/
@[simp]
theorem toReal_vonMisesPDF (m : AddCircle (2 * π)) (κ : ℝ) (θ : AddCircle (2 * π)) :
    (vonMisesPDF m κ θ).toReal = vonMisesPDFReal m κ θ :=
  ENNReal.toReal_ofReal (vonMisesPDFReal_pos m κ θ).le

/-- The von Mises density is jointly continuous in the location, the concentration and the
angle. -/
theorem continuous_uncurry_vonMisesPDFReal :
    Continuous fun p : (AddCircle (2 * π) × ℝ) × AddCircle (2 * π) =>
      vonMisesPDFReal p.1.1 p.1.2 p.2 := by
  have hI : Continuous fun κ : ℝ => besselI 0 κ := by
    simpa using continuous_besselI_natCast 0
  refine Continuous.div ?_ (hI.comp (continuous_snd.comp continuous_fst)) fun p =>
    (besselI_zero_left_pos _).ne'
  exact continuous_exp.comp ((continuous_snd.comp continuous_fst).mul
    (Real.Angle.continuous_cos.comp
      (continuous_snd.sub (continuous_fst.comp continuous_fst))))

/-- The von Mises density is continuous in the angle. -/
theorem continuous_vonMisesPDFReal (m : AddCircle (2 * π)) (κ : ℝ) :
    Continuous (vonMisesPDFReal m κ) :=
  continuous_uncurry_vonMisesPDFReal.comp (Continuous.prodMk_right (m, κ))

/-- The von Mises density is jointly measurable in the location, the concentration and the
angle. -/
theorem measurable_uncurry_vonMisesPDF :
    Measurable fun p : (AddCircle (2 * π) × ℝ) × AddCircle (2 * π) =>
      vonMisesPDF p.1.1 p.1.2 p.2 :=
  ENNReal.measurable_ofReal.comp continuous_uncurry_vonMisesPDFReal.measurable

/-- The von Mises density is measurable in the angle. -/
@[fun_prop]
theorem measurable_vonMisesPDFReal (m : AddCircle (2 * π)) (κ : ℝ) :
    Measurable (vonMisesPDFReal m κ) :=
  (continuous_vonMisesPDFReal m κ).measurable

/-- The extended von Mises density is measurable in the angle. -/
@[fun_prop]
theorem measurable_vonMisesPDF (m : AddCircle (2 * π)) (κ : ℝ) :
    Measurable (vonMisesPDF m κ) :=
  ENNReal.measurable_ofReal.comp (measurable_vonMisesPDFReal m κ)

/-! ### Normalization -/

/-- The von Mises density integrates to one against the Haar probability measure. -/
theorem integral_vonMisesPDFReal (m : AddCircle (2 * π)) (κ : ℝ) :
    ∫ θ, vonMisesPDFReal m κ θ ∂haarAddCircle = 1 := by
  simp only [vonMisesPDFReal]
  rw [integral_div, integral_exp_mul_cos_sub,
    div_self (besselI_zero_left_pos κ).ne']

/-- The von Mises density has total Haar mass one. -/
theorem lintegral_vonMisesPDF (m : AddCircle (2 * π)) (κ : ℝ) :
    ∫⁻ θ, vonMisesPDF m κ θ ∂haarAddCircle = 1 := by
  have hint : Integrable (vonMisesPDFReal m κ) haarAddCircle :=
    (continuous_vonMisesPDFReal m κ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [vonMisesPDF]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun θ => (vonMisesPDFReal_pos m κ θ).le), integral_vonMisesPDFReal,
    ENNReal.ofReal_one]

/-! ### The law -/

/-- The von Mises law on `AddCircle (2 * π)` with location `m` and concentration `κ`: the Haar
probability measure weighted by `vonMisesPDF m κ`. Negative concentrations give the zero
measure. -/
def vonMisesMeasure (m : AddCircle (2 * π)) (κ : ℝ) : Measure (AddCircle (2 * π)) :=
  if 0 ≤ κ then haarAddCircle.withDensity (vonMisesPDF m κ) else 0

/-- For a nonnegative concentration, the von Mises law is the Haar probability measure weighted by
the von Mises density. -/
theorem vonMisesMeasure_of_nonneg (hκ : 0 ≤ κ) :
    vonMisesMeasure m κ = haarAddCircle.withDensity (vonMisesPDF m κ) := by
  rw [vonMisesMeasure, ite_eq_left hκ]

/-- A negative concentration gives the zero measure. -/
@[simp]
theorem vonMisesMeasure_of_neg (hκ : κ < 0) : vonMisesMeasure m κ = 0 := by
  rw [vonMisesMeasure, ite_eq_right hκ.not_ge]

/-- For a nonnegative concentration, the von Mises law is a probability measure. -/
theorem isProbabilityMeasure_vonMisesMeasure (m : AddCircle (2 * π)) (hκ : 0 ≤ κ) :
    IsProbabilityMeasure (vonMisesMeasure m κ) :=
  ⟨by rw [vonMisesMeasure_of_nonneg hκ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_vonMisesPDF]⟩

/-- The von Mises law is a probability measure exactly for nonnegative concentrations. -/
@[simp]
theorem isProbabilityMeasure_vonMisesMeasure_iff :
    IsProbabilityMeasure (vonMisesMeasure m κ) ↔ 0 ≤ κ := by
  refine ⟨fun h => ?_, isProbabilityMeasure_vonMisesMeasure m⟩
  by_contra hκ
  rw [vonMisesMeasure_of_neg (not_le.mp hκ)] at h
  exact IsProbabilityMeasure.ne_zero (0 : Measure (AddCircle (2 * π))) rfl

/-- For a nonnegative concentration, the von Mises law has topological support the whole circle,
since its density is positive and continuous. -/
theorem support_vonMisesMeasure (m : AddCircle (2 * π)) (hκ : 0 ≤ κ) :
    (vonMisesMeasure m κ).support = Set.univ := by
  rw [vonMisesMeasure_of_nonneg hκ, Measure.support_withDensity_eq_closure
    (measurable_vonMisesPDF m κ) isOpen_univ, closure_univ]
  exact Set.eq_univ_of_forall fun θ => (ENNReal.ofReal_pos.2 (vonMisesPDFReal_pos m κ θ)).ne'

/-- For a nonnegative concentration, the Radon–Nikodym derivative of the von Mises law with
respect to the Haar probability measure is the von Mises density. -/
theorem rnDeriv_vonMisesMeasure (m : AddCircle (2 * π)) (hκ : 0 ≤ κ) :
    (vonMisesMeasure m κ).rnDeriv haarAddCircle =ᵐ[haarAddCircle] vonMisesPDF m κ := by
  rw [vonMisesMeasure_of_nonneg hκ]
  exact Measure.rnDeriv_withDensity _ (measurable_vonMisesPDF m κ)

/-- The totalized von Mises family is jointly measurable in the location and the
concentration. -/
@[fun_prop]
theorem measurable_vonMisesMeasure :
    Measurable fun p : AddCircle (2 * π) × ℝ => vonMisesMeasure p.1 p.2 := by
  unfold vonMisesMeasure
  exact Measurable.ite (measurableSet_le measurable_const measurable_snd)
    (measurable_withDensity measurable_uncurry_vonMisesPDF) measurable_const

/-- At zero concentration the von Mises law is the Haar probability measure. -/
@[simp]
theorem vonMisesMeasure_zero_concentration (m : AddCircle (2 * π)) :
    vonMisesMeasure m 0 = haarAddCircle := by
  have hpdf : vonMisesPDF m 0 = 1 := by
    funext θ
    simp [vonMisesPDF, vonMisesPDFReal]
  rw [vonMisesMeasure_of_nonneg le_rfl, hpdf, withDensity_one]

/-- **Rotational equivariance.** Rotating a von Mises law by `a` rotates its location by `a`. -/
@[simp]
theorem map_add_right_vonMisesMeasure (m : AddCircle (2 * π)) (κ : ℝ) (a : AddCircle (2 * π)) :
    (vonMisesMeasure m κ).map (· + a) = vonMisesMeasure (m + a) κ := by
  rcases le_or_gt 0 κ with hκ | hκ
  · rw [vonMisesMeasure_of_nonneg hκ, vonMisesMeasure_of_nonneg hκ,
      Measure.map_add_right_withDensity]
    congr 1
    funext θ
    simp only [vonMisesPDF, vonMisesPDFReal, sub_sub, add_comm a m]
  · simp [hκ]

/-! ### Fourier moments -/

/-- **The Fourier moments of the von Mises law.** For a nonnegative concentration and every
integer `n`, `E[e^{i n θ}] = e^{i n m} I_{|n|}(κ) / I₀(κ)`. -/
theorem integral_fourier_vonMisesMeasure (m : AddCircle (2 * π)) (hκ : 0 ≤ κ) (n : ℤ) :
    ∫ θ, fourier n θ ∂vonMisesMeasure m κ =
      fourier n m * (besselI n.natAbs κ / besselI 0 κ : ℝ) := by
  rw [vonMisesMeasure_of_nonneg hκ, integral_withDensity_eq_integral_toReal_smul
    (measurable_vonMisesPDF m κ) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [toReal_vonMisesPDF, vonMisesPDFReal, Complex.real_smul, Complex.ofReal_div,
    div_mul_eq_mul_div]
  rw [integral_div, integral_exp_mul_cos_sub_mul_fourier]
  ring

/-- **The mean resultant length of the von Mises law.** For a nonnegative concentration, the first
trigonometric moment `E[e^{i θ}] = e^{i m} I₁(κ) / I₀(κ)` has modulus `I₁(κ) / I₀(κ)`, so the
circular variance is `1 - I₁(κ) / I₀(κ)`. -/
theorem norm_integral_fourier_one_vonMisesMeasure (m : AddCircle (2 * π)) (hκ : 0 ≤ κ) :
    ‖∫ θ, fourier 1 θ ∂vonMisesMeasure m κ‖ = besselI 1 κ / besselI 0 κ := by
  have hI : 0 ≤ besselI 1 κ := by
    rcases hκ.eq_or_lt with rfl | hκ
    · simp
    · exact (besselI_pos (by norm_num) hκ).le
  rw [integral_fourier_vonMisesMeasure m hκ, norm_mul, fourier_apply, Circle.norm_coe, one_mul,
    Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg (by simpa using hI) (besselI_zero_left_pos κ).le)]
  simp

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → AddCircle (2 * π)}
  {m : AddCircle (2 * π)} {κ : ℝ}

/-- Rotating a von Mises random angle by `a` gives a von Mises angle with location `m + a`. -/
theorem HasLaw.add_const_vonMisesMeasure (hX : HasLaw X (vonMisesMeasure m κ) P)
    (a : AddCircle (2 * π)) :
    HasLaw (fun ω => X ω + a) (vonMisesMeasure (m + a) κ) P := by
  rw [← map_add_right_vonMisesMeasure]
  exact (hasLaw_map (measurable_add_const a).aemeasurable).comp hX

end ProbabilityTheory
