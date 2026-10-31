/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability
import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The generalized normal distribution

The generalized normal (exponential power) law with location `m`, scale `s` and shape `p` has
density `p / (2 * s * Γ (1 / p)) * exp (-|(x - m) / s| ^ p)` on the whole real line. Shape `1`
gives the Laplace law and shape `2` a Gaussian law; both identifications are in
`TauCeti.Probability.Distributions.GeneralizedNormal.Relations`.

This file defines the density and the law, proves that the law is a probability measure for
`0 < s` and `0 < p`, connects it to `MeasureTheory.HasPDF`, and proves that the family is
measurable in its three parameters. It also computes the absolute central moments: `E |X - m| ^ q`
is finite exactly for `-1 < q`, and then equals `s ^ q * Γ ((q + 1) / p) / Γ (1 / p)`. The total
mass of the density is the case `q = 0`.

**Boundary.** Outside `0 < s ∧ 0 < p` the density, and hence the law, is zero.

## Implementation

After translating by `m` and rescaling by `s`, every absolute moment is the two-sided Gamma
integral `TauCeti.integral_abs_rpow_mul_exp_neg_abs_rpow`.

## References

* S. Nadarajah, *A generalized normal distribution*, Journal of Applied Statistics 32(7),
  685–694 (2005).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti.Probability

variable {m s p q x : ℝ}

/-! ### The density -/

/-- The density of the generalized normal law with location `m`, scale `s` and shape `p`, as a
real-valued function. It vanishes unless `0 < s` and `0 < p`. -/
def generalizedNormalPDFReal (m s p x : ℝ) : ℝ :=
  if 0 < s ∧ 0 < p then p / (2 * s * Real.Gamma p⁻¹) * Real.exp (-|(x - m) / s| ^ p) else 0

/-- The density of the generalized normal law, as a function valued in `ℝ≥0∞`. -/
def generalizedNormalPDF (m s p x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (generalizedNormalPDFReal m s p x)

/-- The `ℝ≥0∞`-valued density is the coercion of the real-valued one. -/
theorem generalizedNormalPDF_eq_ofReal (m s p x : ℝ) :
    generalizedNormalPDF m s p x = ENNReal.ofReal (generalizedNormalPDFReal m s p x) := by
  rw [generalizedNormalPDF]

/-- For positive scale and shape the density is the exponential power formula. -/
@[simp]
theorem generalizedNormalPDFReal_of_pos (hs : 0 < s) (hp : 0 < p) (m x : ℝ) :
    generalizedNormalPDFReal m s p x =
      p / (2 * s * Real.Gamma p⁻¹) * Real.exp (-|(x - m) / s| ^ p) := by
  rw [generalizedNormalPDFReal, ite_eq_left ⟨hs, hp⟩]

/-- Outside the valid parameter range the density vanishes. -/
@[simp]
theorem generalizedNormalPDFReal_of_not_pos (h : ¬ (0 < s ∧ 0 < p)) (m x : ℝ) :
    generalizedNormalPDFReal m s p x = 0 := by
  rw [generalizedNormalPDFReal, ite_eq_right h]

/-- For positive scale and shape the `ℝ≥0∞`-valued density is the exponential power formula. -/
@[simp]
theorem generalizedNormalPDF_of_pos (hs : 0 < s) (hp : 0 < p) (m x : ℝ) :
    generalizedNormalPDF m s p x =
      ENNReal.ofReal (p / (2 * s * Real.Gamma p⁻¹) * Real.exp (-|(x - m) / s| ^ p)) := by
  rw [generalizedNormalPDF_eq_ofReal, generalizedNormalPDFReal_of_pos hs hp]

/-- Outside the valid parameter range the `ℝ≥0∞`-valued density vanishes. -/
@[simp]
theorem generalizedNormalPDF_of_not_pos (h : ¬ (0 < s ∧ 0 < p)) (m x : ℝ) :
    generalizedNormalPDF m s p x = 0 := by
  rw [generalizedNormalPDF_eq_ofReal, generalizedNormalPDFReal_of_not_pos h, ENNReal.ofReal_zero]

/-- The normalizing constant of the density is positive. -/
private lemma generalizedNormal_const_pos (hs : 0 < s) (hp : 0 < p) :
    0 < p / (2 * s * Real.Gamma p⁻¹) := by
  have := Real.Gamma_pos_of_pos (inv_pos.mpr hp)
  positivity

/-- The generalized normal density is nonnegative at every parameter. -/
theorem generalizedNormalPDFReal_nonneg (m s p x : ℝ) : 0 ≤ generalizedNormalPDFReal m s p x := by
  by_cases h : 0 < s ∧ 0 < p
  · rw [generalizedNormalPDFReal_of_pos h.1 h.2]
    exact mul_nonneg (generalizedNormal_const_pos h.1 h.2).le (Real.exp_pos _).le
  · rw [generalizedNormalPDFReal_of_not_pos h]

/-- For positive scale and shape the density is strictly positive everywhere. -/
theorem generalizedNormalPDFReal_pos (hs : 0 < s) (hp : 0 < p) (m x : ℝ) :
    0 < generalizedNormalPDFReal m s p x := by
  rw [generalizedNormalPDFReal_of_pos hs hp]
  exact mul_pos (generalizedNormal_const_pos hs hp) (Real.exp_pos _)

/-- The two densities agree under `ENNReal.toReal`; the density is never infinite. -/
@[simp]
theorem toReal_generalizedNormalPDF (m s p x : ℝ) :
    (generalizedNormalPDF m s p x).toReal = generalizedNormalPDFReal m s p x :=
  ENNReal.toReal_ofReal (generalizedNormalPDFReal_nonneg m s p x)

/-- The density is measurable jointly in its three parameters and the point. -/
@[fun_prop]
theorem measurable_uncurry_generalizedNormalPDFReal :
    Measurable fun θ : (ℝ × ℝ × ℝ) × ℝ => generalizedNormalPDFReal θ.1.1 θ.1.2.1 θ.1.2.2 θ.2 := by
  simp only [generalizedNormalPDFReal]
  refine Measurable.ite ((measurableSet_lt measurable_const measurable_fst.snd.fst).inter
    (measurableSet_lt measurable_const measurable_fst.snd.snd)) ?_ measurable_const
  fun_prop

/-- The real-valued density is measurable. -/
@[fun_prop]
theorem measurable_generalizedNormalPDFReal (m s p : ℝ) :
    Measurable (generalizedNormalPDFReal m s p) :=
  measurable_uncurry_generalizedNormalPDFReal.comp
    ((measurable_const (a := ((m, s, p) : ℝ × ℝ × ℝ))).prodMk measurable_id)

/-- The `ℝ≥0∞`-valued density is measurable. -/
@[fun_prop]
theorem measurable_generalizedNormalPDF (m s p : ℝ) : Measurable (generalizedNormalPDF m s p) :=
  (measurable_generalizedNormalPDFReal m s p).ennreal_ofReal

/-! ### Absolute moments of the density -/

/-- The density weighted by `|x - m| ^ q` is a rescaled two-sided Gamma integrand evaluated at
`(x - m) / s`. -/
private lemma generalizedNormalPDFReal_mul_rpow_abs_sub (hs : 0 < s) (hp : 0 < p) (m q x : ℝ) :
    generalizedNormalPDFReal m s p x * |x - m| ^ q =
      p / (2 * s * Real.Gamma p⁻¹) * s ^ q *
        (|(x - m) / s| ^ q * Real.exp (-|(x - m) / s| ^ p)) := by
  have habs : |x - m| ^ q = |(x - m) / s| ^ q * s ^ q := by
    rw [abs_div, abs_of_pos hs, Real.div_rpow (abs_nonneg _) hs.le,
      div_mul_cancel₀ _ (Real.rpow_pos_of_pos hs q).ne']
  rw [generalizedNormalPDFReal_of_pos hs hp, habs]
  ring

/-- The density weighted by `|x - m| ^ q` is integrable exactly when `-1 < q`, for positive
scale and shape. -/
private lemma integrable_generalizedNormalPDFReal_mul_rpow_abs_sub_iff (hs : 0 < s) (hp : 0 < p)
    (m : ℝ) :
    Integrable (fun x => generalizedNormalPDFReal m s p x * |x - m| ^ q) ↔ -1 < q := by
  have hc : p / (2 * s * Real.Gamma p⁻¹) * s ^ q ≠ 0 :=
    (mul_pos (generalizedNormal_const_pos hs hp) (Real.rpow_pos_of_pos hs q)).ne'
  simp_rw [generalizedNormalPDFReal_mul_rpow_abs_sub hs hp]
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc),
    ← integrable_abs_rpow_mul_exp_neg_abs_rpow_iff hp,
    ← integrable_comp_div_iff (fun y : ℝ => |y| ^ q * Real.exp (-|y| ^ p)) hs.ne']
  exact ⟨fun h => by simpa using h.comp_sub_right (-m), fun h => h.comp_sub_right m⟩

/-- The density-weighted absolute moments: for positive scale and shape and `-1 < q`,
`∫ x, f x * |x - m| ^ q = s ^ q * Γ ((q + 1) / p) / Γ (1 / p)`. -/
private lemma integral_generalizedNormalPDFReal_mul_rpow_abs_sub (hs : 0 < s) (hp : 0 < p)
    (hq : -1 < q) (m : ℝ) :
    ∫ x, generalizedNormalPDFReal m s p x * |x - m| ^ q =
      s ^ q * Real.Gamma ((q + 1) / p) / Real.Gamma p⁻¹ := by
  simp_rw [generalizedNormalPDFReal_mul_rpow_abs_sub hs hp]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun y : ℝ => |y / s| ^ q * Real.exp (-|y / s| ^ p)) m,
    Measure.integral_comp_div (fun y : ℝ => |y| ^ q * Real.exp (-|y| ^ p)) s,
    integral_abs_rpow_mul_exp_neg_abs_rpow hp hq, abs_of_pos hs, smul_eq_mul]
  have := Real.Gamma_pos_of_pos (inv_pos.mpr hp)
  field_simp

/-- The generalized normal density is integrable at every parameter. -/
theorem integrable_generalizedNormalPDFReal (m s p : ℝ) :
    Integrable (generalizedNormalPDFReal m s p) := by
  by_cases h : 0 < s ∧ 0 < p
  · simpa using (integrable_generalizedNormalPDFReal_mul_rpow_abs_sub_iff (q := 0) h.1 h.2 m).mpr
      (by norm_num)
  · rw [show generalizedNormalPDFReal m s p = 0 from
      funext fun x => generalizedNormalPDFReal_of_not_pos h m x]
    exact integrable_zero _ _ _

/-- For positive scale and shape the density integrates to `1`. -/
theorem integral_generalizedNormalPDFReal (hs : 0 < s) (hp : 0 < p) (m : ℝ) :
    ∫ x, generalizedNormalPDFReal m s p x = 1 := by
  have h := integral_generalizedNormalPDFReal_mul_rpow_abs_sub (q := 0) hs hp (by norm_num) m
  simp only [Real.rpow_zero, mul_one, zero_add, one_div, one_mul] at h
  rw [h, div_self (Real.Gamma_pos_of_pos (inv_pos.mpr hp)).ne']

/-- For positive scale and shape the `ℝ≥0∞`-valued density has total mass `1`. -/
theorem lintegral_generalizedNormalPDF_eq_one (hs : 0 < s) (hp : 0 < p) (m : ℝ) :
    ∫⁻ x, generalizedNormalPDF m s p x = 1 := by
  simp_rw [generalizedNormalPDF_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_generalizedNormalPDFReal m s p)
      (ae_of_all _ (generalizedNormalPDFReal_nonneg m s p)),
    integral_generalizedNormalPDFReal hs hp m, ENNReal.ofReal_one]

/-! ### The law -/

/-- The generalized normal law with location `m`, scale `s` and shape `p`. It is the zero
measure unless `0 < s` and `0 < p`. -/
def generalizedNormalMeasure (m s p : ℝ) : Measure ℝ :=
  volume.withDensity (generalizedNormalPDF m s p)

/-- The defining presentation of the generalized normal law as a `Measure.withDensity`. -/
theorem generalizedNormalMeasure_eq_withDensity (m s p : ℝ) :
    generalizedNormalMeasure m s p = volume.withDensity (generalizedNormalPDF m s p) := by
  rw [generalizedNormalMeasure]

/-- Generalized normal laws have no atoms, including at invalid parameters. -/
instance (m s p : ℝ) : NullSingletonClass (generalizedNormalMeasure m s p) := by
  rw [generalizedNormalMeasure_eq_withDensity]
  infer_instance

/-- Outside the valid parameter range the generalized normal law is the zero measure. -/
@[simp]
theorem generalizedNormalMeasure_of_not_pos (h : ¬ (0 < s ∧ 0 < p)) (m : ℝ) :
    generalizedNormalMeasure m s p = 0 := by
  have h0 : generalizedNormalPDF m s p = 0 := funext (generalizedNormalPDF_of_not_pos h m)
  rw [generalizedNormalMeasure_eq_withDensity, h0, withDensity_zero]

/-- For positive scale and shape the generalized normal law is a probability measure. -/
theorem isProbabilityMeasure_generalizedNormalMeasure (hs : 0 < s) (hp : 0 < p) (m : ℝ) :
    IsProbabilityMeasure (generalizedNormalMeasure m s p) := by
  constructor
  rw [generalizedNormalMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_generalizedNormalPDF_eq_one hs hp m]

/-- The generalized normal law is a probability measure exactly at positive scale and shape. -/
@[simp]
theorem isProbabilityMeasure_generalizedNormalMeasure_iff :
    IsProbabilityMeasure (generalizedNormalMeasure m s p) ↔ 0 < s ∧ 0 < p := by
  refine ⟨fun h => ?_, fun h => isProbabilityMeasure_generalizedNormalMeasure h.1 h.2 m⟩
  by_contra hsp
  rw [generalizedNormalMeasure_of_not_pos hsp] at h
  exact not_isProbabilityMeasure_zero h

/-- The generalized normal law is a finite measure at every parameter. -/
instance (m s p : ℝ) : IsFiniteMeasure (generalizedNormalMeasure m s p) := by
  by_cases h : 0 < s ∧ 0 < p
  · have := isProbabilityMeasure_generalizedNormalMeasure h.1 h.2 m
    infer_instance
  · rw [generalizedNormalMeasure_of_not_pos h]
    infer_instance

/-! ### Transfer to the density -/

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function is integrable against a generalized normal law exactly when its density-weighted
version is Lebesgue integrable. This holds at every parameter. -/
theorem integrable_generalizedNormalMeasure_iff (m s p : ℝ) {g : ℝ → E} :
    Integrable g (generalizedNormalMeasure m s p) ↔
      Integrable fun x => generalizedNormalPDFReal m s p x • g x := by
  rw [generalizedNormalMeasure_eq_withDensity, funext (generalizedNormalPDF_eq_ofReal m s p)]
  exact integrable_withDensity_ofReal_iff (measurable_generalizedNormalPDFReal m s p).aemeasurable
    (ae_of_all _ (generalizedNormalPDFReal_nonneg m s p))

/-- An integral against a generalized normal law is the density-weighted Lebesgue integral. This
holds at every parameter. -/
theorem integral_generalizedNormalMeasure_eq (m s p : ℝ) (g : ℝ → E) :
    ∫ x, g x ∂generalizedNormalMeasure m s p = ∫ x, generalizedNormalPDFReal m s p x • g x := by
  rw [generalizedNormalMeasure_eq_withDensity, funext (generalizedNormalPDF_eq_ofReal m s p)]
  exact integral_withDensity_ofReal (measurable_generalizedNormalPDFReal m s p).aemeasurable
    (ae_of_all _ (generalizedNormalPDFReal_nonneg m s p)) g

end Transfer

/-! ### Absolute central moments -/

/-- **The absolute-moment threshold.** For positive scale and shape, `|X - m| ^ q` is integrable
under the generalized normal law exactly when `-1 < q`. -/
theorem integrable_rpow_abs_sub_generalizedNormalMeasure_iff (hs : 0 < s) (hp : 0 < p) (m : ℝ) :
    Integrable (fun x => |x - m| ^ q) (generalizedNormalMeasure m s p) ↔ -1 < q := by
  rw [integrable_generalizedNormalMeasure_iff]
  simp_rw [smul_eq_mul]
  exact integrable_generalizedNormalPDFReal_mul_rpow_abs_sub_iff hs hp m

/-- **The absolute central moments of a generalized normal law.** For positive scale and shape
and `-1 < q`, `E |X - m| ^ q = s ^ q * Γ ((q + 1) / p) / Γ (1 / p)`. -/
theorem integral_rpow_abs_sub_generalizedNormalMeasure (hs : 0 < s) (hp : 0 < p) (hq : -1 < q)
    (m : ℝ) :
    ∫ x, |x - m| ^ q ∂generalizedNormalMeasure m s p =
      s ^ q * Real.Gamma ((q + 1) / p) / Real.Gamma p⁻¹ := by
  rw [integral_generalizedNormalMeasure_eq]
  simp_rw [smul_eq_mul]
  exact integral_generalizedNormalPDFReal_mul_rpow_abs_sub hs hp hq m

/-! ### Absolute continuity -/

section Density

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a generalized normal law has a density. -/
theorem hasPDF_of_hasLaw_generalizedNormalMeasure
    (hX : HasLaw X (generalizedNormalMeasure m s p) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_generalizedNormalPDF m s p).aemeasurable hX

/-- The density of a generalized normal law is `generalizedNormalPDF`. -/
theorem pdf_eq_generalizedNormalPDF_of_hasLaw_generalizedNormalMeasure
    (hX : HasLaw X (generalizedNormalMeasure m s p) P) :
    pdf X P volume =ᵐ[volume] generalizedNormalPDF m s p :=
  pdf_eq_of_hasLaw_withDensity (measurable_generalizedNormalPDF m s p).aemeasurable hX

end Density

/-- The Radon–Nikodym derivative of a generalized normal law against Lebesgue measure is
`generalizedNormalPDF`. -/
theorem rnDeriv_generalizedNormalMeasure (m s p : ℝ) :
    (generalizedNormalMeasure m s p).rnDeriv volume =ᵐ[volume] generalizedNormalPDF m s p := by
  rw [generalizedNormalMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ (measurable_generalizedNormalPDF m s p)

/-! ### Measurability in the parameters -/

/-- The totalized generalized normal family is measurable in its three parameters, so it can be
packaged as a kernel. -/
@[fun_prop]
theorem measurable_generalizedNormalMeasure :
    Measurable fun θ : ℝ × ℝ × ℝ => generalizedNormalMeasure θ.1 θ.2.1 θ.2.2 := by
  simp_rw [generalizedNormalMeasure_eq_withDensity]
  exact measurable_withDensity (μ := volume)
    measurable_uncurry_generalizedNormalPDFReal.ennreal_ofReal

end TauCeti.Probability
