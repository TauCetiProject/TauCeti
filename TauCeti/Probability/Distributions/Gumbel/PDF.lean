/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.Gumbel.Basic
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The density of the Gumbel distribution

For positive scale `s`, the Gumbel law with location `m` has density

`exp (-y) * exp (-exp (-y)) / s`, where `y = (x - m) / s`.

This file derives the density from the defining exponential pushforward.  The change of variables
`e ↦ m - s * log e` sends the positive half-line onto the real line, and its Jacobian cancels
the leading exponential factor in the Gumbel density.  For nonpositive scale, both the totalized
law and its density vanish.

The resulting measure identity supplies the standard `HasPDF`, `pdf`, and Radon–Nikodym
interfaces used by density-based constructions.

## Main results

* `TauCeti.Probability.gumbelPDFReal` and `TauCeti.Probability.gumbelPDF` are the real- and
  `ℝ≥0∞`-valued densities;
* `TauCeti.Probability.gumbelMeasure_eq_withDensity` identifies the Gumbel law with Lebesgue
  measure weighted by its density;
* `TauCeti.Probability.hasPDF_of_hasLaw_gumbelMeasure`,
  `TauCeti.Probability.pdf_eq_gumbelPDF_of_hasLaw_gumbelMeasure`, and
  `TauCeti.Probability.rnDeriv_gumbelMeasure` provide the usual density API.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), ch. 22.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal

namespace TauCeti.Probability

variable {m s x : ℝ}

/-! ### Densities -/

/-- The real-valued density of the Gumbel law with location `m` and scale `s`.

For nonpositive scale it is zero, matching the totalized measure. -/
def gumbelPDFReal (m s x : ℝ) : ℝ :=
  if 0 < s then
    Real.exp (-((x - m) / s)) * Real.exp (-Real.exp (-((x - m) / s))) / s
  else 0

/-- The `ℝ≥0∞`-valued density of the Gumbel law. -/
def gumbelPDF (m s x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gumbelPDFReal m s x)

/-- The `ℝ≥0∞`-valued Gumbel density is `ENNReal.ofReal` of the real-valued one. -/
theorem gumbelPDF_eq_ofReal (m s x : ℝ) :
    gumbelPDF m s x = ENNReal.ofReal (gumbelPDFReal m s x) :=
  (rfl)

/-- The Gumbel density is finite. -/
@[simp]
theorem gumbelPDF_ne_top (m s x : ℝ) : gumbelPDF m s x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The Gumbel density vanishes for nonpositive scale. -/
@[simp]
theorem gumbelPDFReal_of_nonpos (hs : s ≤ 0) (m x : ℝ) : gumbelPDFReal m s x = 0 := by
  rw [gumbelPDFReal, ite_eq_right (not_lt.mpr hs)]

/-- For positive scale, the real Gumbel density has its classical formula. -/
@[simp]
theorem gumbelPDFReal_of_pos (hs : 0 < s) (m x : ℝ) :
    gumbelPDFReal m s x =
      Real.exp (-((x - m) / s)) * Real.exp (-Real.exp (-((x - m) / s))) / s := by
  rw [gumbelPDFReal, ite_eq_left hs]

/-- The `ℝ≥0∞`-valued Gumbel density vanishes for nonpositive scale. -/
@[simp]
theorem gumbelPDF_of_nonpos (hs : s ≤ 0) (m x : ℝ) : gumbelPDF m s x = 0 := by
  rw [gumbelPDF, gumbelPDFReal_of_nonpos hs, ENNReal.ofReal_zero]

/-- For positive scale, the `ℝ≥0∞`-valued Gumbel density has its classical formula. -/
@[simp]
theorem gumbelPDF_of_pos (hs : 0 < s) (m x : ℝ) :
    gumbelPDF m s x = ENNReal.ofReal
      (Real.exp (-((x - m) / s)) * Real.exp (-Real.exp (-((x - m) / s))) / s) := by
  rw [gumbelPDF, gumbelPDFReal_of_pos hs]

/-- The real Gumbel density is nonnegative for all parameters. -/
theorem gumbelPDFReal_nonneg (m s x : ℝ) : 0 ≤ gumbelPDFReal m s x := by
  rcases le_or_gt s 0 with hs | hs
  · rw [gumbelPDFReal_of_nonpos hs]
  · rw [gumbelPDFReal_of_pos hs]
    positivity

/-- A positive-scale Gumbel density is strictly positive everywhere. -/
theorem gumbelPDFReal_pos (hs : 0 < s) (m x : ℝ) : 0 < gumbelPDFReal m s x := by
  rw [gumbelPDFReal_of_pos hs]
  positivity

/-- The `ℝ≥0∞`-valued Gumbel density is strictly positive at positive scale. -/
theorem gumbelPDF_pos (hs : 0 < s) (m x : ℝ) : 0 < gumbelPDF m s x := by
  rw [gumbelPDF_eq_ofReal, ENNReal.ofReal_pos]
  exact gumbelPDFReal_pos hs m x

/-- Converting the extended nonnegative Gumbel density to `ℝ` recovers `gumbelPDFReal`. -/
@[simp]
theorem toReal_gumbelPDF (m s x : ℝ) : (gumbelPDF m s x).toReal = gumbelPDFReal m s x := by
  rw [gumbelPDF, ENNReal.toReal_ofReal (gumbelPDFReal_nonneg m s x)]

/-- The Gumbel density is jointly measurable in the location, scale, and evaluation point. -/
@[fun_prop]
theorem measurable_uncurry_gumbelPDFReal :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ gumbelPDFReal q.1.1 q.1.2 q.2 := by
  unfold gumbelPDFReal
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst.snd) (by fun_prop)
    measurable_const

/-- The `ℝ≥0∞`-valued Gumbel density is jointly measurable in all its arguments. -/
@[fun_prop]
theorem measurable_uncurry_gumbelPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ gumbelPDF q.1.1 q.1.2 q.2 :=
  measurable_uncurry_gumbelPDFReal.ennreal_ofReal

/-- The real-valued Gumbel density is measurable. -/
@[fun_prop]
theorem measurable_gumbelPDFReal (m s : ℝ) : Measurable (gumbelPDFReal m s) :=
  measurable_uncurry_gumbelPDFReal.comp (measurable_prodMk_left (x := (m, s)))

/-- The `ℝ≥0∞`-valued Gumbel density is measurable. -/
@[fun_prop]
theorem measurable_gumbelPDF (m s : ℝ) : Measurable (gumbelPDF m s) :=
  (measurable_gumbelPDFReal m s).ennreal_ofReal

/-! ### Density of the measure -/

private theorem image_gumbelTransform_Ioi (hs : 0 < s) (m : ℝ) :
    (fun e : ℝ ↦ m - s * Real.log e) '' Ioi 0 = univ := by
  apply eq_univ_of_forall
  intro x
  refine ⟨Real.exp ((m - x) / s), Real.exp_pos _, ?_⟩
  dsimp only
  rw [Real.log_exp]
  field_simp
  ring

private theorem gumbelTransform_injOn (hs : 0 < s) (m : ℝ) :
    InjOn (fun e : ℝ ↦ m - s * Real.log e) (Ioi 0) := by
  intro a ha b hb hab
  exact Real.log_injOn_pos ha hb (mul_left_cancel₀ hs.ne' (by linarith))

private theorem gumbelTransform_weight (hs : 0 < s) (m : ℝ) (e : ℝ) (he : 0 < e) :
    ENNReal.ofReal |-(s / e)| * gumbelPDF m s (m - s * Real.log e) = exponentialPDF 1 e := by
  rw [gumbelPDF_of_pos hs, exponentialPDF_of_nonneg he.le]
  have hstandard : -((m - s * Real.log e - m) / s) = Real.log e := by
    field_simp
    ring
  rw [hstandard, Real.exp_log he, one_mul, abs_neg, abs_of_pos (div_pos hs he),
    ← ENNReal.ofReal_mul (div_nonneg hs.le he.le)]
  congr 1
  field_simp

/-- The Gumbel law is Lebesgue measure weighted by `gumbelPDF`, for every parameter value. -/
theorem gumbelMeasure_eq_withDensity (m s : ℝ) :
    gumbelMeasure m s = volume.withDensity (gumbelPDF m s) := by
  rcases le_or_gt s 0 with hs | hs
  · have hpdf : gumbelPDF m s = 0 := funext fun x ↦ by
      rw [gumbelPDF_of_nonpos hs, Pi.zero_apply]
    rw [gumbelMeasure_of_nonpos hs, hpdf, withDensity_zero]
  · have hmap := TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul
      (s := Ioi (0 : ℝ)) (φ := fun e : ℝ ↦ m - s * Real.log e)
      (φ' := fun e : ℝ ↦ -(s / e)) (f := gumbelPDF m s) measurableSet_Ioi (by fun_prop)
      (fun e he ↦ by
        have hderiv := ((Real.hasDerivAt_log he.ne').const_mul s).const_sub m
        simpa [div_eq_mul_inv] using hderiv.hasDerivWithinAt)
      (gumbelTransform_injOn hs m)
    have hweight :
        (fun e : ℝ ↦ ENNReal.ofReal |-(s / e)| * gumbelPDF m s (m - s * Real.log e))
          =ᵐ[volume.restrict (Ioi 0)] exponentialPDF 1 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with e he
      exact gumbelTransform_weight hs m e he
    rw [withDensity_congr_ae hweight, image_gumbelTransform_Ioi hs m,
      Measure.restrict_univ] at hmap
    rw [gumbelMeasure_of_pos hs, expMeasure_eq_withDensity_restrict_Ioi, hmap]

/-- The `ℝ≥0∞`-valued Gumbel density has total mass `1` at positive scale. -/
theorem lintegral_gumbelPDF_eq_one (hs : 0 < s) (m : ℝ) :
    ∫⁻ x, gumbelPDF m s x = 1 := by
  let _ := isProbabilityMeasure_gumbelMeasure hs m
  have h : gumbelMeasure m s Set.univ = 1 := measure_univ
  rwa [gumbelMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h

/-- The real-valued Gumbel density has integral `1` at positive scale. -/
theorem integral_gumbelPDFReal_eq_one (hs : 0 < s) (m : ℝ) :
    ∫ x, gumbelPDFReal m s x = 1 := by
  simp_rw [← toReal_gumbelPDF]
  rw [integral_toReal (measurable_gumbelPDF m s).aemeasurable
      (ae_of_all _ fun x ↦ lt_top_iff_ne_top.mpr (gumbelPDF_ne_top m s x)),
    lintegral_gumbelPDF_eq_one hs m, ENNReal.toReal_one]

/-- The real-valued Gumbel density is integrable for every scale. -/
theorem integrable_gumbelPDFReal (m s : ℝ) : Integrable (gumbelPDFReal m s) := by
  rcases le_or_gt s 0 with hs | hs
  · have hzero : gumbelPDFReal m s = 0 := funext (gumbelPDFReal_of_nonpos hs m)
    rw [hzero]
    exact integrable_zero ℝ ℝ volume
  · apply Integrable.of_integral_ne_zero
    rw [integral_gumbelPDFReal_eq_one hs m]
    exact one_ne_zero

/-! ### Transfer to the density -/

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function is integrable against a Gumbel measure exactly when its density-weighted version
is Lebesgue integrable. This holds at every scale, including the zero measure. -/
theorem integrable_gumbelMeasure_iff (m s : ℝ) {g : ℝ → E} :
    Integrable g (gumbelMeasure m s) ↔
      Integrable fun y ↦ gumbelPDFReal m s y • g y := by
  rw [gumbelMeasure_eq_withDensity, funext (gumbelPDF_eq_ofReal m s)]
  exact integrable_withDensity_ofReal_iff (measurable_gumbelPDFReal m s).aemeasurable
    (ae_of_all _ (gumbelPDFReal_nonneg m s))

/-- An integral against a Gumbel measure is the density-weighted Lebesgue integral. This holds at
every scale, including the zero measure. -/
theorem integral_gumbelMeasure_eq (m s : ℝ) (g : ℝ → E) :
    ∫ y, g y ∂gumbelMeasure m s = ∫ y, gumbelPDFReal m s y • g y := by
  rw [gumbelMeasure_eq_withDensity, funext (gumbelPDF_eq_ofReal m s)]
  exact integral_withDensity_ofReal (measurable_gumbelPDFReal m s).aemeasurable
    (ae_of_all _ (gumbelPDFReal_nonneg m s)) g

end Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a Gumbel law has density `gumbelPDF`. -/
theorem hasPDF_of_hasLaw_gumbelMeasure (hX : HasLaw X (gumbelMeasure m s) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_gumbelPDF m s).aemeasurable
    (by rwa [gumbelMeasure_eq_withDensity] at hX)

/-- The canonical density of a random variable with Gumbel law is `gumbelPDF`. -/
theorem pdf_eq_gumbelPDF_of_hasLaw_gumbelMeasure (hX : HasLaw X (gumbelMeasure m s) P) :
    pdf X P volume =ᵐ[volume] gumbelPDF m s :=
  pdf_eq_of_hasLaw_withDensity (measurable_gumbelPDF m s).aemeasurable
    (by rwa [gumbelMeasure_eq_withDensity] at hX)

/-- The Radon–Nikodym derivative of a Gumbel law with respect to Lebesgue measure is its density. -/
theorem rnDeriv_gumbelMeasure (m s : ℝ) :
    (gumbelMeasure m s).rnDeriv volume =ᵐ[volume] gumbelPDF m s := by
  rw [gumbelMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_gumbelPDF m s)

end TauCeti.Probability
