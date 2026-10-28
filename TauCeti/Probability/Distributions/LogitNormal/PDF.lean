/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LogitNormal.Basic
public import TauCeti.Probability.Density
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Density and support of logit-normal laws

At nonzero Gaussian variance, the logit-normal density is the Gaussian density at the logit,
divided by `x * (1 - x)` on the open unit interval, and zero elsewhere. The change of variables
along the sigmoid establishes the measure identity, hence the `HasPDF` and Radon–Nikodym APIs.
Its topological support is the closed unit interval despite its almost-sure open carrier.
At zero variance the chosen density vanishes and the law is a singular Dirac mass instead.

The substitution uses `TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul`, as in the
log-normal density calculation in `TauCeti.Probability.Distributions.LogNormal.Basic`.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {v : ℝ≥0} {x : ℝ}

/-- The real logit-normal density, zero off the open unit interval and at zero variance. -/
def logitNormalPDFReal (m : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  if x ∈ Ioo 0 1 then gaussianPDFReal m v (Real.log (x / (1 - x))) / (x * (1 - x)) else 0

/-- The extended nonnegative logit-normal density. -/
def logitNormalPDF (m : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (logitNormalPDFReal m v x)

/-- The extended density is the `ENNReal.ofReal` lift of the real density. -/
theorem logitNormalPDF_eq_ofReal (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    logitNormalPDF m v x = ENNReal.ofReal (logitNormalPDFReal m v x) := (rfl)

/-- On the open unit interval, the density is the Gaussian density at the logit times the
Jacobian of the logit. -/
@[simp]
theorem logitNormalPDFReal_of_mem (hx : x ∈ Ioo 0 1) (m : ℝ) (v : ℝ≥0) :
    logitNormalPDFReal m v x =
      gaussianPDFReal m v (Real.log (x / (1 - x))) / (x * (1 - x)) := by
  rw [logitNormalPDFReal, ite_eq_left hx]

/-- The real density vanishes off the open unit interval. -/
@[simp]
theorem logitNormalPDFReal_of_notMem (hx : x ∉ Ioo 0 1) (m : ℝ) (v : ℝ≥0) :
    logitNormalPDFReal m v x = 0 := by
  rw [logitNormalPDFReal, ite_eq_right hx]

/-- The real density vanishes at zero Gaussian variance. -/
@[simp]
theorem logitNormalPDFReal_zero_var (m x : ℝ) : logitNormalPDFReal m 0 x = 0 := by
  simp [logitNormalPDFReal]

/-- The logit-normal density is nonnegative. -/
theorem logitNormalPDFReal_nonneg (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    0 ≤ logitNormalPDFReal m v x := by
  unfold logitNormalPDFReal
  split_ifs with hx
  · exact div_nonneg (gaussianPDFReal_nonneg _ _ _) (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))
  · exact le_rfl

/-- The density is strictly positive at nonzero variance inside the unit interval. -/
theorem logitNormalPDFReal_pos (m : ℝ) (hv : v ≠ 0) (hx : x ∈ Ioo 0 1) :
    0 < logitNormalPDFReal m v x := by
  rw [logitNormalPDFReal_of_mem hx]
  exact div_pos (gaussianPDFReal_pos _ _ _ hv) (mul_pos hx.1 (sub_pos.mpr hx.2))

/-- The real density is jointly measurable in location, variance, and observation. -/
@[fun_prop]
theorem measurable_uncurry_logitNormalPDFReal :
    Measurable (fun p : ℝ × ℝ≥0 × ℝ ↦ logitNormalPDFReal p.1 p.2.1 p.2.2) := by
  unfold logitNormalPDFReal
  exact Measurable.ite (measurableSet_Ioo.preimage (by fun_prop)) (by fun_prop) measurable_const

/-- The real density is measurable in its observation. -/
@[fun_prop]
theorem measurable_logitNormalPDFReal (m : ℝ) (v : ℝ≥0) :
    Measurable (logitNormalPDFReal m v) := by
  exact measurable_uncurry_logitNormalPDFReal.comp
    (by fun_prop : Measurable (fun x : ℝ ↦ (m, v, x)))

/-- The extended density is measurable in its observation. -/
@[fun_prop]
theorem measurable_logitNormalPDF (m : ℝ) (v : ℝ≥0) : Measurable (logitNormalPDF m v) :=
  (measurable_logitNormalPDFReal m v).ennreal_ofReal

/-- Taking the real part of the extended density recovers the real density. -/
@[simp]
theorem toReal_logitNormalPDF (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    (logitNormalPDF m v x).toReal = logitNormalPDFReal m v x :=
  ENNReal.toReal_ofReal (logitNormalPDFReal_nonneg m v x)

private theorem sigmoid_jacobian_mul_pdf (m : ℝ) (v : ℝ≥0) (y : ℝ) :
    ENNReal.ofReal |Real.sigmoid y * (1 - Real.sigmoid y)| *
      logitNormalPDF m v (Real.sigmoid y) = gaussianPDF m v y := by
  have hpos : 0 < Real.sigmoid y * (1 - Real.sigmoid y) :=
    mul_pos (Real.sigmoid_pos y) (sub_pos.mpr (Real.sigmoid_lt_one y))
  rw [abs_of_pos hpos, logitNormalPDF, gaussianPDF, ← ENNReal.ofReal_mul hpos.le,
    logitNormalPDFReal_of_mem ⟨Real.sigmoid_pos y, Real.sigmoid_lt_one y⟩,
    Real.log_sigmoid_div_one_sub, mul_div_cancel₀ _ hpos.ne']

/-- At nonzero variance, the sigmoid pushforward has the named logit-normal density. -/
theorem logitNormalMeasure_eq_withDensity (m : ℝ) (hv : v ≠ 0) :
    logitNormalMeasure m v = volume.withDensity (logitNormalPDF m v) := by
  have hmap := MeasureTheory.map_withDensity_abs_deriv_mul (f := logitNormalPDF m v)
    MeasurableSet.univ (by fun_prop)
    (fun y _ ↦ (Real.hasDerivAt_sigmoid y).hasDerivWithinAt) Real.sigmoid_injective.injOn
  simp only [Measure.restrict_univ, sigmoid_jacobian_mul_pdf, image_univ,
    Real.range_sigmoid] at hmap
  rw [logitNormalMeasure_def, gaussianReal_of_var_ne_zero m hv, hmap,
    ← withDensity_indicator measurableSet_Ioo]
  congr 1
  ext x
  by_cases hx : x ∈ Ioo 0 1 <;> simp [hx, logitNormalPDF]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {m : ℝ}

/-- A variable with a nondegenerate logit-normal law has a density against volume. -/
theorem hasPDF_of_hasLaw_logitNormalMeasure (hv : v ≠ 0)
    (hX : HasLaw X (logitNormalMeasure m v) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_logitNormalPDF m v).aemeasurable
    (by rwa [logitNormalMeasure_eq_withDensity m hv] at hX)

/-- The random-variable PDF is the named logit-normal density almost everywhere. -/
theorem pdf_eq_logitNormalPDF_of_hasLaw_logitNormalMeasure (hv : v ≠ 0)
    (hX : HasLaw X (logitNormalMeasure m v) P) : pdf X P volume =ᵐ[volume] logitNormalPDF m v :=
  pdf_eq_of_hasLaw_withDensity (measurable_logitNormalPDF m v).aemeasurable
    (by rwa [logitNormalMeasure_eq_withDensity m hv] at hX)

/-- The Radon–Nikodym derivative against volume is the named density. -/
theorem rnDeriv_logitNormalMeasure (m : ℝ) (hv : v ≠ 0) :
    (logitNormalMeasure m v).rnDeriv volume =ᵐ[volume] logitNormalPDF m v := by
  rw [logitNormalMeasure_eq_withDensity m hv]
  exact Measure.rnDeriv_withDensity volume (measurable_logitNormalPDF m v)

/-- A nondegenerate logit-normal law has topological support equal to the closed unit interval. -/
@[simp]
theorem support_logitNormalMeasure (m : ℝ) (hv : v ≠ 0) :
    (logitNormalMeasure m v).support = Icc 0 1 := by
  rw [logitNormalMeasure_eq_withDensity m hv,
    Measure.support_withDensity_eq_closure (measurable_logitNormalPDF m v) isOpen_Ioo,
    closure_Ioo zero_ne_one]
  ext x
  by_cases hx : x ∈ Ioo 0 1
  · simp only [Function.mem_support, logitNormalPDF, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact iff_of_true (logitNormalPDFReal_pos m hv hx) hx
  · simp [Function.mem_support, logitNormalPDF, hx]

/-- The zero-variance boundary is singular with respect to Lebesgue measure. -/
theorem mutuallySingular_logitNormalMeasure_zero_var (m : ℝ) :
    logitNormalMeasure m 0 ⟂ₘ volume := by
  rw [logitNormalMeasure_zero_var]
  exact mutuallySingular_dirac _ _

end TauCeti.Probability
