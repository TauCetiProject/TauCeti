/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.IrwinHall.Cdf
public import TauCeti.Probability.Density
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Densities of Irwin–Hall laws

For order at least two, the Irwin–Hall density is an alternating finite sum of truncated
powers of degree one less than the order. This expression is continuous at every integer
knot, including the endpoints of the support. Order one uses the unit-uniform density;
order zero is a Dirac law and its chosen pdf is zero.

The density represents the convolution law as Lebesgue measure with density. The file also
supplies cdf derivatives, normalization, and the random-variable and Radon–Nikodym interfaces.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 26.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

/-- The real Irwin–Hall density. Order one uses the unit-uniform density, and the atomic
order-zero law has chosen density zero. -/
def irwinHallPDFReal (n : ℕ) (x : ℝ) : ℝ :=
  if n = 0 then 0 else if n = 1 then uniformPDFReal 0 1 x else
    (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) *
      max (x - k) 0 ^ (n - 1)) / (n - 1).factorial

/-- The extended nonnegative Irwin–Hall density. It represents the law only at positive order. -/
def irwinHallPDF (n : ℕ) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (irwinHallPDFReal n x)

/-- The extended density is the `ENNReal.ofReal` lift of the real density. -/
theorem irwinHallPDF_eq_ofReal (n : ℕ) (x : ℝ) :
    irwinHallPDF n x = ENNReal.ofReal (irwinHallPDFReal n x) := (rfl)

/-- The atomic order-zero law has chosen real density zero. -/
@[simp]
theorem irwinHallPDFReal_zero (x : ℝ) : irwinHallPDFReal 0 x = 0 := by
  simp [irwinHallPDFReal]

/-- At order one the real density is the unit-uniform density. -/
@[simp]
theorem irwinHallPDFReal_one (x : ℝ) :
    irwinHallPDFReal 1 x = uniformPDFReal 0 1 x := by
  simp [irwinHallPDFReal]

/-- At order at least two the density is the classical alternating truncated-power sum. -/
theorem irwinHallPDFReal_eq {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    irwinHallPDFReal n x =
      (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) *
        max (x - k) 0 ^ (n - 1)) / (n - 1).factorial := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp [irwinHallPDFReal, h0, h1]

/-- The chosen density vanishes at and below zero, including the order-zero convention. -/
@[simp]
theorem irwinHallPDFReal_of_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    irwinHallPDFReal n x = 0 := by
  by_cases h0 : n = 0
  · subst n
    simp
  by_cases h1 : n = 1
  · subst n
    rw [irwinHallPDFReal_one, uniformPDFReal_of_notMem (by
      rintro ⟨hpos, _⟩
      exact (not_lt_of_ge hx) hpos)]
  rw [irwinHallPDFReal_eq (by omega)]
  have hp : n - 1 ≠ 0 := by omega
  have hterm (k : ℕ) : max (x - k) 0 ^ (n - 1) = 0 := by
    rw [max_eq_right (sub_nonpos.mpr (hx.trans (Nat.cast_nonneg k))), zero_pow hp]
  simp [hterm]

/-- Densities of order at least two are continuous, including at integer knots. -/
@[fun_prop]
theorem continuous_irwinHallPDFReal {n : ℕ} (hn : 2 ≤ n) :
    Continuous (irwinHallPDFReal n) := by
  rw [funext (irwinHallPDFReal_eq hn)]
  fun_prop

/-- Every chosen real Irwin–Hall density is measurable. -/
@[fun_prop]
theorem measurable_irwinHallPDFReal (n : ℕ) : Measurable (irwinHallPDFReal n) := by
  rcases n with _ | n
  · rw [funext irwinHallPDFReal_zero]
    exact measurable_const
  rcases n with _ | n
  · rw [funext irwinHallPDFReal_one]
    exact measurable_uniformPDFReal
  · exact (continuous_irwinHallPDFReal (by omega)).measurable

/-- Every extended Irwin–Hall density is measurable. -/
@[fun_prop]
theorem measurable_irwinHallPDF (n : ℕ) : Measurable (irwinHallPDF n) :=
  (measurable_irwinHallPDFReal n).ennreal_ofReal

/-- The interval integral of the Irwin–Hall density is the difference of cdf values
at order at least two. -/
theorem intervalIntegral_irwinHallPDFReal {n : ℕ} (hn : 2 ≤ n) (a b : ℝ) :
    (∫ x in a..b, irwinHallPDFReal n x) =
      cdf (irwinHallMeasure n) b - cdf (irwinHallMeasure n) a := by
  have hint (k : ℕ) : IntervalIntegrable
      (fun x : ℝ ↦ (-1 : ℝ) ^ k * (n.choose k : ℝ) * max (x - k) 0 ^ (n - 1))
      volume a b := (by fun_prop : Continuous _).intervalIntegrable _ _
  simp_rw [irwinHallPDFReal_eq hn]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum (fun k _ ↦ hint k)]
  have hp : 0 < n - 1 := by omega
  have hsucc : n - 1 + 1 = n := by omega
  have hsuccR : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hsucc
  have hfac : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : n ≠ 0)).symm
  simp_rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ max x 0 ^ (n - 1)),
    TauCeti.intervalIntegral.integral_max_zero_pow hp, hsucc, hsuccR]
  rw [cdf_irwinHallMeasure_eq (by omega), cdf_irwinHallMeasure_eq (by omega), hfac]
  simp only [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  field_simp

/-- The cdf has the named density as its derivative everywhere at order at least two. -/
theorem hasDerivAt_cdf_irwinHallMeasure {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    HasDerivAt (cdf (irwinHallMeasure n)) (irwinHallPDFReal n x) x := by
  have hc := continuous_irwinHallPDFReal hn
  have heq : ⇑(cdf (irwinHallMeasure n)) =
      fun y ↦ cdf (irwinHallMeasure n) 0 + ∫ t in 0..y, irwinHallPDFReal n t := by
    ext y
    rw [intervalIntegral_irwinHallPDFReal hn]
    ring
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

/-- The real Irwin–Hall density is nonnegative for every order. -/
theorem irwinHallPDFReal_nonneg (n : ℕ) (x : ℝ) : 0 ≤ irwinHallPDFReal n x := by
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · rw [irwinHallPDFReal_one]
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · rw [uniformPDFReal_of_mem hx]
      norm_num
    · rw [uniformPDFReal_of_notMem hx]
  · exact (hasDerivAt_cdf_irwinHallMeasure (by omega) x).nonneg_of_monotone
      (cdf (irwinHallMeasure (n + 2))).mono

/-- Taking the real value of the extended density recovers the real density. -/
@[simp]
theorem toReal_irwinHallPDF (n : ℕ) (x : ℝ) :
    (irwinHallPDF n x).toReal = irwinHallPDFReal n x := by
  rw [irwinHallPDF_eq_ofReal, ENNReal.toReal_ofReal (irwinHallPDFReal_nonneg n x)]

/-- From order two onward the continuous density vanishes at and above its upper endpoint. -/
@[simp]
theorem irwinHallPDFReal_of_natCast_le {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : (n : ℝ) ≤ x) :
    irwinHallPDFReal n x = 0 := by
  have hs : Iic x =ᵐ[irwinHallMeasure n] univ := Filter.eventuallyEqSet_univ.2 (by
    filter_upwards [ae_mem_Icc_irwinHallMeasure n] with y hy
    exact hy.2.trans hx)
  have hone : cdf (irwinHallMeasure n) x = 1 := by
    rw [cdf_eq_real, measureReal_congr hs, probReal_univ]
  have hmax : IsMaxOn (cdf (irwinHallMeasure n)) univ x := fun y _ ↦ by
    rw [hone]
    exact cdf_le_one _ _
  exact (hmax.isLocalMax (Filter.univ_mem)).hasDerivAt_eq_zero
    (hasDerivAt_cdf_irwinHallMeasure hn x)

/-- Every positive-order Irwin–Hall law is Lebesgue measure weighted by its named density. -/
theorem irwinHallMeasure_eq_withDensity {n : ℕ} (hn : 0 < n) :
    irwinHallMeasure n = volume.withDensity (irwinHallPDF n) := by
  by_cases h1 : n = 1
  · subst n
    rw [irwinHallMeasure_one, uniformMeasure_eq_withDensity]
    congr 1
    ext x
    simp [uniformPDF_eq_ofReal_uniformPDFReal, irwinHallPDF_eq_ofReal]
  have hn2 : 2 ≤ n := by omega
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [← measure_cdf (irwinHallMeasure n), StieltjesFunction.measure_Ioc,
    withDensity_apply _ measurableSet_Ioc]
  simp_rw [irwinHallPDF_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((continuous_irwinHallPDFReal hn2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ (irwinHallPDFReal_nonneg n)),
    ← intervalIntegral.integral_of_le hab.le, intervalIntegral_irwinHallPDFReal hn2]

/-- Every chosen real Irwin–Hall density is integrable against Lebesgue measure. -/
theorem integrable_irwinHallPDFReal (n : ℕ) : Integrable (irwinHallPDFReal n) := by
  by_cases hn : n = 0
  · subst n
    rw [funext irwinHallPDFReal_zero]
    exact integrable_zero _ _ _
  exact integrable_of_eq_withDensity (irwinHallMeasure_eq_withDensity (Nat.pos_of_ne_zero hn))
    (measurable_irwinHallPDFReal n).aemeasurable (ae_of_all _ (irwinHallPDFReal_nonneg n))

/-- The real density of a positive-order Irwin–Hall law integrates to one. -/
theorem integral_irwinHallPDFReal {n : ℕ} (hn : 0 < n) :
    ∫ x, irwinHallPDFReal n x = 1 := by
  have hμ := irwinHallMeasure_eq_withDensity hn
  have hfi := integrable_irwinHallPDFReal n
  have hmass := measureReal_withDensity_ofReal
    (s := univ) (ae_of_all _ (irwinHallPDFReal_nonneg n)) MeasurableSet.univ hfi.integrableOn
  simpa [← irwinHallPDF_eq_ofReal, ← hμ] using hmass.symm

/-- A variable with positive-order Irwin–Hall law has a density. -/
theorem hasPDF_of_hasLaw_irwinHallMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {n : ℕ} (hn : 0 < n)
    (hX : HasLaw X (irwinHallMeasure n) P) : HasPDF X P := by
  rw [irwinHallMeasure_eq_withDensity hn] at hX
  exact hasPDF_of_hasLaw_withDensity (measurable_irwinHallPDF n).aemeasurable hX

/-- The Radon–Nikodym derivative is the named density, including zero at the atomic order. -/
theorem rnDeriv_irwinHallMeasure (n : ℕ) :
    (irwinHallMeasure n).rnDeriv volume =ᵐ[volume] irwinHallPDF n := by
  by_cases hn : n = 0
  · subst n
    rw [irwinHallMeasure_zero]
    have hzero : irwinHallPDF 0 = fun _ ↦ 0 := by
      ext x
      simp [irwinHallPDF_eq_ofReal]
    rw [hzero]
    exact Measure.rnDeriv_eq_zero_of_mutuallySingular (mutuallySingular_dirac 0 volume)
      Measure.AbsolutelyContinuous.rfl
  rw [irwinHallMeasure_eq_withDensity (Nat.pos_of_ne_zero hn)]
  exact Measure.rnDeriv_withDensity volume (measurable_irwinHallPDF n)

/-- The canonical pdf of an Irwin–Hall variable is the named density at every order.
At order zero both vanish; this does not assert absolute continuity of that Dirac law. -/
theorem pdf_eq_irwinHallPDF_of_hasLaw_irwinHallMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {n : ℕ}
    (hX : HasLaw X (irwinHallMeasure n) P) : pdf X P =ᵐ[volume] irwinHallPDF n := by
  rw [pdf_def, hX.map_eq]
  exact rnDeriv_irwinHallMeasure n

end TauCeti.Probability
