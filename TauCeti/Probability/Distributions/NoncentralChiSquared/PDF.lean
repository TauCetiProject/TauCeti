/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralChiSquared.Basic
public import TauCeti.Analysis.SpecialFunctions.BesselI

/-!
# Densities of noncentral chi-squared laws

The Poisson-weighted central densities form a convergent series on the positive half-line.
For positive degree this is the density of the noncentral chi-squared law. At degree zero
it describes only the continuous component; the atom at zero is kept separate.

The modified Bessel representation identifies the usual closed density formula.
Chosen densities vanish at nonpositive arguments and at negative degrees.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Nat

namespace TauCeti.Probability

variable {k x : ℝ} {l : ℝ≥0}

/-- The real density of the continuous component of a noncentral chi-squared law.
At degree zero the atom is excluded; at negative degree the density is zero. -/
def noncentralChiSquaredPDFReal (k : ℝ) (l : ℝ≥0) (x : ℝ) : ℝ :=
  if 0 ≤ k ∧ 0 < x then
    ∑' n : ℕ, (poissonMeasure (l / 2)).real {n} * chiSquaredPDFReal (k + 2 * n) x
  else 0

/-- The extended nonnegative density of the continuous component of a noncentral
chi-squared law. It excludes the atom when the degree is zero. -/
def noncentralChiSquaredPDF (k : ℝ) (l : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (noncentralChiSquaredPDFReal k l x)

/-- The extended density is obtained from its nonnegative real companion. -/
theorem noncentralChiSquaredPDF_eq_ofReal (k : ℝ) (l : ℝ≥0) (x : ℝ) :
    noncentralChiSquaredPDF k l x = ENNReal.ofReal (noncentralChiSquaredPDFReal k l x) := (rfl)

private theorem poisson_mul_chiSquaredPDFReal (k : ℝ) (l : ℝ≥0) (hx : 0 < x) (n : ℕ) :
    (poissonMeasure (l / 2)).real {n} * chiSquaredPDFReal (k + 2 * n) x =
      (exp (-(l : ℝ) / 2) * exp (-x / 2) * x ^ (k / 2 - 1) / 2 ^ (k / 2)) *
        (((l : ℝ) * x / 4) ^ n / (n ! * Gamma (k / 2 + n))) := by
  rw [poissonMeasure_real_singleton, chiSquaredPDFReal_of_nonneg hx.le]
  push_cast
  have he : (k + 2 * (n : ℝ)) / 2 = k / 2 + n := by ring
  have he' : (k + 2 * (n : ℝ)) / 2 - 1 = (k / 2 - 1) + n := by ring
  rw [he', he, rpow_add hx, rpow_add (by norm_num : (0 : ℝ) < 2), rpow_natCast,
    rpow_natCast]
  have hfour : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  simp only [mul_pow, hfour, div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring_nf

/-- The Poisson-weighted real central densities are summable at every positive argument.
This includes degree zero, whose zeroth summand vanishes. -/
theorem summable_poisson_mul_chiSquaredPDFReal (k : ℝ) (l : ℝ≥0) (hx : 0 < x) :
    Summable fun n : ℕ ↦
      (poissonMeasure (l / 2)).real {n} * chiSquaredPDFReal (k + 2 * n) x := by
  simp_rw [poisson_mul_chiSquaredPDFReal k l hx]
  exact (Complex.hasSum_regularizedHGFun_zero_singleton_ofReal_re (k / 2)
    ((l : ℝ) * x / 4)).summable.mul_left _

/-- The defining convergent density series on the positive half-line. -/
theorem noncentralChiSquaredPDFReal_of_pos (hk : 0 ≤ k) (hx : 0 < x) :
    noncentralChiSquaredPDFReal k l x = ∑' n : ℕ,
      (poissonMeasure (l / 2)).real {n} * chiSquaredPDFReal (k + 2 * n) x := by
  simp [noncentralChiSquaredPDFReal, hk, hx]

/-- The chosen real density vanishes at and below zero. -/
@[simp]
theorem noncentralChiSquaredPDFReal_of_nonpos (hx : x ≤ 0) :
    noncentralChiSquaredPDFReal k l x = 0 := by
  simp [noncentralChiSquaredPDFReal, not_lt.mpr hx]

/-- Invalid degrees have zero real density. -/
@[simp]
theorem noncentralChiSquaredPDFReal_of_neg (hk : k < 0) (l : ℝ≥0) (x : ℝ) :
    noncentralChiSquaredPDFReal k l x = 0 := by
  simp [noncentralChiSquaredPDFReal, not_le.mpr hk]

/-- At zero noncentrality the density is the central density on the positive half-line,
with the declared zero values elsewhere. -/
@[simp]
theorem noncentralChiSquaredPDFReal_zero_noncentrality (k x : ℝ) :
    noncentralChiSquaredPDFReal k 0 x =
      if 0 ≤ k ∧ 0 < x then chiSquaredPDFReal k x else 0 := by
  unfold noncentralChiSquaredPDFReal
  split_ifs
  · rw [tsum_eq_single 0]
    · simp [poissonMeasure_real_singleton]
    · intro n hn
      simp [poissonMeasure_real_singleton, hn]
  · rfl

/-- At zero noncentrality the extended density is the central density on the positive
half-line, with the declared zero values elsewhere. -/
@[simp]
theorem noncentralChiSquaredPDF_zero_noncentrality (k x : ℝ) :
    noncentralChiSquaredPDF k 0 x =
      if 0 ≤ k ∧ 0 < x then chiSquaredPDF k x else 0 := by
  rw [noncentralChiSquaredPDF_eq_ofReal, noncentralChiSquaredPDFReal_zero_noncentrality]
  split_ifs <;> simp only [chiSquaredPDF_eq_ofReal, ENNReal.ofReal_zero]

/-- The chosen extended density vanishes at and below zero. -/
@[simp]
theorem noncentralChiSquaredPDF_of_nonpos (hx : x ≤ 0) :
    noncentralChiSquaredPDF k l x = 0 := by
  simp [noncentralChiSquaredPDF_eq_ofReal, noncentralChiSquaredPDFReal_of_nonpos hx]

/-- Invalid degrees have zero extended density. -/
@[simp]
theorem noncentralChiSquaredPDF_of_neg (hk : k < 0) (l : ℝ≥0) (x : ℝ) :
    noncentralChiSquaredPDF k l x = 0 := by
  simp [noncentralChiSquaredPDF_eq_ofReal, noncentralChiSquaredPDFReal_of_neg hk]

/-- The real density is nonnegative for every parameter value. -/
theorem noncentralChiSquaredPDFReal_nonneg (k : ℝ) (l : ℝ≥0) (x : ℝ) :
    0 ≤ noncentralChiSquaredPDFReal k l x := by
  unfold noncentralChiSquaredPDFReal
  split_ifs with h
  · exact tsum_nonneg fun n ↦ mul_nonneg measureReal_nonneg
      (chiSquaredPDFReal_nonneg (by linarith [h.1, n.cast_nonneg (α := ℝ)]) x)
  · rfl

/-- Every non-Dirac valid law has strictly positive continuous density at positive arguments. -/
theorem noncentralChiSquaredPDFReal_pos (hk : 0 ≤ k) (hne : k ≠ 0 ∨ l ≠ 0) (hx : 0 < x) :
    0 < noncentralChiSquaredPDFReal k l x := by
  rw [noncentralChiSquaredPDFReal_of_pos hk hx]
  have hnonneg (n : ℕ) : 0 ≤ (poissonMeasure (l / 2)).real {n} *
      chiSquaredPDFReal (k + 2 * n) x :=
    mul_nonneg measureReal_nonneg (chiSquaredPDFReal_nonneg (by positivity) x)
  have hcentral (n : ℕ) (hd : 0 < k + 2 * n) : 0 < chiSquaredPDFReal (k + 2 * n) x := by
    rw [chiSquaredPDFReal_eq_gammaPDFReal]
    exact gammaPDFReal_pos (by positivity) one_half_pos hx
  have hsum := summable_poisson_mul_chiSquaredPDFReal k l hx
  rcases hne with hk' | hl
  · apply hsum.tsum_pos hnonneg 0
    have hd := hcentral 0 (by simpa using lt_of_le_of_ne hk hk'.symm)
    simpa only [poissonMeasure_real_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, mul_one] using mul_pos (exp_pos (-(↑(l / 2) : ℝ))) hd
  · exact hsum.tsum_pos hnonneg 1
      (mul_pos (poissonMeasure_real_singleton_pos 1 (by positivity)) (hcentral 1 (by positivity)))

/-- Every non-Dirac valid law has strictly positive extended continuous density at
positive arguments. -/
theorem noncentralChiSquaredPDF_pos (hk : 0 ≤ k) (hne : k ≠ 0 ∨ l ≠ 0) (hx : 0 < x) :
    0 < noncentralChiSquaredPDF k l x := by
  rw [noncentralChiSquaredPDF, ENNReal.ofReal_pos]
  exact noncentralChiSquaredPDFReal_pos hk hne hx

/-- The density is jointly measurable in the degree, noncentrality and argument. -/
@[fun_prop]
theorem measurable_uncurry_noncentralChiSquaredPDFReal :
    Measurable fun p : (ℝ × ℝ≥0) × ℝ ↦ noncentralChiSquaredPDFReal p.1.1 p.1.2 p.2 := by
  unfold noncentralChiSquaredPDFReal
  apply Measurable.ite (by measurability) _ measurable_const
  apply Measurable.tsum
  intro n
  simp only [poissonMeasure_real_singleton, chiSquaredPDFReal_eq_gammaPDFReal, gammaPDFReal]
  apply Measurable.mul (by fun_prop)
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- Joint measurability of the extended nonnegative density. -/
@[fun_prop]
theorem measurable_uncurry_noncentralChiSquaredPDF :
    Measurable fun p : (ℝ × ℝ≥0) × ℝ ↦ noncentralChiSquaredPDF p.1.1 p.1.2 p.2 :=
  measurable_uncurry_noncentralChiSquaredPDFReal.ennreal_ofReal

/-- The extended density is measurable as a function of its argument. -/
@[fun_prop]
theorem measurable_noncentralChiSquaredPDF (k : ℝ) (l : ℝ≥0) :
    Measurable (noncentralChiSquaredPDF k l) :=
  measurable_uncurry_noncentralChiSquaredPDF.comp
    (measurable_const.prodMk measurable_id : Measurable fun x : ℝ ↦ ((k, l), x))

/-- On the positive half-line, the extended density is the Poisson-weighted series
of central densities, including the zero-degree case. -/
theorem noncentralChiSquaredPDF_of_pos (hk : 0 ≤ k) (hx : 0 < x) :
    noncentralChiSquaredPDF k l x = ∑' n : ℕ,
      poissonMeasure (l / 2) {n} * chiSquaredPDF (k + 2 * n) x := by
  rw [noncentralChiSquaredPDF, noncentralChiSquaredPDFReal_of_pos hk hx,
    ENNReal.ofReal_tsum_of_nonneg
      (fun n ↦ mul_nonneg measureReal_nonneg (chiSquaredPDFReal_nonneg (by positivity) x))
      (summable_poisson_mul_chiSquaredPDFReal k l hx)]
  congr 1
  funext n
  rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _), chiSquaredPDF_eq_ofReal]

/-- The density series agrees with the chosen density almost everywhere, including the
nonpositive half-line. The value chosen at zero has no effect on the measure. -/
theorem noncentralChiSquaredPDF_eq_tsum_ae (hk : 0 ≤ k) (l : ℝ≥0) :
    noncentralChiSquaredPDF k l =ᵐ[volume] fun x ↦ ∑' n : ℕ,
      poissonMeasure (l / 2) {n} * chiSquaredPDF (k + 2 * n) x := by
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  rcases lt_or_gt_of_ne hx with hx | hx
  · simp [noncentralChiSquaredPDF, noncentralChiSquaredPDFReal_of_nonpos hx.le,
      chiSquaredPDF_of_neg hx]
  · exact noncentralChiSquaredPDF_of_pos hk hx

private theorem withDensity_noncentralChiSquaredPDF (hk : 0 ≤ k) (l : ℝ≥0) :
    volume.withDensity (noncentralChiSquaredPDF k l) = Measure.sum fun n : ℕ ↦
      poissonMeasure (l / 2) {n} • volume.withDensity (chiSquaredPDF (k + 2 * n)) := by
  rw [withDensity_congr_ae (noncentralChiSquaredPDF_eq_tsum_ae hk l)]
  have hfun : (fun x ↦ ∑' n : ℕ,
      poissonMeasure (l / 2) {n} * chiSquaredPDF (k + 2 * n) x) =
      ∑' n : ℕ, poissonMeasure (l / 2) {n} • chiSquaredPDF (k + 2 * n) := by
    ext x
    rw [Pi.tsum_apply (Pi.summable.2 fun _ ↦ ENNReal.summable)]
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hfun, withDensity_tsum (fun n : ℕ ↦
    (measurable_chiSquaredPDF (k + 2 * n)).const_smul _)]
  congr 1
  funext n
  exact withDensity_smul _ (measurable_chiSquaredPDF _)

/-- The noncentral chi-squared law has this density at positive degree. -/
theorem noncentralChiSquaredMeasure_eq_withDensity (hk : 0 < k) (l : ℝ≥0) :
    noncentralChiSquaredMeasure k l = volume.withDensity (noncentralChiSquaredPDF k l) := by
  rw [noncentralChiSquaredMeasure_eq_sum hk.le, withDensity_noncentralChiSquaredPDF hk.le]
  congr 1
  funext n
  rw [chiSquaredMeasure_eq_withDensity (by positivity)]

/-- At degree zero, the atom has mass `exp (-l / 2)` and the density describes the
remaining continuous component, including the pure-atom case `l = 0`. -/
theorem noncentralChiSquaredMeasure_zero_degree_eq_atom_add_withDensity (l : ℝ≥0) :
    noncentralChiSquaredMeasure 0 l =
      ENNReal.ofReal (exp (-(l : ℝ) / 2)) • Measure.dirac 0 +
        volume.withDensity (noncentralChiSquaredPDF 0 l) := by
  rw [noncentralChiSquaredMeasure_zero_degree, withDensity_noncentralChiSquaredPDF (by norm_num)]
  congr 1
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, mul_zero, zero_add, chiSquaredPDF_zero_degree, withDensity_zero,
    Measure.smul_apply, smul_eq_mul]
  simp only [Measure.coe_zero, Pi.zero_apply, mul_zero, zero_add]
  congr 1
  funext n
  rw [chiSquaredMeasure_eq_withDensity (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one]

/-- At positive noncentrality and positive argument the continuous density has its
classical modified-Bessel form. The formula also describes the continuous part at degree zero. -/
theorem noncentralChiSquaredPDFReal_eq_besselI (hk : 0 ≤ k) (hl : 0 < l) (hx : 0 < x) :
    noncentralChiSquaredPDFReal k l x =
      (1 / 2 : ℝ) * exp (-(x + l) / 2) * (x / l) ^ (k / 4 - 1 / 2) *
        besselI (k / 2 - 1) (sqrt ((l : ℝ) * x)) := by
  have hl' : 0 < (l : ℝ) := hl
  have harg : (sqrt ((l : ℝ) * x) / 2) ^ 2 = (l : ℝ) * x / 4 := by
    rw [div_pow, sq_sqrt (by positivity)]
    norm_num
  have hpow : (x / (l : ℝ)) ^ (k / 4 - 1 / 2) *
      (sqrt ((l : ℝ) * x) / 2) ^ (k / 2 - 1) = x ^ (k / 2 - 1) / 2 ^ (k / 2 - 1) := by
    have he : k / 4 - 1 / 2 = (1 / 2 : ℝ) * (k / 2 - 1) := by ring
    have hsqrt : sqrt (x / (l : ℝ)) * sqrt ((l : ℝ) * x) = x := by
      rw [← sqrt_mul (by positivity)]
      have heq : x / (l : ℝ) * ((l : ℝ) * x) = x ^ 2 := by field_simp
      rw [heq, sqrt_sq hx.le]
    rw [he, rpow_mul (by positivity), ← sqrt_eq_rpow,
      ← mul_rpow (by positivity) (by positivity), ← mul_div_assoc, hsqrt,
      div_rpow hx.le (by norm_num)]
  rw [noncentralChiSquaredPDFReal_of_pos hk hx]
  simp_rw [poisson_mul_chiSquaredPDFReal k l hx]
  rw [tsum_mul_left,
    (Complex.hasSum_regularizedHGFun_zero_singleton_ofReal_re (k / 2)
      ((l : ℝ) * x / 4)).tsum_eq, besselI_eq_rpow_mul, harg]
  have hshape : k / 2 - 1 + 1 = k / 2 := by ring
  rw [hshape]
  have he : exp (-(l : ℝ) / 2) * exp (-x / 2) = exp (-(x + l) / 2) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he]
  calc
    _ = (1 / 2 : ℝ) * exp (-(x + l) / 2) *
        (x ^ (k / 2 - 1) / 2 ^ (k / 2 - 1)) *
        (Complex.regularizedHGFun 0 {((k / 2 : ℝ) : ℂ)}
          (((l : ℝ) * x / 4 : ℝ) : ℂ)).re := by
      rw [rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    _ = _ := by rw [← hpow]; ring

/-- The continuous part has mass one at positive degree. -/
theorem lintegral_noncentralChiSquaredPDF_eq_one (hk : 0 < k) (l : ℝ≥0) :
    ∫⁻ x, noncentralChiSquaredPDF k l x = 1 := by
  let := isProbabilityMeasure_noncentralChiSquaredMeasure hk.le l
  have h : noncentralChiSquaredMeasure k l univ = 1 := measure_univ
  rwa [noncentralChiSquaredMeasure_eq_withDensity hk, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h

/-- At degree zero, the continuous part has mass `1 - exp (-l / 2)`. -/
theorem lintegral_noncentralChiSquaredPDF_zero_degree (l : ℝ≥0) :
    ∫⁻ x, noncentralChiSquaredPDF 0 l x = 1 - ENNReal.ofReal (exp (-(l : ℝ) / 2)) := by
  let := isProbabilityMeasure_noncentralChiSquaredMeasure (k := 0) (by norm_num) l
  have h : noncentralChiSquaredMeasure 0 l univ = 1 := measure_univ
  rw [noncentralChiSquaredMeasure_zero_degree_eq_atom_add_withDensity,
    Measure.add_apply, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h
  simp only [smul_eq_mul, measure_univ, mul_one] at h
  exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top (by simpa only [add_comm] using h)

/-- The real density is measurable as a function of its argument. -/
@[fun_prop]
theorem measurable_noncentralChiSquaredPDFReal (k : ℝ) (l : ℝ≥0) :
    Measurable (noncentralChiSquaredPDFReal k l) :=
  measurable_uncurry_noncentralChiSquaredPDFReal.comp
    (measurable_const.prodMk measurable_id : Measurable fun x : ℝ ↦ ((k, l), x))

/-- The continuous density is integrable, including the mixed boundary and invalid degrees. -/
theorem integrable_noncentralChiSquaredPDFReal (k : ℝ) (l : ℝ≥0) :
    Integrable (noncentralChiSquaredPDFReal k l) := by
  refine ⟨(measurable_noncentralChiSquaredPDFReal k l).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (noncentralChiSquaredPDFReal_nonneg k l))).2 ?_⟩
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [noncentralChiSquaredPDFReal_of_neg hk]
  · simp_rw [← noncentralChiSquaredPDF_eq_ofReal]
    rw [lintegral_noncentralChiSquaredPDF_zero_degree]
    exact lt_of_le_of_lt tsub_le_self (by norm_num : (1 : ℝ≥0∞) < ∞)
  · simp_rw [← noncentralChiSquaredPDF_eq_ofReal]
    exact (lintegral_noncentralChiSquaredPDF_eq_one hk l).trans_lt (by norm_num)

/-- The real density integrates to one at positive degree. -/
theorem integral_noncentralChiSquaredPDFReal_eq_one (hk : 0 < k) (l : ℝ≥0) :
    ∫ x, noncentralChiSquaredPDFReal k l x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (noncentralChiSquaredPDFReal_nonneg k l))
      (measurable_noncentralChiSquaredPDFReal k l).aestronglyMeasurable]
  simp_rw [← noncentralChiSquaredPDF_eq_ofReal]
  rw [lintegral_noncentralChiSquaredPDF_eq_one hk l, ENNReal.toReal_one]

/-- At degree zero, the real continuous density integrates to `1 - exp (-l / 2)`. -/
theorem integral_noncentralChiSquaredPDFReal_zero_degree (l : ℝ≥0) :
    ∫ x, noncentralChiSquaredPDFReal 0 l x = 1 - exp (-(l : ℝ) / 2) := by
  rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (noncentralChiSquaredPDFReal_nonneg 0 l))
      (measurable_noncentralChiSquaredPDFReal 0 l).aestronglyMeasurable]
  simp_rw [← noncentralChiSquaredPDF_eq_ofReal]
  rw [lintegral_noncentralChiSquaredPDF_zero_degree, ENNReal.toReal_sub_of_le
    (ENNReal.ofReal_le_one.mpr (exp_le_one_iff.mpr (by linarith [l.coe_nonneg])))
      ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_ofReal (exp_nonneg _)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- Variables with a positive-degree noncentral chi-squared law have a density. -/
theorem hasPDF_of_hasLaw_noncentralChiSquaredMeasure (hk : 0 < k)
    (hX : HasLaw X (noncentralChiSquaredMeasure k l) P) : HasPDF X P volume := by
  apply hasPDF_of_hasLaw_withDensity (measurable_noncentralChiSquaredPDF k l).aemeasurable
  rwa [← noncentralChiSquaredMeasure_eq_withDensity hk]

/-- The canonical random-variable density agrees almost everywhere with the named density. -/
theorem pdf_eq_noncentralChiSquaredPDF_of_hasLaw_noncentralChiSquaredMeasure (hk : 0 < k)
    (hX : HasLaw X (noncentralChiSquaredMeasure k l) P) :
    pdf X P volume =ᵐ[volume] noncentralChiSquaredPDF k l := by
  apply pdf_eq_of_hasLaw_withDensity (measurable_noncentralChiSquaredPDF k l).aemeasurable
  rwa [← noncentralChiSquaredMeasure_eq_withDensity hk]

/-- The Radon–Nikodym derivative is the density of the continuous component. In particular,
the atom at degree zero contributes zero to this derivative. -/
theorem rnDeriv_noncentralChiSquaredMeasure (k : ℝ) (l : ℝ≥0) :
    (noncentralChiSquaredMeasure k l).rnDeriv volume =ᵐ[volume] noncentralChiSquaredPDF k l := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have hzero : noncentralChiSquaredPDF k l = 0 :=
      funext (noncentralChiSquaredPDF_of_neg hk l)
    rw [noncentralChiSquaredMeasure_of_neg hk, hzero]
    simp
  · let := isProbabilityMeasure_noncentralChiSquaredMeasure (k := 0) (by norm_num) l
    have hc : volume.withDensity (noncentralChiSquaredPDF 0 l) ≤
        noncentralChiSquaredMeasure 0 l := by
      rw [noncentralChiSquaredMeasure_zero_degree_eq_atom_add_withDensity]
      exact Measure.le_add_left le_rfl
    have ha : ENNReal.ofReal (exp (-(l : ℝ) / 2)) • Measure.dirac 0 ≤
        noncentralChiSquaredMeasure 0 l := by
      rw [noncentralChiSquaredMeasure_zero_degree_eq_atom_add_withDensity]
      exact Measure.le_add_right le_rfl
    have := isFiniteMeasure_of_le _ hc
    have := isFiniteMeasure_of_le _ ha
    rw [noncentralChiSquaredMeasure_zero_degree_eq_atom_add_withDensity, add_comm]
    exact (Measure.rnDeriv_add_of_mutuallySingular _ _ _
      ((mutuallySingular_dirac 0 volume).smul _)).trans
        (Measure.rnDeriv_withDensity volume (measurable_noncentralChiSquaredPDF 0 l))
  · rw [noncentralChiSquaredMeasure_eq_withDensity hk]
    exact Measure.rnDeriv_withDensity volume (measurable_noncentralChiSquaredPDF k l)

end TauCeti.Probability
