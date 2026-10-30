/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NoncentralBeta.Basic
import TauCeti.Probability.Distributions.Beta.Measurability
import TauCeti.Probability.Distributions.Beta.PDF

/-!
# Densities of noncentral Beta laws

The Poisson-weighted Beta densities `betaPDFReal (a + j) b` form a convergent series at every
point. For positive first shape `a` this series is the density of `noncentralBetaMeasure a b l`.
At `a = 0` the zero-count component is the point mass at zero; its Beta density vanishes, so the
series describes only the continuous component of mass `1 - exp (-l / 2)`, and the atom is kept
separate.

Convergence is a ratio test: raising the Poisson count by one multiplies a term by
`(l / 2) / (j + 1) * x * (a + j + b) / (a + j)`, which tends to zero.
Densities vanish off the open unit interval and for invalid shapes.

## Main definitions

* `TauCeti.Probability.noncentralBetaPDFReal` and `TauCeti.Probability.noncentralBetaPDF` — the
  real and extended densities of the continuous component.

## Main results

* `TauCeti.Probability.summable_poisson_mul_betaPDFReal` — convergence of the density series.
* `TauCeti.Probability.noncentralBetaPDFReal_pos` — positivity on the open unit interval away from
  the Dirac law.
* `TauCeti.Probability.noncentralBetaMeasure_eq_withDensity` — the density at positive first
  shape.
* `TauCeti.Probability.noncentralBetaMeasure_zero_shape_eq_atom_add_withDensity` — the atom and
  the continuous component at first shape zero.
* `TauCeti.Probability.rnDeriv_noncentralBetaMeasure` and
  `TauCeti.Probability.pdf_eq_noncentralBetaPDF_of_hasLaw_noncentralBetaMeasure` — the
  Radon–Nikodym derivative and the density of a random variable, for all parameters.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
* The formal density architecture is adapted from
  `TauCeti.Probability.Distributions.NoncentralChiSquared.PDF`, notably
  `noncentralChiSquaredPDFReal_zero_noncentrality`,
  `noncentralChiSquaredMeasure_zero_degree_eq_atom_add_withDensity`, and
  `rnDeriv_noncentralChiSquaredMeasure`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Nat

namespace TauCeti.Probability

variable {a b x : ℝ} {l : ℝ≥0}

/-- The real density of the continuous component of a noncentral Beta law: the Poisson mixture,
with weights of rate `l / 2`, of the Beta densities `betaPDFReal (a + j) b`. At first shape zero
the atom is excluded; for invalid shapes the density is zero. -/
def noncentralBetaPDFReal (a b : ℝ) (l : ℝ≥0) (x : ℝ) : ℝ :=
  if 0 ≤ a ∧ 0 < b then ∑' j : ℕ, (poissonMeasure (l / 2)).real {j} * betaPDFReal (a + j) b x
  else 0

/-- The extended nonnegative density of the continuous component of a noncentral Beta law. It
excludes the atom at first shape zero. -/
def noncentralBetaPDF (a b : ℝ) (l : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (noncentralBetaPDFReal a b l x)

/-- The extended density is obtained from its nonnegative real companion. -/
theorem noncentralBetaPDF_eq_ofReal (a b : ℝ) (l : ℝ≥0) (x : ℝ) :
    noncentralBetaPDF a b l x = ENNReal.ofReal (noncentralBetaPDFReal a b l x) := (rfl)

/-- The defining density series for valid shapes. -/
theorem noncentralBetaPDFReal_eq_tsum (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) (x : ℝ) :
    noncentralBetaPDFReal a b l x =
      ∑' j : ℕ, (poissonMeasure (l / 2)).real {j} * betaPDFReal (a + j) b x := by
  rw [noncentralBetaPDFReal, ite_eq_left ⟨ha, hb⟩]

/-- Invalid shapes have zero real density. -/
@[simp]
theorem noncentralBetaPDFReal_of_not (h : ¬ (0 ≤ a ∧ 0 < b)) (l : ℝ≥0) (x : ℝ) :
    noncentralBetaPDFReal a b l x = 0 := by
  rw [noncentralBetaPDFReal, ite_eq_right h]

/-- Raising the Poisson count by one multiplies a term of the density series by
`(l / 2) / (j + 1) * x * (a + j + b) / (a + j)`. -/
private theorem poisson_mul_betaPDFReal_succ (l : ℝ≥0) (j : ℕ) (hc : a + j ≠ 0)
    (hcb : a + j + b ≠ 0) (x : ℝ) :
    (poissonMeasure (l / 2)).real {j + 1} * betaPDFReal (a + ↑(j + 1)) b x =
      ((l : ℝ) / 2 / (j + 1) * x * ((a + j + b) / (a + j))) *
        ((poissonMeasure (l / 2)).real {j} * betaPDFReal (a + j) b x) := by
  rw [Nat.cast_succ, ← add_assoc, betaPDFReal_add_one_left hc hcb, poissonMeasure_real_singleton,
    poissonMeasure_real_singleton, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- The Poisson-weighted Beta densities are summable at every point and for every first shape. -/
theorem summable_poisson_mul_betaPDFReal (a : ℝ) (hb : 0 < b) (l : ℝ≥0) (x : ℝ) :
    Summable fun j : ℕ ↦ (poissonMeasure (l / 2)).real {j} * betaPDFReal (a + j) b x := by
  by_cases hx : 0 < x ∧ x < 1
  swap
  · simp [betaPDFReal, hx]
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 - a) ((l : ℝ) * (1 + b)))
  filter_upwards [eventually_ge_atTop N] with j hj
  have hj' : max (1 - a) ((l : ℝ) * (1 + b)) < j := hN.trans_le (Nat.cast_le.mpr hj)
  have hc : 1 ≤ a + j := by linarith [le_max_left (1 - a) ((l : ℝ) * (1 + b))]
  have hl : (l : ℝ) * (1 + b) < j := (le_max_right _ _).trans_lt hj'
  have hratio : (a + j + b) / (a + j) ≤ 1 + b := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hc0 : 0 < a + j := by linarith
  have h0 : 0 ≤ (l : ℝ) / 2 / (j + 1) := by positivity
  have hr0 : 0 ≤ (a + j + b) / (a + j) := div_nonneg (by linarith) hc0.le
  have hfactor : (l : ℝ) / 2 / (j + 1) * x * ((a + j + b) / (a + j)) ≤ 1 / 2 := by
    calc (l : ℝ) / 2 / (j + 1) * x * ((a + j + b) / (a + j))
        ≤ (l : ℝ) / 2 / (j + 1) * 1 * (1 + b) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hx.2.le h0) hratio hr0 (by positivity)
      _ ≤ 1 / 2 := by
          rw [mul_one, div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
          nlinarith [l.coe_nonneg]
  rw [poisson_mul_betaPDFReal_succ l j hc0.ne' (by linarith : 0 < a + j + b).ne', norm_mul,
    Real.norm_of_nonneg (mul_nonneg (mul_nonneg h0 hx.1.le) hr0)]
  exact mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)

/-- The terms of the density series are nonnegative, including the vanishing zero-count term at
first shape zero. -/
private theorem poisson_mul_betaPDFReal_nonneg (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) (j : ℕ)
    (x : ℝ) : 0 ≤ (poissonMeasure (l / 2)).real {j} * betaPDFReal (a + j) b x := by
  refine mul_nonneg measureReal_nonneg ?_
  rcases (add_nonneg ha j.cast_nonneg).eq_or_lt' with h | h
  · rw [h, betaPDFReal_zero_left]
  · exact betaPDFReal_nonneg h hb x

/-- The real density is nonnegative for every parameter value. -/
theorem noncentralBetaPDFReal_nonneg (a b : ℝ) (l : ℝ≥0) (x : ℝ) :
    0 ≤ noncentralBetaPDFReal a b l x := by
  by_cases h : 0 ≤ a ∧ 0 < b
  · rw [noncentralBetaPDFReal_eq_tsum h.1 h.2]
    exact tsum_nonneg (poisson_mul_betaPDFReal_nonneg h.1 h.2 l · x)
  · rw [noncentralBetaPDFReal_of_not h]

/-- The real density vanishes at and below zero. -/
@[simp]
theorem noncentralBetaPDFReal_of_nonpos (hx : x ≤ 0) : noncentralBetaPDFReal a b l x = 0 := by
  simp [noncentralBetaPDFReal, betaPDFReal, not_lt.mpr hx]

/-- The real density vanishes at and above one. -/
@[simp]
theorem noncentralBetaPDFReal_of_one_le (hx : 1 ≤ x) : noncentralBetaPDFReal a b l x = 0 := by
  simp [noncentralBetaPDFReal, betaPDFReal, not_lt.mpr hx]

/-- At zero noncentrality the density is the Beta density, which vanishes at first shape zero;
invalid shapes keep their zero density. -/
@[simp]
theorem noncentralBetaPDFReal_zero_noncentrality (a b x : ℝ) :
    noncentralBetaPDFReal a b 0 x = if 0 ≤ a ∧ 0 < b then betaPDFReal a b x else 0 := by
  unfold noncentralBetaPDFReal
  split_ifs
  · rw [tsum_eq_single 0]
    · simp [poissonMeasure_real_singleton]
    · intro j hj
      simp [poissonMeasure_real_singleton, hj]
  · rfl

/-- Invalid shapes have zero extended density. -/
@[simp]
theorem noncentralBetaPDF_of_not (h : ¬ (0 ≤ a ∧ 0 < b)) (l : ℝ≥0) (x : ℝ) :
    noncentralBetaPDF a b l x = 0 := by
  simp [noncentralBetaPDF_eq_ofReal, noncentralBetaPDFReal_of_not h]

/-- The extended density vanishes at and below zero. -/
@[simp]
theorem noncentralBetaPDF_of_nonpos (hx : x ≤ 0) : noncentralBetaPDF a b l x = 0 := by
  simp [noncentralBetaPDF_eq_ofReal, noncentralBetaPDFReal_of_nonpos hx]

/-- The extended density vanishes at and above one. -/
@[simp]
theorem noncentralBetaPDF_of_one_le (hx : 1 ≤ x) : noncentralBetaPDF a b l x = 0 := by
  simp [noncentralBetaPDF_eq_ofReal, noncentralBetaPDFReal_of_one_le hx]

/-- At zero noncentrality the extended density is the Beta density for valid shapes and zero for
invalid shapes. -/
@[simp]
theorem noncentralBetaPDF_zero_noncentrality (a b x : ℝ) :
    noncentralBetaPDF a b 0 x = if 0 ≤ a ∧ 0 < b then betaPDF a b x else 0 := by
  rw [noncentralBetaPDF_eq_ofReal, noncentralBetaPDFReal_zero_noncentrality]
  split_ifs <;> simp only [betaPDF, ENNReal.ofReal_zero]

/-- Away from the Dirac law at `a = l = 0`, the density is positive on the open unit interval. -/
theorem noncentralBetaPDFReal_pos (ha : 0 ≤ a) (hb : 0 < b) (hne : a ≠ 0 ∨ l ≠ 0) (hx : 0 < x)
    (hx₁ : x < 1) : 0 < noncentralBetaPDFReal a b l x := by
  rw [noncentralBetaPDFReal_eq_tsum ha hb]
  have hsum := summable_poisson_mul_betaPDFReal a hb l x
  have hnonneg := (poisson_mul_betaPDFReal_nonneg ha hb l · x)
  rcases hne with ha' | hl
  · refine hsum.tsum_pos hnonneg 0 (mul_pos ?_ (betaPDFReal_pos hx hx₁ ?_ hb))
    · simp [poissonMeasure_real_singleton, exp_pos]
    · simpa using lt_of_le_of_ne ha (Ne.symm ha')
  · exact hsum.tsum_pos hnonneg 1 (mul_pos (poissonMeasure_real_singleton_pos 1 (by positivity))
      (betaPDFReal_pos hx hx₁ (by positivity) hb))

/-- Away from the Dirac law at `a = l = 0`, the extended density is positive on the open unit
interval. -/
theorem noncentralBetaPDF_pos (ha : 0 ≤ a) (hb : 0 < b) (hne : a ≠ 0 ∨ l ≠ 0) (hx : 0 < x)
    (hx₁ : x < 1) : 0 < noncentralBetaPDF a b l x := by
  rw [noncentralBetaPDF, ENNReal.ofReal_pos]
  exact noncentralBetaPDFReal_pos ha hb hne hx hx₁

/-! ### Measurability -/

/-- The density is jointly measurable in the two shapes, the noncentrality and the argument. -/
@[fun_prop]
theorem measurable_uncurry_noncentralBetaPDFReal :
    Measurable fun p : (ℝ × ℝ × ℝ≥0) × ℝ ↦
      noncentralBetaPDFReal p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  unfold noncentralBetaPDFReal
  refine Measurable.ite ?_ (Measurable.tsum fun j ↦ ?_) measurable_const
  · exact (measurableSet_le measurable_const measurable_fst.fst).inter
      (measurableSet_lt measurable_const measurable_fst.snd.fst)
  · simp only [poissonMeasure_real_singleton, betaPDFReal]
    refine Measurable.mul (by fun_prop) (Measurable.ite ?_ (by fun_prop) measurable_const)
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)

/-- Joint measurability of the extended density. -/
@[fun_prop]
theorem measurable_uncurry_noncentralBetaPDF :
    Measurable fun p : (ℝ × ℝ × ℝ≥0) × ℝ ↦ noncentralBetaPDF p.1.1 p.1.2.1 p.1.2.2 p.2 :=
  measurable_uncurry_noncentralBetaPDFReal.ennreal_ofReal

/-- The real density is measurable as a function of its argument. -/
@[fun_prop]
theorem measurable_noncentralBetaPDFReal (a b : ℝ) (l : ℝ≥0) :
    Measurable (noncentralBetaPDFReal a b l) :=
  measurable_uncurry_noncentralBetaPDFReal.comp
    (measurable_const.prodMk measurable_id : Measurable fun x : ℝ ↦ ((a, b, l), x))

/-- The extended density is measurable as a function of its argument. -/
@[fun_prop]
theorem measurable_noncentralBetaPDF (a b : ℝ) (l : ℝ≥0) :
    Measurable (noncentralBetaPDF a b l) :=
  (measurable_noncentralBetaPDFReal a b l).ennreal_ofReal

/-! ### The density of the law -/

/-- For valid shapes the extended density is the Poisson-weighted series of extended Beta
densities, at every point. -/
theorem noncentralBetaPDF_eq_tsum (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) (x : ℝ) :
    noncentralBetaPDF a b l x = ∑' j : ℕ, poissonMeasure (l / 2) {j} * betaPDF (a + j) b x := by
  rw [noncentralBetaPDF, noncentralBetaPDFReal_eq_tsum ha hb,
    ENNReal.ofReal_tsum_of_nonneg (poisson_mul_betaPDFReal_nonneg ha hb l · x)
      (summable_poisson_mul_betaPDFReal a hb l x)]
  refine tsum_congr fun j ↦ ?_
  rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _), betaPDF]

private theorem withDensity_noncentralBetaPDF (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    volume.withDensity (noncentralBetaPDF a b l) =
      Measure.sum fun j : ℕ ↦ poissonMeasure (l / 2) {j} • betaMeasure (a + j) b := by
  have hfun : noncentralBetaPDF a b l =
      ∑' j : ℕ, poissonMeasure (l / 2) {j} • betaPDF (a + j) b := by
    ext x
    rw [noncentralBetaPDF_eq_tsum ha hb, Pi.tsum_apply (Pi.summable.2 fun _ ↦ ENNReal.summable)]
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hfun, withDensity_tsum fun j ↦ (measurable_betaPDF _ _).const_smul _]
  refine congrArg Measure.sum (funext fun j ↦ ?_)
  rw [withDensity_smul _ (measurable_betaPDF _ _), betaMeasure]

/-- At positive first shape the noncentral Beta law has the density `noncentralBetaPDF`. -/
theorem noncentralBetaMeasure_eq_withDensity (ha : 0 < a) (hb : 0 < b) (l : ℝ≥0) :
    noncentralBetaMeasure a b l = volume.withDensity (noncentralBetaPDF a b l) := by
  rw [noncentralBetaMeasure_eq_sum ha.le hb, withDensity_noncentralBetaPDF ha.le hb]
  refine congrArg Measure.sum (funext fun j ↦ ?_)
  rw [noncentralBetaComponent_of_pos (by positivity)]

/-- At first shape zero the law is the atom of mass `exp (-l / 2)` at zero plus the continuous
component with density `noncentralBetaPDF 0 b l`; this includes the pure atom at `l = 0`. -/
theorem noncentralBetaMeasure_zero_shape_eq_atom_add_withDensity (hb : 0 < b) (l : ℝ≥0) :
    noncentralBetaMeasure 0 b l =
      ENNReal.ofReal (exp (-(l : ℝ) / 2)) • Measure.dirac 0 +
        volume.withDensity (noncentralBetaPDF 0 b l) := by
  rw [noncentralBetaMeasure_zero_shape hb, withDensity_noncentralBetaPDF le_rfl hb]
  congr 1
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
  simp

/-- The continuous part has mass one at positive first shape. -/
theorem lintegral_noncentralBetaPDF_eq_one (ha : 0 < a) (hb : 0 < b) (l : ℝ≥0) :
    ∫⁻ x, noncentralBetaPDF a b l x = 1 := by
  have := isProbabilityMeasure_noncentralBetaMeasure ha.le hb l
  have h : noncentralBetaMeasure a b l univ = 1 := measure_univ
  rwa [noncentralBetaMeasure_eq_withDensity ha hb, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h

/-- At first shape zero the continuous part has mass `1 - exp (-l / 2)`. -/
theorem lintegral_noncentralBetaPDF_zero_shape (hb : 0 < b) (l : ℝ≥0) :
    ∫⁻ x, noncentralBetaPDF 0 b l x = 1 - ENNReal.ofReal (exp (-(l : ℝ) / 2)) := by
  have := isProbabilityMeasure_noncentralBetaMeasure le_rfl hb l
  have h : noncentralBetaMeasure 0 b l univ = 1 := measure_univ
  rw [noncentralBetaMeasure_zero_shape_eq_atom_add_withDensity hb, Measure.add_apply,
    Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  simp only [smul_eq_mul, measure_univ, mul_one] at h
  exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top (by rwa [add_comm])

/-- The extended density integrates to at most one for every parameter value. -/
private theorem lintegral_noncentralBetaPDF_lt_top (a b : ℝ) (l : ℝ≥0) :
    ∫⁻ x, noncentralBetaPDF a b l x < ∞ := by
  by_cases h : 0 ≤ a ∧ 0 < b
  · rcases h.1.eq_or_lt' with rfl | ha
    · rw [lintegral_noncentralBetaPDF_zero_shape h.2]
      exact tsub_le_self.trans_lt ENNReal.one_lt_top
    · rw [lintegral_noncentralBetaPDF_eq_one ha h.2]
      exact ENNReal.one_lt_top
  · simp [noncentralBetaPDF, noncentralBetaPDFReal_of_not h]

/-- The real density is integrable for every parameter value, including first shape zero and
invalid shapes. -/
theorem integrable_noncentralBetaPDFReal (a b : ℝ) (l : ℝ≥0) :
    Integrable (noncentralBetaPDFReal a b l) :=
  ⟨(measurable_noncentralBetaPDFReal a b l).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (noncentralBetaPDFReal_nonneg a b l))).2
      (lintegral_noncentralBetaPDF_lt_top a b l)⟩

/-- The real density integrates to one at positive first shape. -/
theorem integral_noncentralBetaPDFReal_eq_one (ha : 0 < a) (hb : 0 < b) (l : ℝ≥0) :
    ∫ x, noncentralBetaPDFReal a b l x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (noncentralBetaPDFReal_nonneg a b l))
      (measurable_noncentralBetaPDFReal a b l).aestronglyMeasurable]
  simp_rw [← noncentralBetaPDF_eq_ofReal]
  rw [lintegral_noncentralBetaPDF_eq_one ha hb l, ENNReal.toReal_one]

/-- At first shape zero the real density integrates to `1 - exp (-l / 2)`. -/
theorem integral_noncentralBetaPDFReal_zero_shape (hb : 0 < b) (l : ℝ≥0) :
    ∫ x, noncentralBetaPDFReal 0 b l x = 1 - exp (-(l : ℝ) / 2) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (noncentralBetaPDFReal_nonneg 0 b l))
      (measurable_noncentralBetaPDFReal 0 b l).aestronglyMeasurable]
  simp_rw [← noncentralBetaPDF_eq_ofReal]
  rw [lintegral_noncentralBetaPDF_zero_shape hb, ENNReal.toReal_sub_of_le
      (ENNReal.ofReal_le_one.mpr (exp_le_one_iff.mpr (by linarith [l.coe_nonneg])))
      ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_ofReal (exp_nonneg _)]

/-- The Radon–Nikodym derivative with respect to Lebesgue measure is the density of the
continuous component, for every parameter value. At first shape zero the atom contributes
nothing to it. -/
theorem rnDeriv_noncentralBetaMeasure (a b : ℝ) (l : ℝ≥0) :
    (noncentralBetaMeasure a b l).rnDeriv volume =ᵐ[volume] noncentralBetaPDF a b l := by
  by_cases h : 0 ≤ a ∧ 0 < b
  · rcases h.1.eq_or_lt' with rfl | ha
    · let := isProbabilityMeasure_noncentralBetaMeasure le_rfl h.2 l
      have hc : volume.withDensity (noncentralBetaPDF 0 b l) ≤ noncentralBetaMeasure 0 b l := by
        rw [noncentralBetaMeasure_zero_shape_eq_atom_add_withDensity h.2]
        exact Measure.le_add_left le_rfl
      have hd : ENNReal.ofReal (exp (-(l : ℝ) / 2)) • Measure.dirac 0 ≤
          noncentralBetaMeasure 0 b l := by
        rw [noncentralBetaMeasure_zero_shape_eq_atom_add_withDensity h.2]
        exact Measure.le_add_right le_rfl
      have := isFiniteMeasure_of_le _ hc
      have := isFiniteMeasure_of_le _ hd
      rw [noncentralBetaMeasure_zero_shape_eq_atom_add_withDensity h.2, add_comm]
      exact (Measure.rnDeriv_add_of_mutuallySingular _ _ _
        ((mutuallySingular_dirac 0 volume).smul _)).trans
          (Measure.rnDeriv_withDensity volume (measurable_noncentralBetaPDF 0 b l))
    · rw [noncentralBetaMeasure_eq_withDensity ha h.2]
      exact Measure.rnDeriv_withDensity volume (measurable_noncentralBetaPDF a b l)
  · have hzero : noncentralBetaPDF a b l = 0 := by
      ext x
      simp [noncentralBetaPDF, noncentralBetaPDFReal_of_not h]
    rw [noncentralBetaMeasure_of_not h, hzero]
    simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- The density of a variable with a noncentral Beta law agrees almost everywhere with
`noncentralBetaPDF`, for every parameter value. At first shape zero this is the density of the
continuous component only. -/
theorem pdf_eq_noncentralBetaPDF_of_hasLaw_noncentralBetaMeasure
    (hX : HasLaw X (noncentralBetaMeasure a b l) P) :
    pdf X P volume =ᵐ[volume] noncentralBetaPDF a b l := by
  rw [pdf_def, hX.map_eq]
  exact rnDeriv_noncentralBetaMeasure a b l

end TauCeti.Probability
