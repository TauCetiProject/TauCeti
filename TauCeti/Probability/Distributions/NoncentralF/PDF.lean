/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralF.Basic
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.FisherSnedecor.Measurability
import TauCeti.Analysis.SpecialFunctions.Beta
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Densities of noncentral F laws

The noncentral F density is a convergent Poisson series of scaled central F densities.
The scale in each summand is essential: the numerator of the defining ratio is divided by
the original numerator degree, rather than the degree of that central component.

The real and extended nonnegative densities vanish at nonpositive arguments and at invalid
degrees. Their weighted Lebesgue measure is the ratio law, giving normalization and the
Radon–Nikodym and random-variable density identities.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Nat Topology

namespace TauCeti.Probability

variable {m n x : ℝ} {l : ℝ≥0}

/-- The noncentral F density as a Poisson series of scaled central F densities.
Invalid degrees give zero. -/
def noncentralFPDFReal (m n : ℝ) (l : ℝ≥0) (x : ℝ) : ℝ :=
  if 0 < m ∧ 0 < n then
    ∑' j : ℕ, (poissonMeasure (l / 2)).real {j} * (m / (m + 2 * j)) *
      fisherSnedecorPDFReal (m + 2 * j) n (m * x / (m + 2 * j))
  else 0

/-- The extended nonnegative density of the noncentral F law. -/
def noncentralFPDF (m n : ℝ) (l : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (noncentralFPDFReal m n l x)

/-- The extended density is the nonnegative coercion of the real density. -/
theorem noncentralFPDF_eq_ofReal (m n : ℝ) (l : ℝ≥0) (x : ℝ) :
    noncentralFPDF m n l x = ENNReal.ofReal (noncentralFPDFReal m n l x) := (rfl)

private theorem scaled_fisherSnedecorPDFReal (hm : 0 < m) (hn : 0 < n) (hx : 0 < x)
    (j : ℕ) :
    (m / (m + 2 * j)) *
        fisherSnedecorPDFReal (m + 2 * j) n (m * x / (m + 2 * j)) =
      ((m / n) * (m * x / n) ^ (m / 2 - 1) *
        (1 + m * x / n) ^ (-((m + n) / 2))) *
        ((m * x / n / (1 + m * x / n)) ^ j / beta (m / 2 + j) (n / 2)) := by
  have hd : 0 < m + 2 * j := by positivity
  have hy : 0 < m * x / n := by positivity
  have hz : 0 < 1 + m * x / n := by positivity
  rw [fisherSnedecorPDFReal_eq_scaled_beta hd hn (by positivity)]
  have harg : (m + 2 * j) * (m * x / (m + 2 * j)) / n = m * x / n := by
    field_simp
  have ha : (m + 2 * (j : ℝ)) / 2 = m / 2 + j := by ring
  have he : -((m + 2 * (j : ℝ) + n) / 2) = -((m + n) / 2) - j := by ring
  rw [harg, ha, he, show m / 2 + (j : ℝ) - 1 = (m / 2 - 1) + j by ring,
    rpow_add hy, rpow_sub hz, rpow_natCast, rpow_natCast]
  simp only [div_pow]
  field_simp [hd.ne', hn.ne', hz.ne', (beta_pos (by positivity : 0 < m / 2 + j)
    (by positivity : 0 < n / 2)).ne']

private theorem poisson_mul_scaled_fisherSnedecorPDFReal (hm : 0 < m) (hn : 0 < n)
    (l : ℝ≥0) (hx : 0 < x) (j : ℕ) :
    (poissonMeasure (l / 2)).real {j} * (m / (m + 2 * j)) *
        fisherSnedecorPDFReal (m + 2 * j) n (m * x / (m + 2 * j)) =
      (exp (-(l : ℝ) / 2) * ((m / n) * (m * x / n) ^ (m / 2 - 1) *
        (1 + m * x / n) ^ (-((m + n) / 2)))) *
        (((l : ℝ) / 2 * (m * x / n / (1 + m * x / n))) ^ j /
          (j ! * beta (m / 2 + j) (n / 2))) := by
  rw [mul_assoc, scaled_fisherSnedecorPDFReal hm hn hx, poissonMeasure_real_singleton]
  push_cast
  rw [mul_pow]
  ring_nf

/-- The Poisson series of scaled central F densities converges at every real argument. -/
theorem summable_poisson_mul_scaled_fisherSnedecorPDFReal (hm : 0 < m) (hn : 0 < n)
    (l : ℝ≥0) (x : ℝ) :
    Summable fun j : ℕ ↦ (poissonMeasure (l / 2)).real {j} * (m / (m + 2 * j)) *
      fisherSnedecorPDFReal (m + 2 * j) n (m * x / (m + 2 * j)) := by
  by_cases hx : 0 < x
  swap
  · have harg (j : ℕ) : m * x / (m + 2 * j) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hm.le (le_of_not_gt hx))
        (by positivity)
    simp only [fisherSnedecorPDFReal_of_nonpos (harg _), mul_zero, summable_zero]
  simp_rw [poisson_mul_scaled_fisherSnedecorPDFReal hm hn l hx]
  apply Summable.mul_left
  let z := (l : ℝ) / 2 * (m * x / n / (1 + m * x / n))
  let f := fun j : ℕ ↦ z ^ j / (j ! * beta (m / 2 + j) (n / 2))
  by_cases hl : l = 0
  · subst l
    exact summable_of_ne_finset_zero (s := {0}) fun j hj ↦ by
      simp only [Finset.mem_singleton] at hj
      simp [hj]
  have hz : 0 < z := by dsimp [z]; positivity
  have hf (j : ℕ) : 0 < f j := by
    dsimp [f]
    exact div_pos (pow_pos hz _)
      (mul_pos (by positivity) (beta_pos (by positivity) (by positivity)))
  -- The beta recurrence leaves a bounded shape ratio and a factor tending to zero.
  have hratio (j : ℕ) :
      ‖f (j + 1)‖ / ‖f j‖ =
        z / ((j : ℝ) + 1) * ((m / 2 + n / 2 + j) / (m / 2 + j)) := by
    rw [Real.norm_of_nonneg (hf _).le, Real.norm_of_nonneg (hf _).le]
    rw [div_eq_iff (hf j).ne']
    dsimp [f]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ,
      show m / 2 + ((j : ℝ) + 1) = (m / 2 + j) + 1 by ring,
      beta_add_one_left (by positivity) (by positivity)]
    field_simp [(beta_pos (by positivity : 0 < m / 2 + j) (by positivity : 0 < n / 2)).ne']
    ring
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
    (Eventually.of_forall fun j ↦ (hf j).ne')
  simp_rw [hratio]
  have hzero : Tendsto (fun j : ℕ ↦ z / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hone : Tendsto (fun j : ℕ ↦ (m / 2 + n / 2 + j) / (m / 2 + j)) atTop (𝓝 1) := by
    simpa using tendsto_add_mul_div_add_mul_atTop_nhds (m / 2 + n / 2) (m / 2) (1 : ℝ)
      (d := 1) one_ne_zero
  simpa using hzero.mul hone

/-- The defining convergent density series at positive degrees. -/
theorem noncentralFPDFReal_of_pos (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) (x : ℝ) :
    noncentralFPDFReal m n l x =
      ∑' j : ℕ, (poissonMeasure (l / 2)).real {j} * (m / (m + 2 * j)) *
        fisherSnedecorPDFReal (m + 2 * j) n (m * x / (m + 2 * j)) := by
  rw [noncentralFPDFReal, ite_eq_left ⟨hm, hn⟩]

/-- The chosen real density vanishes at invalid degrees. -/
@[simp]
theorem noncentralFPDFReal_of_not_pos (h : ¬ (0 < m ∧ 0 < n)) (l : ℝ≥0) (x : ℝ) :
    noncentralFPDFReal m n l x = 0 := by
  rw [noncentralFPDFReal, ite_eq_right h]

/-- The chosen real density vanishes at nonpositive arguments. -/
@[simp]
theorem noncentralFPDFReal_of_nonpos (hx : x ≤ 0) (m n : ℝ) (l : ℝ≥0) :
    noncentralFPDFReal m n l x = 0 := by
  by_cases h : 0 < m ∧ 0 < n
  · rw [noncentralFPDFReal_of_pos h.1 h.2]
    have harg (j : ℕ) : m * x / (m + 2 * j) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h.1.le hx)
        (add_nonneg h.1.le (by positivity))
    simp only [fisherSnedecorPDFReal_of_nonpos (harg _), mul_zero, tsum_zero]
  · exact noncentralFPDFReal_of_not_pos h l x

/-- The real density is nonnegative at all parameters and arguments. -/
theorem noncentralFPDFReal_nonneg (m n : ℝ) (l : ℝ≥0) (x : ℝ) :
    0 ≤ noncentralFPDFReal m n l x := by
  by_cases h : 0 < m ∧ 0 < n
  · rw [noncentralFPDFReal_of_pos h.1 h.2]
    exact tsum_nonneg fun j ↦ mul_nonneg (mul_nonneg measureReal_nonneg
      (div_nonneg h.1.le (add_nonneg h.1.le (by positivity))))
      (fisherSnedecorPDFReal_nonneg _ _ _)
  · simp [h]

/-- The real density is strictly positive on the positive half-line at valid degrees. -/
theorem noncentralFPDFReal_pos (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) (hx : 0 < x) :
    0 < noncentralFPDFReal m n l x := by
  rw [noncentralFPDFReal_of_pos hm hn]
  apply (summable_poisson_mul_scaled_fisherSnedecorPDFReal hm hn l x).tsum_pos
    (fun j ↦ mul_nonneg (mul_nonneg measureReal_nonneg (by positivity))
      (fisherSnedecorPDFReal_nonneg _ _ _)) 0
  simp only [Nat.cast_zero, mul_zero, add_zero, div_self hm.ne', mul_one,
    mul_div_cancel_left₀ x hm.ne', poissonMeasure_real_singleton, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one]
  rw [fisherSnedecorPDFReal_of_pos hm hn hx]
  have := Gamma_pos_of_pos (by positivity : 0 < (m + n) / 2)
  have := Gamma_pos_of_pos (by positivity : 0 < m / 2)
  have := Gamma_pos_of_pos (by positivity : 0 < n / 2)
  positivity

/-- Zero noncentrality recovers the central F density, including invalid degrees. -/
@[simp]
theorem noncentralFPDFReal_zero_noncentrality (m n x : ℝ) :
    noncentralFPDFReal m n 0 x = fisherSnedecorPDFReal m n x := by
  by_cases h : 0 < m ∧ 0 < n
  · rw [noncentralFPDFReal_of_pos h.1 h.2, tsum_eq_single 0]
    · simp [poissonMeasure_real_singleton, h.1.ne']
    · intro j hj
      simp [poissonMeasure_real_singleton, hj]
  · simp [h]

/-- Invalid degrees have zero extended density. -/
@[simp]
theorem noncentralFPDF_of_not_pos (h : ¬ (0 < m ∧ 0 < n)) (l : ℝ≥0) (x : ℝ) :
    noncentralFPDF m n l x = 0 := by
  simp [noncentralFPDF_eq_ofReal, h]

/-- The extended density vanishes at nonpositive arguments. -/
@[simp]
theorem noncentralFPDF_of_nonpos (hx : x ≤ 0) (m n : ℝ) (l : ℝ≥0) :
    noncentralFPDF m n l x = 0 := by
  simp [noncentralFPDF_eq_ofReal, hx]

/-- Zero noncentrality recovers the central extended density. -/
@[simp]
theorem noncentralFPDF_zero_noncentrality (m n x : ℝ) :
    noncentralFPDF m n 0 x = fisherSnedecorPDF m n x := by
  simp only [noncentralFPDF_eq_ofReal, noncentralFPDFReal_zero_noncentrality,
    fisherSnedecorPDF_eq_ofReal]

/-- Converting the extended density to a real number recovers the real density. -/
@[simp]
theorem toReal_noncentralFPDF (m n : ℝ) (l : ℝ≥0) (x : ℝ) :
    (noncentralFPDF m n l x).toReal = noncentralFPDFReal m n l x :=
  ENNReal.toReal_ofReal (noncentralFPDFReal_nonneg m n l x)

/-- Joint measurability of the real density in both degrees, noncentrality and argument. -/
@[fun_prop]
theorem measurable_uncurry_noncentralFPDFReal :
    Measurable fun p : (ℝ × ℝ × ℝ≥0) × ℝ ↦
      noncentralFPDFReal p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  unfold noncentralFPDFReal
  apply Measurable.ite (by measurability) _ measurable_const
  apply Measurable.tsum
  intro j
  simp only [poissonMeasure_real_singleton]
  refine Measurable.mul (by fun_prop) ?_
  have hpdf : Measurable fun p : (ℝ × ℝ × ℝ≥0) × ℝ ↦
      (fisherSnedecorPDF (p.1.1 + 2 * j) p.1.2.1
        (p.1.1 * p.2 / (p.1.1 + 2 * j))).toReal :=
    (measurable_uncurry_fisherSnedecorPDF.comp
      (f := fun p : (ℝ × ℝ × ℝ≥0) × ℝ ↦
        ((p.1.1 + 2 * j, p.1.2.1), p.1.1 * p.2 / (p.1.1 + 2 * j)))
      (by fun_prop)).ennreal_toReal
  simpa only [toReal_fisherSnedecorPDF] using hpdf

/-- Joint measurability of the extended density. -/
@[fun_prop]
theorem measurable_uncurry_noncentralFPDF :
    Measurable fun p : (ℝ × ℝ × ℝ≥0) × ℝ ↦
      noncentralFPDF p.1.1 p.1.2.1 p.1.2.2 p.2 :=
  measurable_uncurry_noncentralFPDFReal.ennreal_ofReal

/-- Measurability of the real density in its argument. -/
@[fun_prop]
theorem measurable_noncentralFPDFReal (m n : ℝ) (l : ℝ≥0) :
    Measurable (noncentralFPDFReal m n l) :=
  measurable_uncurry_noncentralFPDFReal.comp
    (measurable_const.prodMk measurable_id : Measurable fun x : ℝ ↦ ((m, n, l), x))

/-- Measurability of the extended density in its argument. -/
@[fun_prop]
theorem measurable_noncentralFPDF (m n : ℝ) (l : ℝ≥0) :
    Measurable (noncentralFPDF m n l) :=
  (measurable_noncentralFPDFReal m n l).ennreal_ofReal

/-- The extended density is the Poisson series of scaled central F densities at every point. -/
theorem noncentralFPDF_eq_tsum (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) (x : ℝ) :
    noncentralFPDF m n l x = ∑' j : ℕ, poissonMeasure (l / 2) {j} *
      ENNReal.ofReal (m / (m + 2 * j)) *
        fisherSnedecorPDF (m + 2 * j) n (m * x / (m + 2 * j)) := by
  rw [noncentralFPDF_eq_ofReal, noncentralFPDFReal_of_pos hm hn,
    ENNReal.ofReal_tsum_of_nonneg
      (fun j ↦ mul_nonneg (mul_nonneg measureReal_nonneg (by positivity))
        (fisherSnedecorPDFReal_nonneg _ _ _))
      (summable_poisson_mul_scaled_fisherSnedecorPDFReal hm hn l x)]
  congr 1
  funext j
  rw [ENNReal.ofReal_mul (mul_nonneg measureReal_nonneg (by positivity)),
    ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _), fisherSnedecorPDF_eq_ofReal]

private theorem map_scaled_fisherSnedecorMeasure_eq_withDensity (hm : 0 < m) (n : ℝ)
    (j : ℕ) :
    (fisherSnedecorMeasure (m + 2 * j) n).map (fun x ↦ (m + 2 * j) / m * x) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (m / (m + 2 * j)) *
        fisherSnedecorPDF (m + 2 * j) n (m * x / (m + 2 * j))) := by
  rw [fisherSnedecorMeasure_eq_withDensity]
  have hmap := map_affine_withDensity_volume (a := 0) (b := (m + 2 * j) / m)
    (fisherSnedecorPDF (m + 2 * j) n) (by positivity)
  simp only [zero_add] at hmap
  rw [hmap]
  congr 1
  funext x
  rw [affineDensity_apply, abs_of_pos (by positivity), inv_div, sub_zero]
  congr 2
  field_simp

/-- The noncentral F ratio law has its Poisson-series density, including invalid degrees. -/
theorem noncentralFMeasure_eq_withDensity (m n : ℝ) (l : ℝ≥0) :
    noncentralFMeasure m n l = volume.withDensity (noncentralFPDF m n l) := by
  by_cases h : 0 < m ∧ 0 < n
  · rw [noncentralFMeasure_eq_sum h.1]
    have hg (j : ℕ) : Measurable (fun x : ℝ ↦ ENNReal.ofReal (m / (m + 2 * j)) *
        fisherSnedecorPDF (m + 2 * j) n (m * x / (m + 2 * j))) := by fun_prop
    simp_rw [map_scaled_fisherSnedecorMeasure_eq_withDensity h.1,
      ← withDensity_smul _ (hg _)]
    rw [← withDensity_tsum (fun j ↦ (hg j).const_smul (poissonMeasure (l / 2) {j}))]
    congr 1
    funext x
    rw [Pi.tsum_apply (Pi.summable.2 fun _ ↦ ENNReal.summable), noncentralFPDF_eq_tsum h.1 h.2]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  · rw [noncentralFMeasure_of_not_pos h,
      show noncentralFPDF m n l = 0 from funext (noncentralFPDF_of_not_pos h l), withDensity_zero]

/-- The extended density integrates to one for positive degrees. -/
theorem lintegral_noncentralFPDF_eq_one (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    ∫⁻ x, noncentralFPDF m n l x = 1 := by
  let _ := isProbabilityMeasure_noncentralFMeasure hm hn l
  have h : noncentralFMeasure m n l univ = 1 := measure_univ
  rwa [noncentralFMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h

/-- The real density is integrable, also at invalid degrees where it vanishes. -/
theorem integrable_noncentralFPDFReal (m n : ℝ) (l : ℝ≥0) :
    Integrable (noncentralFPDFReal m n l) := by
  by_cases h : 0 < m ∧ 0 < n
  · refine ⟨(measurable_noncentralFPDFReal m n l).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (noncentralFPDFReal_nonneg m n l))).2 ?_⟩
    simp_rw [← noncentralFPDF_eq_ofReal]
    rw [lintegral_noncentralFPDF_eq_one h.1 h.2]
    norm_num
  · rw [show noncentralFPDFReal m n l = 0 from funext (noncentralFPDFReal_of_not_pos h l)]
    exact integrable_zero _ _ _

/-- The real density integrates to one for positive degrees. -/
theorem integral_noncentralFPDFReal_eq_one (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    ∫ x, noncentralFPDFReal m n l x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (noncentralFPDFReal_nonneg m n l))
    (measurable_noncentralFPDFReal m n l).aestronglyMeasurable]
  simp_rw [← noncentralFPDF_eq_ofReal]
  rw [lintegral_noncentralFPDF_eq_one hm hn, ENNReal.toReal_one]

/-- The Radon–Nikodym derivative of the noncentral F law is the named density. -/
theorem rnDeriv_noncentralFMeasure (m n : ℝ) (l : ℝ≥0) :
    (noncentralFMeasure m n l).rnDeriv volume =ᵐ[volume] noncentralFPDF m n l := by
  rw [noncentralFMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_noncentralFPDF m n l)

/-- The canonical density of a variable with noncentral F law is the named density. -/
theorem pdf_eq_noncentralFPDF_of_hasLaw_noncentralFMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (noncentralFMeasure m n l) P) :
    pdf X P volume =ᵐ[volume] noncentralFPDF m n l := by
  apply pdf_eq_of_hasLaw_withDensity (measurable_noncentralFPDF m n l).aemeasurable
  rwa [← noncentralFMeasure_eq_withDensity]

end TauCeti.Probability
