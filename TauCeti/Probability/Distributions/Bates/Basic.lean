/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.IrwinHall.PDF
public import TauCeti.Probability.Distributions.IrwinHall.Transforms
public import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.Dirac

/-!
# Bates distributions

The Bates law of positive order `n` is the distribution of the average of `n` independent
unit-uniform variables. It is the Irwin–Hall law scaled by `1 / n`. Order zero is totalized
to the zero measure, since an empty sample has no average.

This file transports the Irwin–Hall density, cdf, moments, transforms, and quantiles through
that scaling. In particular, the mean is `1 / 2`, the variance is `1 / (12 * n)`,
and every exponential moment exists. The product-measure and independent-variable
constructions identify this analytic law with a sample average.

The construction uses `irwinHallMeasure` and the affine change-of-variables API in
`TauCeti.Probability.Distributions.Affine`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 26.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

/-- The law of an average of `n` independent unit uniforms, or zero when `n = 0`. -/
def batesMeasure (n : ℕ) : Measure ℝ :=
  if n = 0 then 0 else (irwinHallMeasure n).map (fun x ↦ x / (n : ℝ))

/-- The Bates law is the scaled Irwin–Hall law, with an explicit invalid-order branch. -/
theorem batesMeasure_def (n : ℕ) :
    batesMeasure n = if n = 0 then 0 else (irwinHallMeasure n).map (fun x ↦ x / (n : ℝ)) := (rfl)

/-- There is no order-zero sample average; its law is the zero measure. -/
@[simp]
theorem batesMeasure_zero : batesMeasure 0 = 0 := by
  simp [batesMeasure_def]

/-- At positive order, Bates is the average obtained by scaling an Irwin–Hall sum. -/
theorem batesMeasure_eq_map_irwinHallMeasure {n : ℕ} (hn : 0 < n) :
    batesMeasure n = (irwinHallMeasure n).map (fun x ↦ x / (n : ℝ)) := by
  simp [batesMeasure_def, hn.ne']

/-- Every positive-order Bates law is a probability measure. -/
theorem isProbabilityMeasure_batesMeasure {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (batesMeasure n) := by
  rw [batesMeasure_eq_map_irwinHallMeasure hn]
  infer_instance

/-- Every Bates law is finite, including the order-zero zero measure. -/
instance isFiniteMeasure_batesMeasure (n : ℕ) : IsFiniteMeasure (batesMeasure n) := by
  by_cases hn : n = 0
  · subst n
    simp only [batesMeasure_zero]
    infer_instance
  · have := isProbabilityMeasure_batesMeasure (Nat.pos_of_ne_zero hn)
    infer_instance

/-- A single-observation Bates law is unit uniform. -/
@[simp]
theorem batesMeasure_one : batesMeasure 1 = uniformMeasure 0 1 := by
  simp [batesMeasure_eq_map_irwinHallMeasure zero_lt_one]

/-- The totalized family is measurable in its natural-number order. -/
@[fun_prop]
theorem measurable_batesMeasure : Measurable batesMeasure := measurable_of_countable _

/-- A Bates variable lies in `[0, 1]` almost surely, also for the zero law at order zero. -/
theorem ae_mem_Icc_batesMeasure (n : ℕ) :
    ∀ᵐ x ∂batesMeasure n, x ∈ Icc (0 : ℝ) 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [batesMeasure_eq_map_irwinHallMeasure (Nat.pos_of_ne_zero hn)]
  apply (ae_map_iff (by fun_prop) measurableSet_Icc).2
  filter_upwards [ae_mem_Icc_irwinHallMeasure n] with x hx
  exact ⟨div_nonneg hx.1 hnR.le, (div_le_one hnR).2 hx.2⟩

/-- Averaging a nonempty finite product of unit uniforms gives the Bates law. -/
theorem map_average_pi_uniformMeasure_zero_one {ι : Type*} [Fintype ι] [Nonempty ι] :
    (Measure.pi fun _ : ι ↦ uniformMeasure 0 1).map
        (fun x ↦ (∑ i, x i) / (Fintype.card ι : ℝ)) = batesMeasure (Fintype.card ι) := by
  rw [batesMeasure_eq_map_irwinHallMeasure Fintype.card_pos,
    ← map_sum_pi_uniformMeasure_zero_one, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Multiplying a positive-order Bates variable by its order recovers the Irwin–Hall law. -/
theorem map_mul_batesMeasure {n : ℕ} (hn : 0 < n) :
    (batesMeasure n).map (fun x ↦ (n : ℝ) * x) = irwinHallMeasure n := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [batesMeasure_eq_map_irwinHallMeasure hn, Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def, mul_div_cancel₀, hnR]

/-- The real Bates density is the scaled Irwin–Hall density. Its order-zero value is zero. -/
def batesPDFReal (n : ℕ) (x : ℝ) : ℝ := (n : ℝ) * irwinHallPDFReal n (n * x)

/-- Scaling the sum to an average multiplies its density by the order. -/
theorem batesPDFReal_def (n : ℕ) (x : ℝ) :
    batesPDFReal n x = (n : ℝ) * irwinHallPDFReal n (n * x) := (rfl)

/-- The extended nonnegative Bates density. -/
def batesPDF (n : ℕ) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (batesPDFReal n x)

/-- The extended density is the nonnegative lift of the real density. -/
theorem batesPDF_eq_ofReal (n : ℕ) (x : ℝ) :
    batesPDF n x = ENNReal.ofReal (batesPDFReal n x) := (rfl)

/-- The chosen real density vanishes at order zero. -/
@[simp]
theorem batesPDFReal_zero (x : ℝ) : batesPDFReal 0 x = 0 := by
  simp [batesPDFReal]

/-- The real density at order one is unit uniform. -/
@[simp]
theorem batesPDFReal_one (x : ℝ) : batesPDFReal 1 x = uniformPDFReal 0 1 x := by
  simp [batesPDFReal]

/-- From order two onward the Bates density is an alternating sum of truncated powers. -/
theorem batesPDFReal_eq {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    batesPDFReal n x = (n : ℝ) *
      (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) *
        max (n * x - k) 0 ^ (n - 1)) / (n - 1).factorial := by
  rw [batesPDFReal, irwinHallPDFReal_eq hn, mul_div_assoc]

/-- The chosen real Bates density is nonnegative at every order. -/
theorem batesPDFReal_nonneg (n : ℕ) (x : ℝ) : 0 ≤ batesPDFReal n x := by
  rw [batesPDFReal_def]
  exact mul_nonneg (Nat.cast_nonneg n) (irwinHallPDFReal_nonneg n _)

/-- Taking the real value of the extended density recovers the real density. -/
@[simp]
theorem toReal_batesPDF (n : ℕ) (x : ℝ) : (batesPDF n x).toReal = batesPDFReal n x := by
  rw [batesPDF_eq_ofReal, ENNReal.toReal_ofReal (batesPDFReal_nonneg n x)]

/-- Every real Bates density is measurable. -/
@[fun_prop]
theorem measurable_batesPDFReal (n : ℕ) : Measurable (batesPDFReal n) := by
  unfold batesPDFReal
  exact measurable_const.mul ((measurable_irwinHallPDFReal n).comp (by fun_prop))

/-- Every extended Bates density is measurable. -/
@[fun_prop]
theorem measurable_batesPDF (n : ℕ) : Measurable (batesPDF n) :=
  (measurable_batesPDFReal n).ennreal_ofReal

/-- At every order the Bates law is Lebesgue measure weighted by its named density. -/
theorem batesMeasure_eq_withDensity (n : ℕ) :
    batesMeasure n = volume.withDensity (batesPDF n) := by
  by_cases hn : n = 0
  · subst n
    have hzero : batesPDF 0 = 0 := by
      ext x
      simp [batesPDF_eq_ofReal]
    rw [batesMeasure_zero, hzero, withDensity_zero]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hmap := map_affine_withDensity_volume (a := 0) (b := (n : ℝ)⁻¹)
    (irwinHallPDF n) (inv_ne_zero hnR.ne')
  rw [← irwinHallMeasure_eq_withDensity (Nat.pos_of_ne_zero hn)] at hmap
  rw [batesMeasure_eq_map_irwinHallMeasure (Nat.pos_of_ne_zero hn)]
  calc
    _ = (irwinHallMeasure n).map (fun x ↦ 0 + (n : ℝ)⁻¹ * x) := by
      congr 1
      ext x
      simp [div_eq_mul_inv, mul_comm]
    _ = volume.withDensity (affineDensity 0 (n : ℝ)⁻¹ (irwinHallPDF n)) := hmap
    _ = _ := by
      congr 1
      ext x
      simp [affineDensity_apply, abs_of_pos (inv_pos.mpr hnR), batesPDF_eq_ofReal,
        batesPDFReal, irwinHallPDF_eq_ofReal, ENNReal.ofReal_mul (Nat.cast_nonneg n), mul_comm]

/-- A Bates variable has a Lebesgue density, including for the order-zero zero measure. -/
theorem hasPDF_of_hasLaw_batesMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {n : ℕ} (hX : HasLaw X (batesMeasure n) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_batesPDF n).aemeasurable
    (by rwa [batesMeasure_eq_withDensity] at hX)

/-- The canonical density of a Bates variable is its named density almost everywhere. -/
theorem pdf_eq_batesPDF_of_hasLaw_batesMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {n : ℕ} (hX : HasLaw X (batesMeasure n) P) :
    pdf X P =ᵐ[volume] batesPDF n :=
  pdf_eq_of_hasLaw_withDensity (measurable_batesPDF n).aemeasurable
    (by rwa [batesMeasure_eq_withDensity] at hX)

/-- The Radon–Nikodym derivative of a Bates law is its named density. -/
theorem rnDeriv_batesMeasure (n : ℕ) :
    (batesMeasure n).rnDeriv volume =ᵐ[volume] batesPDF n := by
  rw [batesMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_batesPDF n)

/-- The cdf of a positive-order Bates law is the Irwin–Hall cdf at the scaled argument. -/
theorem cdf_batesMeasure {n : ℕ} (hn : 0 < n) (x : ℝ) :
    cdf (batesMeasure n) x = cdf (irwinHallMeasure n) (n * x) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simpa [batesMeasure_eq_map_irwinHallMeasure hn, div_eq_mul_inv, mul_comm] using
    cdf_map_affine_of_pos (μ := irwinHallMeasure n) (a := 0) (inv_pos.mpr hnR) x

/-- The Bates cdf is an alternating truncated-power polynomial, valid at its knots too. -/
theorem cdf_batesMeasure_eq {n : ℕ} (hn : 0 < n) (x : ℝ) :
    cdf (batesMeasure n) x =
      (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) *
        max (n * x - k) 0 ^ n) / n.factorial := by
  rw [cdf_batesMeasure hn, cdf_irwinHallMeasure_eq hn]

open scoped Pointwise in
/-- Bates quantiles are the scaled Irwin–Hall quantiles at every order `n` and every level `u`.
For `u ≤ 0` and `1 < u` both sides are zero by the junk-value convention of `Measure.quantile`;
at `u = 1` the identity relates the least points where the two cdfs reach one. At order zero
both sides are zero: the right side divides by zero, and Mathlib's cdf of the zero measure is
the default step cdf, which is the cdf of `dirac 0`, so its quantile is zero at every level. -/
theorem quantile_batesMeasure (n : ℕ) (u : ℝ) :
    (batesMeasure n).quantile u = (irwinHallMeasure n).quantile u / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- Mathlib builds `cdf 0` from a Radon–Nikodym derivative that does not depend on the
    -- level, so it is not a Stieltjes point and `toRatCDF` falls back to `defaultRatCDF`.
    have hcdf (x : ℝ) : cdf (0 : Measure ℝ) x = cdf (Measure.dirac 0) x := by
      set f : Unit → ℚ → ℝ := fun a r ↦ (preCDF (0 : Measure (Unit × ℝ)) r a).toReal
      have hf : f () = fun _ ↦ f () 0 := funext fun r ↦ by simp [f, preCDF, Measure.IicSnd]
      have hnot : ¬IsRatStieltjesPoint f () := fun h ↦ by
        have h1 := h.tendsto_atTop_one
        have h0 := h.tendsto_atBot_zero
        rw [hf, tendsto_const_nhds_iff] at h1 h0
        exact one_ne_zero (h1.symm.trans h0)
      rw [← StieltjesFunction.iInf_rat_gt_eq, ← StieltjesFunction.iInf_rat_gt_eq]
      congr! 2 with q
      rw [cdf, Measure.prod_zero, condCDF, stieltjesOfMeasurableRat_eq, cdf_dirac]
      change toRatCDF f () q = _
      simp only [toRatCDF, hnot, ↓reduceIte, defaultRatCDF, ← not_lt, ite_not, Rat.cast_lt_zero]
    rw [batesMeasure_zero, Nat.cast_zero, div_zero,
      Measure.quantile_eq_of_le_cdf_iff 0 (Measure.dirac 0) fun x ↦ by rw [hcdf]]
    rcases le_or_gt u 0 with h0 | h0
    · exact Measure.quantile_of_nonpos _ h0
    rcases le_or_gt u 1 with h1 | h1
    · exact Measure.quantile_dirac 0 h0 h1
    · exact Measure.quantile_of_one_lt _ h1
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hset : {x : ℝ | u ≤ cdf (batesMeasure n) x} =
      (n : ℝ)⁻¹ • {y : ℝ | u ≤ cdf (irwinHallMeasure n) y} := by
    ext x
    rw [Set.mem_inv_smul_set_iff₀ hnR.ne']
    simp [cdf_batesMeasure hn, smul_eq_mul]
  rw [Measure.quantile_def, Measure.quantile_def, hset,
    Real.sInf_smul_of_nonneg (inv_nonneg.mpr hnR.le), smul_eq_mul, div_eq_inv_mul]

/-- Every exponential moment of every Bates law exists. -/
@[simp]
theorem integrableExpSet_id_batesMeasure (n : ℕ) :
    integrableExpSet id (batesMeasure n) = univ := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, id_eq, mem_univ, iff_true]
  exact integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable (ae_mem_Icc_batesMeasure n)

/-- Every natural moment of every Bates law is integrable. -/
@[simp]
theorem integrable_pow_batesMeasure (n k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k) (batesMeasure n) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := id)
  simp

/-- The mean of a positive-order Bates law is one half. -/
@[simp]
theorem integral_id_batesMeasure {n : ℕ} (hn : 0 < n) :
    ∫ x, x ∂batesMeasure n = (1 : ℝ) / 2 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hint : Integrable id (irwinHallMeasure n) := by
    apply integrable_of_mem_interior_integrableExpSet
    simp
  have h := integral_id_map_affine (μ := irwinHallMeasure n) (a := 0) (b := (n : ℝ)⁻¹) hint
  simpa [batesMeasure_eq_map_irwinHallMeasure hn, div_eq_mul_inv, mul_comm, hnR] using h

/-- The variance of a Bates law is `1 / (12 * n)`. At order zero both sides are zero: the
zero measure has variance zero, and `1 / (12 * 0) = 0` by the division-by-zero convention. -/
@[simp]
theorem variance_id_batesMeasure (n : ℕ) :
    Var[id; batesMeasure n] = 1 / (12 * (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h := variance_id_map_affine (μ := irwinHallMeasure n) (a := 0) (b := (n : ℝ)⁻¹)
  rw [batesMeasure_eq_map_irwinHallMeasure hn]
  simp only [zero_add, variance_id_irwinHallMeasure, mul_comm ((n : ℝ)⁻¹),
    ← div_eq_mul_inv] at h
  rw [h]
  field_simp

/-- Away from zero, the Bates mgf is the `n`th power of the uniform mgf at `t / n`.
Its value at zero is one under the positive-order probability law. -/
@[simp]
theorem mgf_id_batesMeasure {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ≠ 0) :
    mgf id (batesMeasure n) t = ((exp (t / n) - 1) / (t / n)) ^ n := by
  have hnt : (n : ℝ)⁻¹ * t ≠ 0 := mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne')) ht
  have h := mgf_id_map_affine (μ := irwinHallMeasure n) (a := 0) (b := (n : ℝ)⁻¹) t
  rw [mgf_id_irwinHallMeasure n hnt] at h
  simpa [batesMeasure_eq_map_irwinHallMeasure hn, div_eq_mul_inv, mul_comm] using h

/-- The Bates cgf is `n` times the logarithm of the uniform-mgf factor at `t / n`, at every
order and frequency. At order zero both sides are zero, since the zero measure has cgf
`log 0 = 0`. At `t = 0` the cgf of the probability law is `log 1 = 0`, and the right side is
`n * log (0 / 0) = 0` by the conventions `0 / 0 = 0` and `log 0 = 0`. -/
@[simp]
theorem cgf_id_batesMeasure (n : ℕ) (t : ℝ) :
    cgf id (batesMeasure n) t = n * log ((exp (t / n) - 1) / (t / n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases eq_or_ne t 0 with rfl | ht
  · have := isProbabilityMeasure_batesMeasure hn
    simp
  · rw [cgf, mgf_id_batesMeasure hn ht, log_pow]

/-- The Bates characteristic function is the `n`th power of the scaled uniform transform.
At frequency zero it is one under the positive-order probability law. -/
@[simp]
theorem charFun_batesMeasure {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ≠ 0) :
    charFun (batesMeasure n) t =
      ((Complex.exp (Complex.I * (t / n)) - 1) / (Complex.I * (t / n))) ^ n := by
  have hnt : (n : ℝ)⁻¹ * t ≠ 0 := mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne')) ht
  have h := charFun_map_affine (μ := irwinHallMeasure n) (a := 0) (b := (n : ℝ)⁻¹) t
  rw [charFun_irwinHallMeasure n hnt] at h
  simpa [batesMeasure_eq_map_irwinHallMeasure hn, div_eq_mul_inv, mul_comm] using h

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- Averaging a nonempty finite independent family of unit uniforms has the Bates law. -/
theorem iIndepFun.hasLaw_average_batesMeasure {ι Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace Ω] {P : Measure Ω} {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (uniformMeasure 0 1) P) :
    HasLaw (fun ω ↦ (∑ i, X i ω) / (Fintype.card ι : ℝ)) (batesMeasure (Fintype.card ι)) P := by
  have hsum := hindep.hasLaw_sum_irwinHallMeasure hX
  rw [batesMeasure_eq_map_irwinHallMeasure Fintype.card_pos]
  simpa only [Finset.sum_apply] using
    (hasLaw_map (by fun_prop : AEMeasurable (fun x : ℝ ↦ x / (Fintype.card ι : ℝ))
      (irwinHallMeasure (Fintype.card ι)))).fun_comp hsum

end ProbabilityTheory
