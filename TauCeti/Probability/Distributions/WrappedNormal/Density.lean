/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.WrappedNormal.Basic
public import TauCeti.Probability.Density
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import TauCeti.Analysis.SpecialFunctions.Gaussian.LatticeSum
import TauCeti.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import TauCeti.Probability.Distributions.Gaussian.Periodization
import TauCeti.MeasureTheory.Measure.AddCircle

/-!
# Density of the wrapped normal law

At positive variance `v`, the wrapped normal law with location `m` has a continuous, strictly
positive density relative to normalized Haar measure on `AddCircle (2 * π)`. It is `2 * π` times
the periodized Gaussian density: for real representatives `a` of `m` and `x` of `θ`,

`wrappedNormalPDFReal a v x = 2 * π * ∑ k : ℤ, gaussianPDFReal a v (x + 2 * π * k)`.

The density is defined on circle points, so it does not depend on the chosen representatives.
By Poisson summation it also has the Fourier-series form

`wrappedNormalPDFReal a v x = 1 + 2 * ∑ n ≥ 1, exp (-n ^ 2 * v / 2) * cos (n * (x - a))`,

and this cosine series converges uniformly in `x`, so it may be integrated termwise. Both
expressions are bridged through the Gaussian lattice sum `Real.gaussianLatticeSum`.

The real and extended nonnegative densities are totalized at variance zero by the zero function:
the zero-variance law is a Dirac mass with no density relative to Haar measure.

The measure identity is obtained by reducing the Gaussian law, together with its density, modulo
`2 * π` (`AddCircle.map_coe_withDensity`).

## References

* K. V. Mardia and P. E. Jupp, *Directional Statistics*, Wiley, 2000, section 3.5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

local instance instFactTwoPiPosWrappedNormal : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The real density of the wrapped normal law relative to normalized Haar measure: `2 * π` times
the periodization of the centred Gaussian density, evaluated at `θ - m`. At variance zero it is
the zero function. -/
def wrappedNormalPDFReal (m : AddCircle (2 * π)) (v : ℝ≥0) (θ : AddCircle (2 * π)) : ℝ :=
  2 * π * QuotientAddGroup.automorphize (gaussianPDFReal 0 v) (θ - m)

/-- The extended nonnegative density of the wrapped normal law relative to normalized Haar
measure. -/
def wrappedNormalPDF (m : AddCircle (2 * π)) (v : ℝ≥0) (θ : AddCircle (2 * π)) : ℝ≥0∞ :=
  ENNReal.ofReal (wrappedNormalPDFReal m v θ)

theorem wrappedNormalPDFReal_def (m : AddCircle (2 * π)) (v : ℝ≥0) (θ : AddCircle (2 * π)) :
    wrappedNormalPDFReal m v θ =
      2 * π * QuotientAddGroup.automorphize (gaussianPDFReal 0 v) (θ - m) := by
  rw [wrappedNormalPDFReal]

/-- The extended density is obtained from the real density by `ENNReal.ofReal`. -/
@[simp]
theorem wrappedNormalPDF_apply (m : AddCircle (2 * π)) (v : ℝ≥0) (θ : AddCircle (2 * π)) :
    wrappedNormalPDF m v θ = ENNReal.ofReal (wrappedNormalPDFReal m v θ) := by
  rw [wrappedNormalPDF]

/-- In real representatives, the wrapped normal density is `2 * π` times the periodized Gaussian
density with mean `a`. -/
theorem wrappedNormalPDFReal_coe (a : ℝ) (v : ℝ≥0) (x : ℝ) :
    wrappedNormalPDFReal a v x = 2 * π * ∑' k : ℤ, gaussianPDFReal a v (x + 2 * π * k) := by
  rw [wrappedNormalPDFReal_def, ← AddCircle.coe_sub, AddCircle.automorphize_coe]
  congr 1
  refine tsum_congr fun k ↦ ?_
  rw [zsmul_eq_mul, sub_add_eq_add_sub, gaussianPDFReal_sub, zero_add, mul_comm (k : ℝ)]

/-- At variance zero the totalized real density is identically zero, reflecting the singular
Dirac law at that variance. -/
@[simp]
theorem wrappedNormalPDFReal_zero_var (m θ : AddCircle (2 * π)) :
    wrappedNormalPDFReal m 0 θ = 0 := by
  induction m using QuotientAddGroup.induction_on with | H a => ?_
  induction θ using QuotientAddGroup.induction_on with | H x => ?_
  simp [wrappedNormalPDFReal_coe, gaussianPDFReal_zero_var]

/-- In real representatives, the wrapped normal density is a rescaled Gaussian lattice sum. This
holds at every variance, both sides vanishing at variance zero. -/
theorem wrappedNormalPDFReal_coe_eq_gaussianLatticeSum (a : ℝ) (v : ℝ≥0) (x : ℝ) :
    wrappedNormalPDFReal a v x =
      √(2 * π) / √(v : ℝ) * gaussianLatticeSum ((a - x) / (2 * π)) (√(v : ℝ) / (2 * π)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rw [wrappedNormalPDFReal_def, ← AddCircle.coe_sub, AddCircle.automorphize_coe,
    (hasSum_gaussianPDFReal_add_zsmul 0 hv two_pi_pos.ne' (x - a)).tsum_eq, zero_sub, neg_sub,
    sqrt_mul two_pi_pos.le, ← mul_assoc, mul_inv, ← mul_assoc]
  congr 1
  rw [← div_eq_mul_inv (2 * π), Real.div_sqrt, div_eq_mul_inv]

/-- **Fourier series of the wrapped normal density.** At positive variance, in real
representatives, the density is `1 + 2 * ∑ n ≥ 1, exp (-n ^ 2 * v / 2) * cos (n * (x - a))`. -/
theorem hasSum_wrappedNormalPDFReal_coe {v : ℝ≥0} (hv : v ≠ 0) (a x : ℝ) :
    HasSum (fun n : ℕ ↦ 2 * rexp (-((n + 1 : ℝ) ^ 2 * v / 2)) * cos ((n + 1 : ℝ) * (x - a)))
      (wrappedNormalPDFReal a v x - 1) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs : 0 < √(v : ℝ) / (2 * π) := div_pos (sqrt_pos.mpr hv') two_pi_pos
  have h2π : √(2 * π) ^ 2 = 2 * π := sq_sqrt two_pi_pos.le
  have h := (hasSum_gaussianLatticeCosineSeries ((a - x) / (2 * π)) (√(v : ℝ) / (2 * π))).mul_left
    (√(2 * π) / √(v : ℝ))
  rw [wrappedNormalPDFReal_coe_eq_gaussianLatticeSum]
  rw [abs_of_pos hs] at h
  convert h using 1
  · funext n
    have hcos : cos (2 * π * (n + 1 : ℝ) * ((a - x) / (2 * π))) = cos ((n + 1 : ℝ) * (x - a)) := by
      rw [← cos_neg]
      congr 1
      field_simp
      ring
    have hexp : -2 * π ^ 2 * (√(v : ℝ) / (2 * π)) ^ 2 * (n + 1 : ℝ) ^ 2 =
        -((n + 1 : ℝ) ^ 2 * v / 2) := by
      rw [div_pow, sq_sqrt hv'.le]
      field_simp
    rw [hcos, hexp]
    field_simp
    rw [h2π]
    ring
  · rw [mul_sub]
    congr 1
    field_simp
    exact h2π.symm

/-- The Fourier series of the wrapped normal density converges uniformly in the real
representative of the angle, so it may be integrated termwise. -/
theorem hasSumUniformly_wrappedNormalPDFReal_coe {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) :
    HasSumUniformly
      (fun n : ℕ ↦ fun x : ℝ ↦
        2 * rexp (-((n + 1 : ℝ) ^ 2 * v / 2)) * cos ((n + 1 : ℝ) * (x - a)))
      (fun x ↦ wrappedNormalPDFReal a v x - 1) := by
  have hu : Summable fun n : ℕ ↦ 2 * rexp (-((n + 1 : ℝ) ^ 2 * v / 2)) := by
    simpa using (hasSum_wrappedNormalPDFReal_coe hv a a).summable
  simp_rw [← (hasSum_wrappedNormalPDFReal_coe hv a _).tsum_eq, ← hasSumUniformlyOn_univ_iff]
  exact .of_norm_le_summable hu fun _ _ _ ↦
    (norm_mul_le_of_le (norm_of_nonneg (by positivity)).le (abs_cos_le_one _)).trans_eq (mul_one _)

/-- The real wrapped normal density is nonnegative. -/
theorem wrappedNormalPDFReal_nonneg (m : AddCircle (2 * π)) (v : ℝ≥0) (θ : AddCircle (2 * π)) :
    0 ≤ wrappedNormalPDFReal m v θ := by
  induction m using QuotientAddGroup.induction_on with | H a => ?_
  induction θ using QuotientAddGroup.induction_on with | H x => ?_
  rw [wrappedNormalPDFReal_coe]
  exact mul_nonneg two_pi_pos.le (tsum_nonneg fun _ ↦ gaussianPDFReal_nonneg _ _ _)

/-- At positive variance the wrapped normal density is strictly positive at every circle point. -/
theorem wrappedNormalPDFReal_pos (m : AddCircle (2 * π)) {v : ℝ≥0} (hv : v ≠ 0)
    (θ : AddCircle (2 * π)) : 0 < wrappedNormalPDFReal m v θ := by
  induction m using QuotientAddGroup.induction_on with | H a => ?_
  induction θ using QuotientAddGroup.induction_on with | H x => ?_
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [wrappedNormalPDFReal_coe_eq_gaussianLatticeSum]
  exact mul_pos (div_pos (sqrt_pos.mpr two_pi_pos) (sqrt_pos.mpr hv'))
    (gaussianLatticeSum_pos _ (div_ne_zero (sqrt_ne_zero'.mpr hv') two_pi_pos.ne'))

/-- The real wrapped normal density is continuous at every variance. -/
@[fun_prop]
theorem continuous_wrappedNormalPDFReal (m : AddCircle (2 * π)) (v : ℝ≥0) :
    Continuous (wrappedNormalPDFReal m v) := by
  induction m using QuotientAddGroup.induction_on with | H a => ?_
  refine (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
  simp only [Function.comp_def, wrappedNormalPDFReal_coe_eq_gaussianLatticeSum]
  exact continuous_const.mul ((contDiff_gaussianLatticeSum _ (n := 0)).continuous.comp
    ((continuous_const.sub continuous_id).div_const _))

/-- The extended wrapped normal density is measurable at every variance. -/
@[fun_prop]
theorem measurable_wrappedNormalPDF (m : AddCircle (2 * π)) (v : ℝ≥0) :
    Measurable (wrappedNormalPDF m v) :=
  (continuous_wrappedNormalPDFReal m v).measurable.ennreal_ofReal

/-- At positive variance the wrapped normal law is normalized Haar measure weighted by its named
density. -/
theorem wrappedNormalMeasure_eq_withDensity (m : AddCircle (2 * π)) {v : ℝ≥0} (hv : v ≠ 0) :
    wrappedNormalMeasure m v = AddCircle.haarAddCircle.withDensity (wrappedNormalPDF m v) := by
  induction m using QuotientAddGroup.induction_on with | H a => ?_
  rw [wrappedNormalMeasure_coe, gaussianReal_of_var_ne_zero _ hv,
    AddCircle.map_coe_withDensity (measurable_gaussianPDF a v),
    AddCircle.volume_eq_smul_haarAddCircle, withDensity_smul_measure,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext θ
  induction θ using QuotientAddGroup.induction_on with | H x => ?_
  rw [Pi.smul_apply, smul_eq_mul, AddCircle.automorphize_coe, wrappedNormalPDF_apply,
    wrappedNormalPDFReal_coe, ENNReal.ofReal_mul two_pi_pos.le,
    ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ gaussianPDFReal_nonneg _ _ _)
      ((summable_gaussianPDFReal_add_zsmul a v two_pi_pos.ne' x).congr fun k ↦ by
        rw [zsmul_eq_mul, mul_comm (k : ℝ)])]
  refine congrArg _ (tsum_congr fun k ↦ ?_)
  rw [gaussianPDF, zsmul_eq_mul, mul_comm (k : ℝ)]

/-- At positive variance the wrapped normal real density integrates to one against normalized
Haar measure. -/
theorem integral_wrappedNormalPDFReal (m : AddCircle (2 * π)) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ θ, wrappedNormalPDFReal m v θ ∂AddCircle.haarAddCircle = 1 := by
  have hint : Integrable (wrappedNormalPDFReal m v) AddCircle.haarAddCircle := by
    simpa only [integrableOn_univ] using
      (continuous_wrappedNormalPDFReal m v).continuousOn.integrableOn_compact'
        (μ := AddCircle.haarAddCircle) isCompact_univ MeasurableSet.univ
  have h := measure_univ (μ := wrappedNormalMeasure m v)
  rw [wrappedNormalMeasure_eq_withDensity m hv, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h
  simp_rw [wrappedNormalPDF_apply] at h
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ (wrappedNormalPDFReal_nonneg m v))] at h
  exact (ENNReal.ofReal_eq_one.mp h)

/-- The Radon–Nikodym derivative of a positive-variance wrapped normal law relative to normalized
Haar measure is its named density. -/
theorem rnDeriv_wrappedNormalMeasure (m : AddCircle (2 * π)) {v : ℝ≥0} (hv : v ≠ 0) :
    (wrappedNormalMeasure m v).rnDeriv AddCircle.haarAddCircle =ᵐ[AddCircle.haarAddCircle]
      wrappedNormalPDF m v := by
  rw [wrappedNormalMeasure_eq_withDensity m hv]
  exact Measure.rnDeriv_withDensity AddCircle.haarAddCircle (measurable_wrappedNormalPDF m v)

/-- A random angle with a positive-variance wrapped normal law has a density relative to
normalized Haar measure. -/
theorem hasPDF_of_hasLaw_wrappedNormalMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → AddCircle (2 * π)} {m : AddCircle (2 * π)} {v : ℝ≥0}
    (hX : HasLaw X (wrappedNormalMeasure m v) P) (hv : v ≠ 0) :
    HasPDF X P AddCircle.haarAddCircle := by
  rw [wrappedNormalMeasure_eq_withDensity m hv] at hX
  exact hasPDF_of_hasLaw_withDensity (measurable_wrappedNormalPDF m v).aemeasurable hX

/-- The density of a random angle with a positive-variance wrapped normal law agrees almost
everywhere with the named wrapped normal density. -/
theorem pdf_eq_wrappedNormalPDF_of_hasLaw_wrappedNormalMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → AddCircle (2 * π)}
    {m : AddCircle (2 * π)} {v : ℝ≥0}
    (hX : HasLaw X (wrappedNormalMeasure m v) P) (hv : v ≠ 0) :
    pdf X P AddCircle.haarAddCircle =ᵐ[AddCircle.haarAddCircle] wrappedNormalPDF m v := by
  rw [wrappedNormalMeasure_eq_withDensity m hv] at hX
  exact pdf_eq_of_hasLaw_withDensity (measurable_wrappedNormalPDF m v).aemeasurable hX

end TauCeti.Probability
