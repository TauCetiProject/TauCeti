/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.WrappedCauchy.Basic
public import TauCeti.Probability.Density
import TauCeti.Analysis.Complex.Poisson.Integral
import TauCeti.MeasureTheory.Integral.Circle.Haar
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Fourier

/-!
# Density of the wrapped Cauchy law

At positive scale `γ`, the wrapped Cauchy law with location `m` has density relative to normalized
Haar measure given by the Poisson kernel with pole `exp (-γ) exp (i m)`. In angular coordinates,
this is

`(1 - exp (-γ) ^ 2) / (1 + exp (-γ) ^ 2 - 2 * exp (-γ) * cos (θ - m))`.

The real and extended nonnegative densities are totalized at scale zero by the zero function. This
correctly records that the zero-scale Dirac law has no density relative to Haar measure, while the
measure identity and random-variable density interfaces are stated at positive scale.

The proof converts Haar integrals on the additive circle to circle averages. The Poisson integral
formula computes every integer Fourier moment of the weighted Haar measure, and uniqueness of
Fourier moments for circle probability measures identifies it with the wrapped Cauchy law.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), section 3.5.7.
-/

public section

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped ENNReal NNReal

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

namespace TauCeti.Probability

/-- The real Poisson-kernel density of the wrapped Cauchy family relative to normalized Haar
measure. At scale zero it is the zero function. -/
def wrappedCauchyPDFReal (m : AddCircle (2 * π)) (γ : ℝ≥0)
    (θ : AddCircle (2 * π)) : ℝ :=
  (1 - Real.exp (-(γ : ℝ)) ^ 2) /
    (1 + Real.exp (-(γ : ℝ)) ^ 2 -
      2 * Real.exp (-(γ : ℝ)) * Real.Angle.cos (θ - m))

/-- The extended nonnegative density of the wrapped Cauchy family relative to normalized Haar
measure. -/
def wrappedCauchyPDF (m : AddCircle (2 * π)) (γ : ℝ≥0)
    (θ : AddCircle (2 * π)) : ℝ≥0∞ :=
  ENNReal.ofReal (wrappedCauchyPDFReal m γ θ)

/-- The wrapped Cauchy density in angular coordinates. -/
theorem wrappedCauchyPDFReal_apply (m : AddCircle (2 * π)) (γ : ℝ≥0)
    (θ : AddCircle (2 * π)) :
    wrappedCauchyPDFReal m γ θ =
      (1 - Real.exp (-(γ : ℝ)) ^ 2) /
        (1 + Real.exp (-(γ : ℝ)) ^ 2 -
          2 * Real.exp (-(γ : ℝ)) * Real.Angle.cos (θ - m)) := by
  rw [wrappedCauchyPDFReal]

/-- The extended density is obtained from the real density by `ENNReal.ofReal`. -/
@[simp]
theorem wrappedCauchyPDF_apply (m : AddCircle (2 * π)) (γ : ℝ≥0)
    (θ : AddCircle (2 * π)) :
    wrappedCauchyPDF m γ θ = ENNReal.ofReal (wrappedCauchyPDFReal m γ θ) := by
  rw [wrappedCauchyPDF]

private theorem poissonKernel_eq_wrappedCauchyPDFReal (m : AddCircle (2 * π)) (γ : ℝ≥0)
    (θ : AddCircle (2 * π)) :
    poissonKernel 0 ((Real.exp (-(γ : ℝ)) : ℂ) * (AddCircle.toCircle m : ℂ))
        (AddCircle.toCircle θ) = wrappedCauchyPDFReal m γ θ := by
  induction m using QuotientAddGroup.induction_on with | H a => ?_
  induction θ using QuotientAddGroup.induction_on with | H x => ?_
  rw [wrappedCauchyPDFReal, poissonKernel_def]
  have hden :
      ‖(AddCircle.toCircle (↑x : AddCircle (2 * π)) : ℂ) -
          (Real.exp (-(γ : ℝ)) : ℂ) *
            (AddCircle.toCircle (↑a : AddCircle (2 * π)) : ℂ)‖ ^ 2 =
        1 + Real.exp (-(γ : ℝ)) ^ 2 -
          2 * Real.exp (-(γ : ℝ)) * Real.cos (x - a) := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, AddCircle.toCircle_apply_mk, Complex.exp_re,
      Complex.exp_im, Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq a]
  simp only [sub_zero]
  rw [hden]
  simp only [Circle.norm_coe, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_exp, one_pow, mul_one]
  rw [← QuotientAddGroup.mk_sub]
  -- `Real.Angle.cos_coe` is stated for the coercion `ℝ → Real.Angle`, which agrees with the
  -- quotient map to `AddCircle (2 * π)` only after unfolding `Real.Angle`, so it cannot rewrite.
  exact congrArg (fun c ↦ (1 - Real.exp (-(γ : ℝ)) ^ 2) /
      (1 + Real.exp (-(γ : ℝ)) ^ 2 - 2 * Real.exp (-(γ : ℝ)) * c))
    (Real.Angle.cos_coe (x - a)).symm

/-- At scale zero the totalized real density is identically zero, reflecting the singular Dirac
law at that scale. -/
@[simp]
theorem wrappedCauchyPDFReal_zero_scale (m θ : AddCircle (2 * π)) :
    wrappedCauchyPDFReal m 0 θ = 0 := by
  rw [wrappedCauchyPDFReal_apply]
  simp

private lemma wrappedCauchy_pole_mem_ball (m : AddCircle (2 * π)) {γ : ℝ≥0}
    (hγ : 0 < γ) :
    (Real.exp (-(γ : ℝ)) : ℂ) * (AddCircle.toCircle m : ℂ) ∈ Metric.ball 0 1 := by
  rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Circle.norm_coe, mul_one]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (NNReal.coe_pos.mpr hγ))

private theorem continuous_wrappedCauchyPDFReal_of_pos (m : AddCircle (2 * π))
    {γ : ℝ≥0} (hγ : 0 < γ) : Continuous (wrappedCauchyPDFReal m γ) := by
  refine Continuous.congr ?_ (poissonKernel_eq_wrappedCauchyPDFReal m γ)
  have hnot : (Real.exp (-(γ : ℝ)) : ℂ) * (AddCircle.toCircle m : ℂ) ∉
      Metric.sphere 0 |(1 : ℝ)| := by
    intro hs
    have hlt := wrappedCauchy_pole_mem_ball m hγ
    rw [Metric.mem_ball, dist_zero_right] at hlt
    rw [Metric.mem_sphere, dist_zero_right, abs_one] at hs
    linarith
  apply (continuousOn_poissonKernel_sphere (R := (1 : ℝ)) hnot).comp_continuous
    (by fun_prop)
  intro θ
  simp

/-- The totalized real density is continuous at every scale. -/
@[fun_prop]
theorem continuous_wrappedCauchyPDFReal (m : AddCircle (2 * π)) (γ : ℝ≥0) :
    Continuous (wrappedCauchyPDFReal m γ) := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · exact continuous_const.congr fun θ ↦ (wrappedCauchyPDFReal_zero_scale m θ).symm
  · exact continuous_wrappedCauchyPDFReal_of_pos m (pos_iff_ne_zero.mpr hγ)

/-- The extended wrapped Cauchy density is measurable at every scale. -/
@[fun_prop]
theorem measurable_wrappedCauchyPDF (m : AddCircle (2 * π)) (γ : ℝ≥0) :
    Measurable (wrappedCauchyPDF m γ) :=
  (continuous_wrappedCauchyPDFReal m γ).measurable.ennreal_ofReal

/-- The real wrapped Cauchy density is nonnegative. -/
theorem wrappedCauchyPDFReal_nonneg (m : AddCircle (2 * π)) (γ : ℝ≥0)
    (θ : AddCircle (2 * π)) : 0 ≤ wrappedCauchyPDFReal m γ θ := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  · rw [← poissonKernel_eq_wrappedCauchyPDFReal]
    apply poissonKernel_nonneg_on_sphere (R := (1 : ℝ))
      (by simpa using wrappedCauchy_pole_mem_ball m (pos_iff_ne_zero.mpr hγ))
    simp

/-- At positive scale the wrapped Cauchy density is strictly positive at every circle point. -/
theorem wrappedCauchyPDFReal_pos (m : AddCircle (2 * π)) {γ : ℝ≥0} (hγ : 0 < γ)
    (θ : AddCircle (2 * π)) : 0 < wrappedCauchyPDFReal m γ θ := by
  have hr : 0 < Real.exp (-(γ : ℝ)) := Real.exp_pos _
  have hr1 : Real.exp (-(γ : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (NNReal.coe_pos.mpr hγ))
  have hcos : Real.Angle.cos (θ - m) ≤ 1 := by
    exact (Real.Angle.cos_toReal (θ - m)).symm.le.trans (Real.cos_le_one _)
  have hsquare : 0 < (1 - Real.exp (-(γ : ℝ))) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr1)
  rw [wrappedCauchyPDFReal_apply]
  apply div_pos
  · nlinarith
  · nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hcos)]

/-- At positive scale the wrapped Cauchy real density integrates to one against normalized Haar
measure. -/
theorem integral_wrappedCauchyPDFReal (m : AddCircle (2 * π)) {γ : ℝ≥0} (hγ : 0 < γ) :
    ∫ θ, wrappedCauchyPDFReal m γ θ ∂AddCircle.haarAddCircle = 1 := by
  rw [AddCircle.integral_haarAddCircle_eq_circleAverage_arg]
  calc
    circleAverage (fun z ↦ wrappedCauchyPDFReal m γ (Complex.arg z)) 0 1 =
        circleAverage
          (poissonKernel 0 ((Real.exp (-(γ : ℝ)) : ℂ) *
            (AddCircle.toCircle m : ℂ))) 0 1 := by
      apply circleAverage_congr_sphere
      intro z hz
      dsimp only
      rw [← poissonKernel_eq_wrappedCauchyPDFReal,
        AddCircle.toCircle_arg_of_mem_sphere (by simpa only [abs_one] using hz)]
    _ = 1 := by
      apply circleAverage_poissonKernel (R := (1 : ℝ))
      simpa only [abs_one] using wrappedCauchy_pole_mem_ball m hγ

private theorem integral_wrappedCauchyPDFReal_smul_fourier_nat
    (m : AddCircle (2 * π)) {γ : ℝ≥0} (hγ : 0 < γ) (n : ℕ) :
    ∫ θ, wrappedCauchyPDFReal m γ θ • fourier (n : ℤ) θ
        ∂AddCircle.haarAddCircle =
      fourier (n : ℤ) m * (Real.exp (-(γ : ℝ)) : ℂ) ^ n := by
  rw [AddCircle.integral_haarAddCircle_eq_circleAverage_arg]
  calc
    circleAverage
        (fun z ↦ wrappedCauchyPDFReal m γ (Complex.arg z) •
          fourier (n : ℤ) (Complex.arg z : AddCircle (2 * π))) 0 1 =
      circleAverage
        (poissonKernel 0 ((Real.exp (-(γ : ℝ)) : ℂ) *
          (AddCircle.toCircle m : ℂ)) • fun z : ℂ ↦ z ^ n) 0 1 := by
      apply circleAverage_congr_sphere
      intro z hz
      have harg := AddCircle.toCircle_arg_of_mem_sphere (by simpa only [abs_one] using hz)
      dsimp only [Pi.smul_apply']
      rw [fourier_apply, AddCircle.toCircle_zsmul,
        Circle.coe_zpow, zpow_natCast, ← poissonKernel_eq_wrappedCauchyPDFReal, harg]
    _ = ((Real.exp (-(γ : ℝ)) : ℂ) *
          (AddCircle.toCircle m : ℂ)) ^ n := by
      apply (differentiable_id.pow n).diffContOnCl.circleAverage_poissonKernel_smul
      simpa only [abs_one] using wrappedCauchy_pole_mem_ball m hγ
    _ = fourier (n : ℤ) m * (Real.exp (-(γ : ℝ)) : ℂ) ^ n := by
      rw [mul_pow, mul_comm]
      congr 1
      rw [fourier_apply]
      exact congrArg Subtype.val (AddCircle.toCircle_zsmul (n := (n : ℤ)) (x := m)).symm

private theorem integral_wrappedCauchyPDFReal_smul_fourier
    (m : AddCircle (2 * π)) {γ : ℝ≥0} (hγ : 0 < γ) (n : ℤ) :
    ∫ θ, wrappedCauchyPDFReal m γ θ • fourier n θ ∂AddCircle.haarAddCircle =
      fourier n m * (Real.exp (-(γ : ℝ)) : ℂ) ^ n.natAbs := by
  cases n with
  | ofNat n => simpa using integral_wrappedCauchyPDFReal_smul_fourier_nat m hγ n
  | negSucc n =>
      have hpos := integral_wrappedCauchyPDFReal_smul_fourier_nat m hγ (n + 1)
      have hn : (.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) := by omega
      calc
        ∫ θ, wrappedCauchyPDFReal m γ θ • fourier (.negSucc n) θ
            ∂AddCircle.haarAddCircle =
            ∫ θ, starRingEnd ℂ
              (wrappedCauchyPDFReal m γ θ • fourier (n + 1 : ℕ) θ)
                ∂AddCircle.haarAddCircle := by
          apply integral_congr_ae
          filter_upwards with θ
          rw [hn, fourier_neg, Complex.real_smul, Complex.real_smul, map_mul,
            Complex.conj_ofReal]
        _ = starRingEnd ℂ
              (∫ θ, wrappedCauchyPDFReal m γ θ • fourier (n + 1 : ℕ) θ
                ∂AddCircle.haarAddCircle) := integral_conj
        _ = fourier (.negSucc n) m *
              (Real.exp (-(γ : ℝ)) : ℂ) ^ Int.natAbs (.negSucc n) := by
          rw [hpos, map_mul, map_pow]
          simp only [Int.natAbs_negSucc, conj_ofReal]
          rw [hn, fourier_neg]

/-- At positive scale the wrapped Cauchy law is normalized Haar measure weighted by its named
Poisson-kernel density. -/
theorem wrappedCauchyMeasure_eq_withDensity (m : AddCircle (2 * π)) {γ : ℝ≥0}
    (hγ : 0 < γ) :
    wrappedCauchyMeasure m γ = AddCircle.haarAddCircle.withDensity (wrappedCauchyPDF m γ) := by
  have hpdf : wrappedCauchyPDF m γ = fun θ ↦ ENNReal.ofReal (wrappedCauchyPDFReal m γ θ) :=
    funext (wrappedCauchyPDF_apply m γ)
  have hcont := continuous_wrappedCauchyPDFReal m γ
  have hnonneg : ∀ θ, 0 ≤ wrappedCauchyPDFReal m γ θ :=
    wrappedCauchyPDFReal_nonneg m γ
  have hint : Integrable (wrappedCauchyPDFReal m γ) AddCircle.haarAddCircle := by
    simpa only [integrableOn_univ] using hcont.continuousOn.integrableOn_compact'
      (μ := AddCircle.haarAddCircle) isCompact_univ MeasurableSet.univ
  have hν_univ :
      AddCircle.haarAddCircle.withDensity (wrappedCauchyPDF m γ) Set.univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hpdf,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnonneg),
      integral_wrappedCauchyPDFReal m hγ]
    simp
  have : IsProbabilityMeasure (AddCircle.haarAddCircle.withDensity (wrappedCauchyPDF m γ)) :=
    ⟨hν_univ⟩
  have hprob : (wrappedCauchyMeasure m γ).toProbabilityMeasure =
      (AddCircle.haarAddCircle.withDensity (wrappedCauchyPDF m γ)).toProbabilityMeasure := by
    apply ProbabilityMeasure.ext_of_forall_integral_fourier_eq
    intro n
    rw [Measure.coe_toProbabilityMeasure, Measure.coe_toProbabilityMeasure,
      integral_fourier_wrappedCauchyMeasure, hpdf]
    rw [Probability.integral_withDensity_ofReal
      hcont.measurable.aemeasurable (ae_of_all _ hnonneg)]
    rw [integral_wrappedCauchyPDFReal_smul_fourier m hγ n]
    congr 1
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    rw [mul_comm, Nat.cast_natAbs, Int.cast_abs]
    ring
  exact congrArg ProbabilityMeasure.toMeasure hprob

/-- The Radon–Nikodym derivative of a positive-scale wrapped Cauchy law relative to normalized
Haar measure is its named density. -/
theorem rnDeriv_wrappedCauchyMeasure (m : AddCircle (2 * π)) {γ : ℝ≥0} (hγ : 0 < γ) :
    (wrappedCauchyMeasure m γ).rnDeriv AddCircle.haarAddCircle =ᵐ[AddCircle.haarAddCircle]
      wrappedCauchyPDF m γ := by
  rw [wrappedCauchyMeasure_eq_withDensity m hγ]
  exact Measure.rnDeriv_withDensity AddCircle.haarAddCircle
    (measurable_wrappedCauchyPDF m γ)

/-- A random angle with a positive-scale wrapped Cauchy law has a density relative to normalized
Haar measure. -/
theorem hasPDF_of_hasLaw_wrappedCauchyMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → AddCircle (2 * π)} {m : AddCircle (2 * π)} {γ : ℝ≥0}
    (hX : HasLaw X (wrappedCauchyMeasure m γ) P) (hγ : 0 < γ) :
    HasPDF X P AddCircle.haarAddCircle := by
  rw [wrappedCauchyMeasure_eq_withDensity m hγ] at hX
  exact hasPDF_of_hasLaw_withDensity (measurable_wrappedCauchyPDF m γ).aemeasurable hX

/-- The density of a random angle with a positive-scale wrapped Cauchy law agrees almost
everywhere with the named wrapped Cauchy density. -/
theorem pdf_eq_wrappedCauchyPDF_of_hasLaw_wrappedCauchyMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → AddCircle (2 * π)}
    {m : AddCircle (2 * π)} {γ : ℝ≥0}
    (hX : HasLaw X (wrappedCauchyMeasure m γ) P) (hγ : 0 < γ) :
    pdf X P AddCircle.haarAddCircle =ᵐ[AddCircle.haarAddCircle] wrappedCauchyPDF m γ := by
  rw [wrappedCauchyMeasure_eq_withDensity m hγ] at hX
  exact pdf_eq_of_hasLaw_withDensity (measurable_wrappedCauchyPDF m γ).aemeasurable hX

end TauCeti.Probability
