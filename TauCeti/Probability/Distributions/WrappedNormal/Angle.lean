/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.WrappedNormal.Density
public import TauCeti.Probability.Quantile
import TauCeti.Probability.Distributions.Gaussian.Periodization
import TauCeti.MeasureTheory.Measure.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The wrapped normal law in the fixed angle chart

`wrappedNormalAngleMeasure` reads a wrapped normal circle point in `[-π, π)`. At positive
variance its real density is the periodized Gaussian density. Its cdf is the integral
of that density from `-π`, with zero and one extensions outside the chart. Interior quantiles
are the unique roots of this integral, vary continuously and strictly increasingly with the
probability level, and tend to the chart endpoints.

At variance zero the angle law is the Dirac mass at the chosen representative of the location.
The location parameter remains a circle point, so the formulas are independent of its real
representative. The cdf uses the fixed chart rather than a chart centered at the location.

The fixed-chart interface follows
`TauCeti.Probability.wrappedCauchyAngleMeasure_eq_withDensity` and its cdf/quantile theory in
`TauCeti.Probability.Distributions.WrappedCauchy.Angle`. The proofs use the shared Haar chart
transport and measure-level cdf/quantile APIs. The cdf also equals the absolutely convergent
sum of Gaussian probabilities of the translated intervals.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), section 3.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- Positivity of the period used by the fixed wrapped normal angle chart. -/
local instance wrappedNormalAnglePeriodPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {m : AddCircle (2 * π)} {v : ℝ≥0} {x u : ℝ}

/-- The real angle of a wrapped normal point, chosen in `[-π, π)`. Zero variance gives the
Dirac mass at the chosen representative of the location. -/
def wrappedNormalAngleMeasure (m : AddCircle (2 * π)) (v : ℝ≥0) : Measure ℝ :=
  (wrappedNormalMeasure m v).map (fun θ ↦ (AddCircle.equivIco (2 * π) (-π) θ : ℝ))

/-- The angle law is the pushforward under the representative in `[-π, π)`. -/
theorem wrappedNormalAngleMeasure_def (m : AddCircle (2 * π)) (v : ℝ≥0) :
    wrappedNormalAngleMeasure m v =
      (wrappedNormalMeasure m v).map (fun θ ↦ (AddCircle.equivIco (2 * π) (-π) θ : ℝ)) := by
  rw [wrappedNormalAngleMeasure]

/-- Zero variance gives the Dirac mass at the location's representative in `[-π, π)`. -/
@[simp]
theorem wrappedNormalAngleMeasure_zero_var (m : AddCircle (2 * π)) :
    wrappedNormalAngleMeasure m 0 =
      Measure.dirac (AddCircle.equivIco (2 * π) (-π) m : ℝ) := by
  rw [wrappedNormalAngleMeasure_def, wrappedNormalMeasure_zero_var, Measure.map_dirac]

/-- The fixed-chart angle law is a probability measure at every variance, including zero. -/
instance isProbabilityMeasure_wrappedNormalAngleMeasure (m : AddCircle (2 * π)) (v : ℝ≥0) :
    IsProbabilityMeasure (wrappedNormalAngleMeasure m v) := by
  rw [wrappedNormalAngleMeasure_def]
  infer_instance

/-- The angle density is the lifted Haar density divided by `2π`, restricted to the
fixed chart. -/
theorem wrappedNormalAngleMeasure_eq_withDensity (hv : v ≠ 0) :
    wrappedNormalAngleMeasure m v = (volume.restrict (Ico (-π) π)).withDensity
      (fun t : ℝ ↦ ENNReal.ofReal (wrappedNormalPDFReal m v t / (2 * π))) := by
  rw [wrappedNormalAngleMeasure_def, wrappedNormalMeasure_eq_withDensity m hv,
    AddCircle.map_coe_equivIco_withDensity_haarAddCircle (-π) (measurable_wrappedNormalPDF m v)]
  have hπ : -π + 2 * π = π := by ring
  rw [hπ]
  congr 1
  funext t
  simp only [wrappedNormalPDF_apply]
  rw [ENNReal.ofReal_div_of_pos two_pi_pos, div_eq_mul_inv, mul_comm]

/-- Every chosen angle lies in the half-open chart, including at the seam. -/
theorem ae_mem_Ico_wrappedNormalAngleMeasure (m : AddCircle (2 * π)) (v : ℝ≥0) :
    ∀ᵐ t ∂wrappedNormalAngleMeasure m v, t ∈ Ico (-π) π := by
  rw [wrappedNormalAngleMeasure_def]
  have hm : Measurable (fun θ : AddCircle (2 * π) ↦
      (AddCircle.equivIco (2 * π) (-π) θ : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (2 * π) (-π)).measurable
  apply (ae_map_iff hm.aemeasurable measurableSet_Ico).2
  exact ae_of_all _ fun θ ↦ by
    have hπ : -π + 2 * π = π := by ring
    simpa only [mem_Ico, hπ] using (AddCircle.equivIco (2 * π) (-π) θ).property

/-- At positive variance the angle law has no atoms. -/
theorem nullSingletonClass_wrappedNormalAngleMeasure (hv : v ≠ 0) :
    NullSingletonClass (wrappedNormalAngleMeasure m v) := by
  rw [wrappedNormalAngleMeasure_eq_withDensity hv]
  infer_instance

/-- The angle cdf is continuous. -/
theorem continuous_cdf_wrappedNormalAngleMeasure (m : AddCircle (2 * π)) {v : ℝ≥0} (hv : v ≠ 0) :
    Continuous (cdf (wrappedNormalAngleMeasure m v)) := by
  have := nullSingletonClass_wrappedNormalAngleMeasure (m := m) hv
  exact Measure.continuous_cdf_of_noAtoms _

/-- The topological support of the angle law is the closed chart interval. Both
endpoints belong to the support although the chosen representatives exclude `π`. -/
@[simp]
theorem support_wrappedNormalAngleMeasure (hv : v ≠ 0) :
    (wrappedNormalAngleMeasure m v).support = Icc (-π) π := by
  rw [wrappedNormalAngleMeasure_eq_withDensity hv, ← withDensity_indicator measurableSet_Ico]
  have hf : Measurable fun t : ℝ ↦ ENNReal.ofReal (wrappedNormalPDFReal m v t / (2 * π)) :=
    ((continuous_wrappedNormalPDFReal m v).comp (AddCircle.continuous_mk' _)).measurable.div_const
      _ |>.ennreal_ofReal
  have hpos (t : ℝ) : 0 < ENNReal.ofReal (wrappedNormalPDFReal m v t / (2 * π)) :=
    ENNReal.ofReal_pos.mpr (div_pos (wrappedNormalPDFReal_pos _ hv _) two_pi_pos)
  have hclosure : closure (Ioo (-π) π) = Icc (-π) π :=
    closure_Ioo (neg_lt_self pi_pos).ne
  rw [← hclosure]
  apply Measure.support_withDensity_eq_closure_of_subset (hf.indicator measurableSet_Ico)
    isOpen_Ioo
  · intro t ht
    simpa only [Function.mem_support, indicator_of_mem (Ioo_subset_Ico_self ht)] using
      (hpos t).ne'
  · intro t ht
    rw [hclosure]
    exact Ico_subset_Icc_self (Set.support_indicator_subset ht)

/-- On the closed chart interval the cdf is the integral of the angle density from `-π`. -/
theorem cdf_wrappedNormalAngleMeasure_eq_integral (hv : v ≠ 0) (hx : x ∈ Icc (-π) π) :
    cdf (wrappedNormalAngleMeasure m v) x =
      (∫ t in (-π)..x, wrappedNormalPDFReal m v t) / (2 * π) := by
  have hf : Continuous fun t : ℝ ↦ wrappedNormalPDFReal m v t / (2 * π) :=
    ((continuous_wrappedNormalPDFReal m v).comp (AddCircle.continuous_mk' _)).div_const _
  rw [cdf_eq_real, wrappedNormalAngleMeasure_eq_withDensity hv,
    Measure.restrict_congr_set Ico_ae_eq_Ioc,
    measureReal_withDensity_ofReal
      (ae_of_all _ fun t ↦ (div_pos (wrappedNormalPDFReal_pos _ hv _) two_pi_pos).le)
      measurableSet_Iic ((hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrableOn),
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le hx.2,
    ← intervalIntegral.integral_of_le hx.1, intervalIntegral.integral_div]

/-- On the closed chart, the wrapped normal cdf is the convergent sum of the Gaussian
probabilities of all period-translates of `(-π, x]`. The sum is over integers, so convergence
is unconditional (and hence absolute). -/
theorem hasSum_gaussianReal_wrappedNormalAngleMeasure (a : ℝ) (hv : v ≠ 0)
    (hx : x ∈ Icc (-π) π) :
    HasSum (fun k : ℤ ↦ (gaussianReal a v).real
      (Ioc (-π + 2 * π * k) (x + 2 * π * k)))
      (cdf (wrappedNormalAngleMeasure a v) x) := by
  have hsum (t : ℝ) :
      HasSum (fun k : ℤ ↦ gaussianPDFReal a v (t + 2 * π * k))
        (wrappedNormalPDFReal a v t / (2 * π)) := by
    rw [wrappedNormalPDFReal_coe, mul_div_cancel_left₀ _ two_pi_pos.ne']
    exact ((summable_gaussianPDFReal_add_zsmul a v two_pi_pos.ne' t).congr
      fun k ↦ by rw [zsmul_eq_mul, mul_comm (k : ℝ)]).hasSum
  have hint : IntervalIntegrable (fun t : ℝ ↦ wrappedNormalPDFReal a v t / (2 * π))
      volume (-π) x :=
    (((continuous_wrappedNormalPDFReal a v).comp
      (AddCircle.continuous_mk' _)).div_const _).intervalIntegrable _ _
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k : ℤ ↦ fun t : ℝ ↦ gaussianPDFReal a v (t + 2 * π * k))
    (fun k ↦ ((measurable_gaussianPDFReal a v).comp (by fun_prop)).aestronglyMeasurable)
    (fun k ↦ ae_of_all _ fun t _ ↦ (Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)).le)
    (ae_of_all _ fun t _ ↦ (hsum t).summable)
    (hint.congr (by intro t _; exact (hsum t).tsum_eq.symm))
    (ae_of_all _ fun t _ ↦ hsum t)
  rw [intervalIntegral.integral_div, ← cdf_wrappedNormalAngleMeasure_eq_integral hv hx] at h
  refine h.congr_fun fun k ↦ ?_
  simp only [Function.comp_apply]
  rw [intervalIntegral.integral_comp_add_right,
    intervalIntegral.integral_of_le (by linarith [hx.1]),
    measureReal_def, gaussianReal_apply_eq_integral a hv,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg _ _))]

/-- The fixed-chart cdf is the sum of Gaussian interval probabilities, with the location
specified by any real representative. -/
theorem cdf_wrappedNormalAngleMeasure_eq_tsum (a : ℝ) (hv : v ≠ 0)
    (hx : x ∈ Icc (-π) π) :
    cdf (wrappedNormalAngleMeasure a v) x = ∑' k : ℤ, (gaussianReal a v).real
      (Ioc (-π + 2 * π * k) (x + 2 * π * k)) :=
  (hasSum_gaussianReal_wrappedNormalAngleMeasure a hv hx).tsum_eq.symm

/-- The angle cdf vanishes at and below the lower endpoint of the fixed chart. -/
@[simp]
theorem cdf_wrappedNormalAngleMeasure_of_le (hv : v ≠ 0) (hx : x ≤ -π) :
    cdf (wrappedNormalAngleMeasure m v) x = 0 := by
  have hzero : cdf (wrappedNormalAngleMeasure m v) (-π) = 0 := by
    rw [cdf_wrappedNormalAngleMeasure_eq_integral hv ⟨le_rfl, (neg_lt_self pi_pos).le⟩]
    simp
  exact le_antisymm (hzero ▸ monotone_cdf _ hx) (cdf_nonneg _ _)

/-- The angle cdf is one at and above the upper endpoint of the fixed chart. -/
@[simp]
theorem cdf_wrappedNormalAngleMeasure_of_ge (hx : π ≤ x) :
    cdf (wrappedNormalAngleMeasure m v) x = 1 := by
  have heq : Iic x =ᵐ[wrappedNormalAngleMeasure m v] univ :=
    Filter.eventuallyEqSet_univ.2
      ((ae_mem_Ico_wrappedNormalAngleMeasure m v).mono fun _ ht ↦ ht.2.le.trans hx)
  rw [cdf_eq_real, measureReal_congr heq, probReal_univ]

/-- The angle cdf increases strictly throughout the closed chart interval. -/
theorem strictMonoOn_cdf_wrappedNormalAngleMeasure (hv : v ≠ 0) :
    StrictMonoOn (cdf (wrappedNormalAngleMeasure m v)) (Icc (-π) π) :=
  Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Icc
    (by rw [support_wrappedNormalAngleMeasure hv])

/-- The angle cdf is positive exactly above the lower endpoint. -/
@[simp]
theorem cdf_wrappedNormalAngleMeasure_pos_iff (hv : v ≠ 0) :
    0 < cdf (wrappedNormalAngleMeasure m v) x ↔ -π < x := by
  constructor
  · contrapose!
    intro hx
    simp [cdf_wrappedNormalAngleMeasure_of_le hv hx]
  · intro hx
    by_cases hπx : π ≤ x
    · simp [cdf_wrappedNormalAngleMeasure_of_ge hπx]
    · exact (cdf_nonneg _ (-π)).trans_lt
        (strictMonoOn_cdf_wrappedNormalAngleMeasure hv
          ⟨le_rfl, (neg_lt_self pi_pos).le⟩ ⟨hx.le, (not_le.mp hπx).le⟩ hx)

/-- The angle cdf is less than one exactly below the upper endpoint. -/
@[simp]
theorem cdf_wrappedNormalAngleMeasure_lt_one_iff (hv : v ≠ 0) :
    cdf (wrappedNormalAngleMeasure m v) x < 1 ↔ x < π := by
  constructor
  · contrapose!
    intro hx
    simp [cdf_wrappedNormalAngleMeasure_of_ge hx]
  · intro hx
    by_cases hxπ : x ≤ -π
    · simp [cdf_wrappedNormalAngleMeasure_of_le hv hxπ]
    · exact (strictMonoOn_cdf_wrappedNormalAngleMeasure hv
        ⟨(not_le.mp hxπ).le, hx.le⟩ ⟨(neg_lt_self pi_pos).le, le_rfl⟩ hx).trans_le
        (cdf_le_one _ π)

/-- Interior angle quantiles lie strictly between the chart endpoints. -/
theorem quantile_wrappedNormalAngleMeasure_mem_Ioo (hv : v ≠ 0) (hu : u ∈ Ioo 0 1) :
    (wrappedNormalAngleMeasure m v).quantile u ∈ Ioo (-π) π := by
  have hroot := Measure.cdf_quantile _ (continuous_cdf_wrappedNormalAngleMeasure m hv) hu.1 hu.2
  exact ⟨(cdf_wrappedNormalAngleMeasure_pos_iff hv).1 (hroot.symm ▸ hu.1),
    (cdf_wrappedNormalAngleMeasure_lt_one_iff hv).1 (hroot.symm ▸ hu.2)⟩

/-- The angle quantile is exactly the unique interior root of the normalized density
integral, at every interior probability level. -/
theorem quantile_wrappedNormalAngleMeasure_eq_iff (hv : v ≠ 0) (hu : u ∈ Ioo 0 1) :
    (wrappedNormalAngleMeasure m v).quantile u = x ↔
      x ∈ Ioo (-π) π ∧ (∫ t in (-π)..x, wrappedNormalPDFReal m v t) / (2 * π) = u := by
  have hq := quantile_wrappedNormalAngleMeasure_mem_Ioo (m := m) hv hu
  have hroot := Measure.cdf_quantile _ (continuous_cdf_wrappedNormalAngleMeasure m hv) hu.1 hu.2
  constructor
  · rintro rfl
    exact ⟨hq,
      (cdf_wrappedNormalAngleMeasure_eq_integral hv (Ioo_subset_Icc_self hq)).symm.trans hroot⟩
  · rintro ⟨hx, hxu⟩
    exact (strictMonoOn_cdf_wrappedNormalAngleMeasure hv).injOn (Ioo_subset_Icc_self hq)
      (Ioo_subset_Icc_self hx) (hroot.trans
        ((cdf_wrappedNormalAngleMeasure_eq_integral hv (Ioo_subset_Icc_self hx)).trans hxu).symm)

/-- Angle quantiles increase strictly at interior probability levels. -/
theorem strictMonoOn_quantile_wrappedNormalAngleMeasure (hv : v ≠ 0) :
    StrictMonoOn (wrappedNormalAngleMeasure m v).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_wrappedNormalAngleMeasure m hv)

/-- Angle quantiles are continuous at interior probability levels. -/
theorem continuousOn_quantile_wrappedNormalAngleMeasure (hv : v ≠ 0) :
    ContinuousOn (wrappedNormalAngleMeasure m v).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Icc
    (strictMonoOn_cdf_wrappedNormalAngleMeasure hv)
    (fun _ hu ↦ Ioo_subset_Icc_self (quantile_wrappedNormalAngleMeasure_mem_Ioo hv hu))

/-- Angle quantiles tend to `-π` as the probability level decreases to zero. -/
theorem tendsto_quantile_wrappedNormalAngleMeasure_nhdsGT_zero (hv : v ≠ 0) :
    Tendsto (wrappedNormalAngleMeasure m v).quantile (𝓝[>] 0) (𝓝 (-π)) := by
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos _
    ((ae_mem_Ico_wrappedNormalAngleMeasure m v).mono fun _ ht ↦ ht.1)
    (fun _ hx ↦ (cdf_wrappedNormalAngleMeasure_pos_iff hv).2 hx)

/-- Angle quantiles tend to `π` as the probability level increases to one. -/
theorem tendsto_quantile_wrappedNormalAngleMeasure_nhdsLT_one (hv : v ≠ 0) :
    Tendsto (wrappedNormalAngleMeasure m v).quantile (𝓝[<] 1) (𝓝 π) := by
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one _
    ((ae_mem_Ico_wrappedNormalAngleMeasure m v).mono fun _ ht ↦ ht.2.le)
    (fun _ hx ↦ (cdf_wrappedNormalAngleMeasure_lt_one_iff hv).2 hx)

/-- The totalized fixed-chart angle family is jointly Giry measurable. -/
@[fun_prop]
theorem measurable_wrappedNormalAngleMeasure :
    Measurable fun p : AddCircle (2 * π) × ℝ≥0 ↦ wrappedNormalAngleMeasure p.1 p.2 := by
  simp only [wrappedNormalAngleMeasure_def]
  exact (Measure.measurable_map _ (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (2 * π) (-π)).measurable)).comp measurable_wrappedNormalMeasure

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

attribute [local instance] wrappedNormalAnglePeriodPos

/-- Reading a wrapped normal random circle point in `[-π, π)` gives the fixed-chart angle law. -/
theorem HasLaw.angle_wrappedNormalMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → AddCircle (2 * π)} {m : AddCircle (2 * π)} {v : ℝ≥0}
    (hX : HasLaw X (wrappedNormalMeasure m v) P) :
    HasLaw (fun ω ↦ (AddCircle.equivIco (2 * π) (-π) (X ω) : ℝ))
      (wrappedNormalAngleMeasure m v) P := by
  rw [wrappedNormalAngleMeasure_def]
  exact (hasLaw_map (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (2 * π) (-π)).measurable).aemeasurable).comp hX

end ProbabilityTheory
