/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.WrappedCauchy.Density
public import TauCeti.Probability.Quantile
public import TauCeti.Probability.Distributions.Dirac
import TauCeti.MeasureTheory.Measure.AddCircle

/-!
# The wrapped Cauchy law in the fixed angle chart

`wrappedCauchyAngleMeasure` reads a wrapped Cauchy circle point in `[-π, π)`. At positive
scale its real density is the Haar Poisson kernel divided by `2π`. Its cdf is the integral
of that density from `-π`, with zero and one extensions outside the chart. Interior quantiles
are the unique roots of this integral, vary continuously and strictly increasingly with the
probability level, and tend to the chart endpoints.

At scale zero the angle law is the Dirac mass at the chosen representative of the location.
The location parameter remains a circle point, so the formulas are independent of its real
representative. The cdf uses the fixed chart rather than a chart centered at the location.

The chart transport follows `TauCeti.Probability.vonMisesAngleMeasure_eq_withDensity` in
`TauCeti.Probability.Distributions.VonMises.Angle`, using the shared Haar chart transport and
cdf/quantile APIs directly.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), section 3.5.7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- Positivity of the period used by the fixed wrapped Cauchy angle chart. -/
local instance wrappedCauchyAnglePeriodPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {m : AddCircle (2 * π)} {γ : ℝ≥0} {x u : ℝ}

/-- The real angle of a wrapped Cauchy point, chosen in `[-π, π)`. Zero scale gives the Dirac mass
at the chosen representative of the location. -/
def wrappedCauchyAngleMeasure (m : AddCircle (2 * π)) (γ : ℝ≥0) : Measure ℝ :=
  (wrappedCauchyMeasure m γ).map (fun θ ↦ (AddCircle.equivIco (2 * π) (-π) θ : ℝ))

/-- The angle law is the pushforward under the representative in `[-π, π)`. -/
theorem wrappedCauchyAngleMeasure_def (m : AddCircle (2 * π)) (γ : ℝ≥0) :
    wrappedCauchyAngleMeasure m γ =
      (wrappedCauchyMeasure m γ).map (fun θ ↦ (AddCircle.equivIco (2 * π) (-π) θ : ℝ)) := by
  rw [wrappedCauchyAngleMeasure]

/-- Zero scale gives the Dirac mass at the location's representative in `[-π, π)`. -/
@[simp]
theorem wrappedCauchyAngleMeasure_zero_scale (m : AddCircle (2 * π)) :
    wrappedCauchyAngleMeasure m 0 =
      Measure.dirac (AddCircle.equivIco (2 * π) (-π) m : ℝ) := by
  rw [wrappedCauchyAngleMeasure_def, wrappedCauchyMeasure_zero_scale, Measure.map_dirac]

/-- The fixed-chart angle law is a probability measure at every scale, including zero. -/
instance isProbabilityMeasure_wrappedCauchyAngleMeasure (m : AddCircle (2 * π)) (γ : ℝ≥0) :
    IsProbabilityMeasure (wrappedCauchyAngleMeasure m γ) := by
  rw [wrappedCauchyAngleMeasure_def]
  infer_instance

/-- The angle density is the lifted Haar density divided by `2π`, restricted to the
fixed chart. -/
theorem wrappedCauchyAngleMeasure_eq_withDensity (hγ : 0 < γ) :
    wrappedCauchyAngleMeasure m γ = (volume.restrict (Ico (-π) π)).withDensity
      (fun t : ℝ ↦ ENNReal.ofReal (wrappedCauchyPDFReal m γ t / (2 * π))) := by
  rw [wrappedCauchyAngleMeasure_def, wrappedCauchyMeasure_eq_withDensity m hγ,
    AddCircle.map_coe_equivIco_withDensity_haarAddCircle (-π) (measurable_wrappedCauchyPDF m γ)]
  have hπ : -π + 2 * π = π := by ring
  rw [hπ]
  congr 1
  funext t
  simp only [wrappedCauchyPDF_apply]
  rw [ENNReal.ofReal_div_of_pos two_pi_pos, div_eq_mul_inv, mul_comm]

/-- Every chosen angle lies in the half-open chart, including at the seam. -/
theorem ae_mem_Ico_wrappedCauchyAngleMeasure (m : AddCircle (2 * π)) (γ : ℝ≥0) :
    ∀ᵐ t ∂wrappedCauchyAngleMeasure m γ, t ∈ Ico (-π) π := by
  rw [wrappedCauchyAngleMeasure_def]
  have hm : Measurable (fun θ : AddCircle (2 * π) ↦
      (AddCircle.equivIco (2 * π) (-π) θ : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (2 * π) (-π)).measurable
  apply (ae_map_iff hm.aemeasurable measurableSet_Ico).2
  exact ae_of_all _ fun θ ↦ by
    have hπ : -π + 2 * π = π := by ring
    simpa only [mem_Ico, hπ] using (AddCircle.equivIco (2 * π) (-π) θ).property

/-- At positive scale the angle law has no atoms. -/
theorem nullSingletonClass_wrappedCauchyAngleMeasure (hγ : 0 < γ) :
    NullSingletonClass (wrappedCauchyAngleMeasure m γ) := by
  rw [wrappedCauchyAngleMeasure_eq_withDensity hγ]
  infer_instance

/-- The angle cdf is continuous. -/
theorem continuous_cdf_wrappedCauchyAngleMeasure (m : AddCircle (2 * π)) {γ : ℝ≥0} (hγ : 0 < γ) :
    Continuous (cdf (wrappedCauchyAngleMeasure m γ)) := by
  have := nullSingletonClass_wrappedCauchyAngleMeasure (m := m) hγ
  exact Measure.continuous_cdf_of_noAtoms _

/-- The topological support of the angle law is the closed chart interval. Both
endpoints belong to the support although the chosen representatives exclude `π`. -/
@[simp]
theorem support_wrappedCauchyAngleMeasure (hγ : 0 < γ) :
    (wrappedCauchyAngleMeasure m γ).support = Icc (-π) π := by
  rw [wrappedCauchyAngleMeasure_eq_withDensity hγ, ← withDensity_indicator measurableSet_Ico]
  have hf : Measurable fun t : ℝ ↦ ENNReal.ofReal (wrappedCauchyPDFReal m γ t / (2 * π)) :=
    ((continuous_wrappedCauchyPDFReal m γ).comp (AddCircle.continuous_mk' _)).measurable.div_const
      _ |>.ennreal_ofReal
  have hpos (t : ℝ) : 0 < ENNReal.ofReal (wrappedCauchyPDFReal m γ t / (2 * π)) :=
    ENNReal.ofReal_pos.mpr (div_pos (wrappedCauchyPDFReal_pos _ hγ _) two_pi_pos)
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
theorem cdf_wrappedCauchyAngleMeasure_eq_integral (hγ : 0 < γ) (hx : x ∈ Icc (-π) π) :
    cdf (wrappedCauchyAngleMeasure m γ) x =
      (∫ t in (-π)..x, wrappedCauchyPDFReal m γ t) / (2 * π) := by
  have hf : Continuous fun t : ℝ ↦ wrappedCauchyPDFReal m γ t / (2 * π) :=
    ((continuous_wrappedCauchyPDFReal m γ).comp (AddCircle.continuous_mk' _)).div_const _
  rw [cdf_eq_real, wrappedCauchyAngleMeasure_eq_withDensity hγ,
    Measure.restrict_congr_set Ico_ae_eq_Ioc,
    measureReal_withDensity_ofReal
      (ae_of_all _ fun t ↦ (div_pos (wrappedCauchyPDFReal_pos _ hγ _) two_pi_pos).le)
      measurableSet_Iic ((hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrableOn),
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le hx.2,
    ← intervalIntegral.integral_of_le hx.1, intervalIntegral.integral_div]

/-- The angle cdf vanishes at and below the lower endpoint of the fixed chart. -/
@[simp]
theorem cdf_wrappedCauchyAngleMeasure_of_le (hγ : 0 < γ) (hx : x ≤ -π) :
    cdf (wrappedCauchyAngleMeasure m γ) x = 0 := by
  have hzero : cdf (wrappedCauchyAngleMeasure m γ) (-π) = 0 := by
    rw [cdf_wrappedCauchyAngleMeasure_eq_integral hγ ⟨le_rfl, (neg_lt_self pi_pos).le⟩]
    simp
  exact le_antisymm (hzero ▸ monotone_cdf _ hx) (cdf_nonneg _ _)

/-- The angle cdf is one at and above the upper endpoint of the fixed chart. -/
@[simp]
theorem cdf_wrappedCauchyAngleMeasure_of_ge (hx : π ≤ x) :
    cdf (wrappedCauchyAngleMeasure m γ) x = 1 := by
  have heq : Iic x =ᵐ[wrappedCauchyAngleMeasure m γ] univ :=
    Filter.eventuallyEqSet_univ.2
      ((ae_mem_Ico_wrappedCauchyAngleMeasure m γ).mono fun _ ht ↦ ht.2.le.trans hx)
  rw [cdf_eq_real, measureReal_congr heq, probReal_univ]

/-- The angle cdf increases strictly throughout the closed chart interval. -/
theorem strictMonoOn_cdf_wrappedCauchyAngleMeasure (hγ : 0 < γ) :
    StrictMonoOn (cdf (wrappedCauchyAngleMeasure m γ)) (Icc (-π) π) :=
  Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Icc
    (by rw [support_wrappedCauchyAngleMeasure hγ])

/-- The angle cdf is positive exactly above the lower endpoint. -/
@[simp]
theorem cdf_wrappedCauchyAngleMeasure_pos_iff (hγ : 0 < γ) :
    0 < cdf (wrappedCauchyAngleMeasure m γ) x ↔ -π < x := by
  constructor
  · contrapose!
    intro hx
    simp [cdf_wrappedCauchyAngleMeasure_of_le hγ hx]
  · intro hx
    by_cases hπx : π ≤ x
    · simp [cdf_wrappedCauchyAngleMeasure_of_ge hπx]
    · exact (cdf_nonneg _ (-π)).trans_lt
        (strictMonoOn_cdf_wrappedCauchyAngleMeasure hγ
          ⟨le_rfl, (neg_lt_self pi_pos).le⟩ ⟨hx.le, (not_le.mp hπx).le⟩ hx)

/-- The angle cdf is less than one exactly below the upper endpoint. -/
@[simp]
theorem cdf_wrappedCauchyAngleMeasure_lt_one_iff (hγ : 0 < γ) :
    cdf (wrappedCauchyAngleMeasure m γ) x < 1 ↔ x < π := by
  constructor
  · contrapose!
    intro hx
    simp [cdf_wrappedCauchyAngleMeasure_of_ge hx]
  · intro hx
    by_cases hxπ : x ≤ -π
    · simp [cdf_wrappedCauchyAngleMeasure_of_le hγ hxπ]
    · exact (strictMonoOn_cdf_wrappedCauchyAngleMeasure hγ
        ⟨(not_le.mp hxπ).le, hx.le⟩ ⟨(neg_lt_self pi_pos).le, le_rfl⟩ hx).trans_le
        (cdf_le_one _ π)

/-- Interior angle quantiles lie strictly between the chart endpoints. -/
theorem quantile_wrappedCauchyAngleMeasure_mem_Ioo (hγ : 0 < γ) (hu : u ∈ Ioo 0 1) :
    (wrappedCauchyAngleMeasure m γ).quantile u ∈ Ioo (-π) π := by
  have hroot := Measure.cdf_quantile _ (continuous_cdf_wrappedCauchyAngleMeasure m hγ) hu.1 hu.2
  exact ⟨(cdf_wrappedCauchyAngleMeasure_pos_iff hγ).1 (hroot.symm ▸ hu.1),
    (cdf_wrappedCauchyAngleMeasure_lt_one_iff hγ).1 (hroot.symm ▸ hu.2)⟩

/-- The angle quantile is exactly the unique interior root of the normalized density
integral, at every interior probability level. -/
theorem quantile_wrappedCauchyAngleMeasure_eq_iff (hγ : 0 < γ) (hu : u ∈ Ioo 0 1) :
    (wrappedCauchyAngleMeasure m γ).quantile u = x ↔
      x ∈ Ioo (-π) π ∧ (∫ t in (-π)..x, wrappedCauchyPDFReal m γ t) / (2 * π) = u := by
  have hq := quantile_wrappedCauchyAngleMeasure_mem_Ioo (m := m) hγ hu
  have hroot := Measure.cdf_quantile _ (continuous_cdf_wrappedCauchyAngleMeasure m hγ) hu.1 hu.2
  constructor
  · rintro rfl
    exact ⟨hq,
      (cdf_wrappedCauchyAngleMeasure_eq_integral hγ (Ioo_subset_Icc_self hq)).symm.trans hroot⟩
  · rintro ⟨hx, hxu⟩
    exact (strictMonoOn_cdf_wrappedCauchyAngleMeasure hγ).injOn (Ioo_subset_Icc_self hq)
      (Ioo_subset_Icc_self hx) (hroot.trans
        ((cdf_wrappedCauchyAngleMeasure_eq_integral hγ (Ioo_subset_Icc_self hx)).trans hxu).symm)

/-- Angle quantiles increase strictly at interior probability levels. -/
theorem strictMonoOn_quantile_wrappedCauchyAngleMeasure (hγ : 0 < γ) :
    StrictMonoOn (wrappedCauchyAngleMeasure m γ).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_wrappedCauchyAngleMeasure m hγ)

/-- Angle quantiles are continuous at interior probability levels. -/
theorem continuousOn_quantile_wrappedCauchyAngleMeasure (hγ : 0 < γ) :
    ContinuousOn (wrappedCauchyAngleMeasure m γ).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Icc
    (strictMonoOn_cdf_wrappedCauchyAngleMeasure hγ)
    (fun _ hu ↦ Ioo_subset_Icc_self (quantile_wrappedCauchyAngleMeasure_mem_Ioo hγ hu))

/-- Angle quantiles tend to `-π` as the probability level decreases to zero. -/
theorem tendsto_quantile_wrappedCauchyAngleMeasure_nhdsGT_zero (hγ : 0 < γ) :
    Tendsto (wrappedCauchyAngleMeasure m γ).quantile (𝓝[>] 0) (𝓝 (-π)) := by
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos _
    ((ae_mem_Ico_wrappedCauchyAngleMeasure m γ).mono fun _ ht ↦ ht.1)
    (fun _ hx ↦ (cdf_wrappedCauchyAngleMeasure_pos_iff hγ).2 hx)

/-- Angle quantiles tend to `π` as the probability level increases to one. -/
theorem tendsto_quantile_wrappedCauchyAngleMeasure_nhdsLT_one (hγ : 0 < γ) :
    Tendsto (wrappedCauchyAngleMeasure m γ).quantile (𝓝[<] 1) (𝓝 π) := by
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one _
    ((ae_mem_Ico_wrappedCauchyAngleMeasure m γ).mono fun _ ht ↦ ht.2.le)
    (fun _ hx ↦ (cdf_wrappedCauchyAngleMeasure_lt_one_iff hγ).2 hx)

/-- The totalized fixed-chart angle family is jointly Giry measurable. -/
@[fun_prop]
theorem measurable_wrappedCauchyAngleMeasure :
    Measurable fun p : AddCircle (2 * π) × ℝ≥0 ↦ wrappedCauchyAngleMeasure p.1 p.2 := by
  simp only [wrappedCauchyAngleMeasure_def]
  exact (Measure.measurable_map _ (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (2 * π) (-π)).measurable)).comp measurable_wrappedCauchyMeasure

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

attribute [local instance] wrappedCauchyAnglePeriodPos

/-- Reading a wrapped Cauchy random circle point in `[-π, π)` gives the fixed-chart angle law. -/
theorem HasLaw.angle_wrappedCauchyMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → AddCircle (2 * π)} {m : AddCircle (2 * π)} {γ : ℝ≥0}
    (hX : HasLaw X (wrappedCauchyMeasure m γ) P) :
    HasLaw (fun ω ↦ (AddCircle.equivIco (2 * π) (-π) (X ω) : ℝ))
      (wrappedCauchyAngleMeasure m γ) P := by
  rw [wrappedCauchyAngleMeasure_def]
  exact (hasLaw_map (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (2 * π) (-π)).measurable).aemeasurable).comp hX

end ProbabilityTheory
