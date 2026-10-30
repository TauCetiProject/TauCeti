/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.VonMises.Basic
public import TauCeti.Probability.Quantile
import TauCeti.MeasureTheory.Measure.AddCircle
import TauCeti.Probability.Density

/-!
# The von Mises law in the fixed angle chart

`vonMisesAngleMeasure` reads a von Mises circle point in `[-π, π)`. Its real density is
the Haar density divided by `2π`. The cdf integrates that density from `-π`, is zero
below the chart, and is one above it. The interior quantile is the unique root of this
integral, is continuous and strictly increasing, and tends to the two chart endpoints.

The location remains a circle point, so every formula is independent of its real
representative. The angle cdf and quantile use the fixed chart, rather than a chart
centered at the location.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), section 3.5.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal

namespace TauCeti.Probability

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {m : AddCircle (2 * π)} {κ x u : ℝ}

/-- The real angle of a von Mises point, chosen in `[-π, π)`. Negative concentration
gives the zero measure, as for the circle-valued law. -/
def vonMisesAngleMeasure (m : AddCircle (2 * π)) (κ : ℝ) : Measure ℝ :=
  (vonMisesMeasure m κ).map (fun θ ↦ (AddCircle.equivIco (2 * π) (-π) θ : ℝ))

/-- The angle law is the pushforward under the representative in `[-π, π)`. -/
theorem vonMisesAngleMeasure_def (m : AddCircle (2 * π)) (κ : ℝ) :
    vonMisesAngleMeasure m κ =
      (vonMisesMeasure m κ).map (fun θ ↦ (AddCircle.equivIco (2 * π) (-π) θ : ℝ)) := by
  rw [vonMisesAngleMeasure]

/-- Negative concentration gives the zero angle law. -/
@[simp]
theorem vonMisesAngleMeasure_of_neg (hκ : κ < 0) : vonMisesAngleMeasure m κ = 0 := by
  simp [vonMisesAngleMeasure_def, vonMisesMeasure_of_neg hκ]

/-- At valid concentrations the fixed-chart angle law is a probability measure. -/
theorem isProbabilityMeasure_vonMisesAngleMeasure (m : AddCircle (2 * π)) (hκ : 0 ≤ κ) :
    IsProbabilityMeasure (vonMisesAngleMeasure m κ) := by
  have := isProbabilityMeasure_vonMisesMeasure m hκ
  rw [vonMisesAngleMeasure_def]
  infer_instance

/-- The angle density is the lifted Haar density divided by `2π`, restricted to the
fixed chart. -/
theorem vonMisesAngleMeasure_eq_withDensity (hκ : 0 ≤ κ) :
    vonMisesAngleMeasure m κ = (volume.restrict (Ico (-π) π)).withDensity
      (fun t : ℝ ↦ ENNReal.ofReal (vonMisesPDFReal m κ t / (2 * π))) := by
  rw [vonMisesAngleMeasure_def, vonMisesMeasure_of_nonneg hκ,
    AddCircle.map_coe_equivIco_withDensity_haarAddCircle (-π) (measurable_vonMisesPDF m κ)]
  have hπ : -π + 2 * π = π := by ring
  rw [hπ]
  congr 1
  funext t
  simp only [vonMisesPDF_def]
  rw [ENNReal.ofReal_div_of_pos two_pi_pos, div_eq_mul_inv, mul_comm]

/-- Every chosen angle lies in the half-open chart, including at the seam. -/
theorem ae_mem_Ico_vonMisesAngleMeasure (m : AddCircle (2 * π)) (κ : ℝ) :
    ∀ᵐ t ∂vonMisesAngleMeasure m κ, t ∈ Ico (-π) π := by
  rw [vonMisesAngleMeasure_def]
  have hm : Measurable (fun θ : AddCircle (2 * π) ↦
      (AddCircle.equivIco (2 * π) (-π) θ : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (2 * π) (-π)).measurable
  apply (ae_map_iff hm.aemeasurable measurableSet_Ico).2
  exact ae_of_all _ fun θ ↦ by
    have hπ : -π + 2 * π = π := by ring
    simpa only [mem_Ico, hπ] using (AddCircle.equivIco (2 * π) (-π) θ).property

/-- The angle law has no atoms, for every concentration, including invalid ones. -/
instance nullSingletonClass_vonMisesAngleMeasure (m : AddCircle (2 * π)) (κ : ℝ) :
    NullSingletonClass (vonMisesAngleMeasure m κ) := by
  by_cases hκ : 0 ≤ κ
  · rw [vonMisesAngleMeasure_eq_withDensity hκ]
    infer_instance
  · rw [vonMisesAngleMeasure_of_neg (lt_of_not_ge hκ)]
    exact ⟨fun _ ↦ rfl⟩

/-- The angle cdf is continuous. -/
theorem continuous_cdf_vonMisesAngleMeasure (m : AddCircle (2 * π)) (hκ : 0 ≤ κ) :
    Continuous (cdf (vonMisesAngleMeasure m κ)) := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  exact Measure.continuous_cdf_of_noAtoms _

/-- The topological support of the angle law is the closed chart interval. Both
endpoints belong to the support although the chosen representatives exclude `π`. -/
@[simp]
theorem support_vonMisesAngleMeasure (hκ : 0 ≤ κ) :
    (vonMisesAngleMeasure m κ).support = Icc (-π) π := by
  rw [vonMisesAngleMeasure_eq_withDensity hκ, ← withDensity_indicator measurableSet_Ico]
  have hf : Measurable fun t : ℝ ↦ ENNReal.ofReal (vonMisesPDFReal m κ t / (2 * π)) :=
    ((continuous_vonMisesPDFReal m κ).comp (AddCircle.continuous_mk' _)).measurable.div_const
      _ |>.ennreal_ofReal
  have hpos (t : ℝ) : 0 < ENNReal.ofReal (vonMisesPDFReal m κ t / (2 * π)) :=
    ENNReal.ofReal_pos.mpr (div_pos (vonMisesPDFReal_pos _ _ _) two_pi_pos)
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
theorem cdf_vonMisesAngleMeasure_eq_integral (hκ : 0 ≤ κ) (hx : x ∈ Icc (-π) π) :
    cdf (vonMisesAngleMeasure m κ) x =
      (∫ t in (-π)..x, vonMisesPDFReal m κ t) / (2 * π) := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  have hf : Continuous fun t : ℝ ↦ vonMisesPDFReal m κ t / (2 * π) :=
    ((continuous_vonMisesPDFReal m κ).comp (AddCircle.continuous_mk' _)).div_const _
  rw [cdf_eq_real, vonMisesAngleMeasure_eq_withDensity hκ,
    Measure.restrict_congr_set Ico_ae_eq_Ioc,
    measureReal_withDensity_ofReal
      (ae_of_all _ fun t ↦ (div_pos (vonMisesPDFReal_pos _ _ _) two_pi_pos).le)
      measurableSet_Iic ((hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrableOn),
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le hx.2,
    ← intervalIntegral.integral_of_le hx.1, intervalIntegral.integral_div]

/-- The angle cdf vanishes at and below the lower endpoint of the fixed chart. -/
@[simp]
theorem cdf_vonMisesAngleMeasure_of_le (hκ : 0 ≤ κ) (hx : x ≤ -π) :
    cdf (vonMisesAngleMeasure m κ) x = 0 := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  have hzero : cdf (vonMisesAngleMeasure m κ) (-π) = 0 := by
    rw [cdf_vonMisesAngleMeasure_eq_integral hκ ⟨le_rfl, (neg_lt_self pi_pos).le⟩]
    simp
  exact le_antisymm (hzero ▸ monotone_cdf _ hx) (cdf_nonneg _ _)

/-- The angle cdf is one at and above the upper endpoint of the fixed chart. -/
@[simp]
theorem cdf_vonMisesAngleMeasure_of_ge (hκ : 0 ≤ κ) (hx : π ≤ x) :
    cdf (vonMisesAngleMeasure m κ) x = 1 := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  have heq : Iic x =ᵐ[vonMisesAngleMeasure m κ] univ :=
    Filter.eventuallyEqSet_univ.2
      ((ae_mem_Ico_vonMisesAngleMeasure m κ).mono fun _ ht ↦ ht.2.le.trans hx)
  rw [cdf_eq_real, measureReal_congr heq, probReal_univ]

/-- The angle cdf increases strictly throughout the closed chart interval. -/
theorem strictMonoOn_cdf_vonMisesAngleMeasure (hκ : 0 ≤ κ) :
    StrictMonoOn (cdf (vonMisesAngleMeasure m κ)) (Icc (-π) π) := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  exact Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Icc
    (by rw [support_vonMisesAngleMeasure hκ])

/-- The angle cdf is positive exactly above the lower endpoint. -/
@[simp]
theorem cdf_vonMisesAngleMeasure_pos_iff (hκ : 0 ≤ κ) :
    0 < cdf (vonMisesAngleMeasure m κ) x ↔ -π < x := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  constructor
  · contrapose!
    intro hx
    simp [cdf_vonMisesAngleMeasure_of_le hκ hx]
  · intro hx
    by_cases hπx : π ≤ x
    · simp [cdf_vonMisesAngleMeasure_of_ge hκ hπx]
    · exact (cdf_nonneg _ (-π)).trans_lt
        (strictMonoOn_cdf_vonMisesAngleMeasure hκ
          ⟨le_rfl, (neg_lt_self pi_pos).le⟩ ⟨hx.le, (not_le.mp hπx).le⟩ hx)

/-- The angle cdf is less than one exactly below the upper endpoint. -/
@[simp]
theorem cdf_vonMisesAngleMeasure_lt_one_iff (hκ : 0 ≤ κ) :
    cdf (vonMisesAngleMeasure m κ) x < 1 ↔ x < π := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  constructor
  · contrapose!
    intro hx
    simp [cdf_vonMisesAngleMeasure_of_ge hκ hx]
  · intro hx
    by_cases hxπ : x ≤ -π
    · simp [cdf_vonMisesAngleMeasure_of_le hκ hxπ]
    · exact (strictMonoOn_cdf_vonMisesAngleMeasure hκ
        ⟨(not_le.mp hxπ).le, hx.le⟩ ⟨(neg_lt_self pi_pos).le, le_rfl⟩ hx).trans_le
        (cdf_le_one _ π)

/-- Interior angle quantiles lie strictly between the chart endpoints. -/
theorem quantile_vonMisesAngleMeasure_mem_Ioo (hκ : 0 ≤ κ) (hu : u ∈ Ioo 0 1) :
    (vonMisesAngleMeasure m κ).quantile u ∈ Ioo (-π) π := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  have hroot := Measure.cdf_quantile _ (continuous_cdf_vonMisesAngleMeasure m hκ) hu.1 hu.2
  exact ⟨(cdf_vonMisesAngleMeasure_pos_iff hκ).1 (hroot.symm ▸ hu.1),
    (cdf_vonMisesAngleMeasure_lt_one_iff hκ).1 (hroot.symm ▸ hu.2)⟩

/-- The angle quantile is exactly the unique interior root of the normalized density
integral, at every interior probability level. -/
theorem quantile_vonMisesAngleMeasure_eq_iff (hκ : 0 ≤ κ) (hu : u ∈ Ioo 0 1) :
    (vonMisesAngleMeasure m κ).quantile u = x ↔
      x ∈ Ioo (-π) π ∧ (∫ t in (-π)..x, vonMisesPDFReal m κ t) / (2 * π) = u := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  have hq := quantile_vonMisesAngleMeasure_mem_Ioo (m := m) hκ hu
  have hroot := Measure.cdf_quantile _ (continuous_cdf_vonMisesAngleMeasure m hκ) hu.1 hu.2
  constructor
  · rintro rfl
    exact ⟨hq, (cdf_vonMisesAngleMeasure_eq_integral hκ (Ioo_subset_Icc_self hq)).symm.trans hroot⟩
  · rintro ⟨hx, hxu⟩
    exact (strictMonoOn_cdf_vonMisesAngleMeasure hκ).injOn (Ioo_subset_Icc_self hq)
      (Ioo_subset_Icc_self hx) (hroot.trans
        ((cdf_vonMisesAngleMeasure_eq_integral hκ (Ioo_subset_Icc_self hx)).trans hxu).symm)

/-- Angle quantiles increase strictly at interior probability levels. -/
theorem strictMonoOn_quantile_vonMisesAngleMeasure (hκ : 0 ≤ κ) :
    StrictMonoOn (vonMisesAngleMeasure m κ).quantile (Ioo 0 1) := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  exact Measure.strictMonoOn_quantile _ (continuous_cdf_vonMisesAngleMeasure m hκ)

/-- Angle quantiles are continuous at interior probability levels. -/
theorem continuousOn_quantile_vonMisesAngleMeasure (hκ : 0 ≤ κ) :
    ContinuousOn (vonMisesAngleMeasure m κ).quantile (Ioo 0 1) := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  exact Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Icc
    (strictMonoOn_cdf_vonMisesAngleMeasure hκ)
    (fun _ hu ↦ Ioo_subset_Icc_self (quantile_vonMisesAngleMeasure_mem_Ioo hκ hu))

/-- Angle quantiles tend to `-π` as the probability level decreases to zero. -/
theorem tendsto_quantile_vonMisesAngleMeasure_nhdsGT_zero (hκ : 0 ≤ κ) :
    Tendsto (vonMisesAngleMeasure m κ).quantile (𝓝[>] 0) (𝓝 (-π)) := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos _
    ((ae_mem_Ico_vonMisesAngleMeasure m κ).mono fun _ ht ↦ ht.1)
    (fun _ hx ↦ (cdf_vonMisesAngleMeasure_pos_iff hκ).2 hx)

/-- Angle quantiles tend to `π` as the probability level increases to one. -/
theorem tendsto_quantile_vonMisesAngleMeasure_nhdsLT_one (hκ : 0 ≤ κ) :
    Tendsto (vonMisesAngleMeasure m κ).quantile (𝓝[<] 1) (𝓝 π) := by
  have := isProbabilityMeasure_vonMisesAngleMeasure m hκ
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one _
    ((ae_mem_Ico_vonMisesAngleMeasure m κ).mono fun _ ht ↦ ht.2.le)
    (fun _ hx ↦ (cdf_vonMisesAngleMeasure_lt_one_iff hκ).2 hx)

/-- The totalized fixed-chart angle family is jointly Giry measurable. -/
@[fun_prop]
theorem measurable_vonMisesAngleMeasure :
    Measurable fun p : AddCircle (2 * π) × ℝ ↦ vonMisesAngleMeasure p.1 p.2 := by
  simp only [vonMisesAngleMeasure_def]
  exact (Measure.measurable_map _ (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (2 * π) (-π)).measurable)).comp measurable_vonMisesMeasure

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- Reading a von Mises random circle point in `[-π, π)` gives the fixed-chart angle law. -/
theorem HasLaw.angle_vonMisesMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → AddCircle (2 * π)} {m : AddCircle (2 * π)} {κ : ℝ}
    (hX : HasLaw X (vonMisesMeasure m κ) P) :
    HasLaw (fun ω ↦ (AddCircle.equivIco (2 * π) (-π) (X ω) : ℝ))
      (vonMisesAngleMeasure m κ) P := by
  rw [vonMisesAngleMeasure_def]
  exact (hasLaw_map (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (2 * π) (-π)).measurable).aemeasurable).comp hX

end ProbabilityTheory
