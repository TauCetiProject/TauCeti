/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Order.Cadlag
public import TauCeti.MeasureTheory.OptimalTransport.DynamicPlan
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Bernoulli
import TauCeti.MeasureTheory.Measure.ContinuousMap
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.KantorovichRubinstein

/-!
# A Wasserstein geodesic with no continuous-path lift

The curve `(1-t) δ₀ + t δ₁` is a constant-speed geodesic for the `1`-Wasserstein distance.
Nevertheless no probability measure on continuous paths has these time marginals: almost every
path would stay in the disconnected set `{0,1}` and hence could not join its two endpoints.
The same marginals are realized by jumping from zero to one at a uniform random time.
This distinguishes continuous-path superposition from the bounded-variation endpoint theory.
The closed-range argument uses `TauCeti.ae_forall_apply_mem_of_dense`; the distance lower bound
uses Kantorovich–Rubinstein weak duality with the identity function.

## References

* E. Abedi, Z. Li and T. Schultz, *Absolutely continuous and BV-curves in 1-Wasserstein spaces*,
  Calc. Var. Partial Differential Equations 63 (2024), Example 1.1.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

namespace TauCeti

/-- The sample path that jumps from zero to one at time `a`. -/
noncomputable def jumpPath (a t : I) : ℝ := if a ≤ t then 1 else 0

/-- The value of a jump path, including its value at the jump itself. -/
theorem jumpPath_def (a t : I) : jumpPath a t = if a ≤ t then 1 else 0 :=
  (rfl)

@[simp] theorem jumpPath_of_le {a t : I} (h : a ≤ t) : jumpPath a t = 1 := by
  simp [jumpPath_def, h]

@[simp] theorem jumpPath_of_lt {a t : I} (h : t < a) : jumpPath a t = 0 := by
  simp [jumpPath_def, not_le.mpr h]

/-- Jump paths are nondecreasing. -/
theorem monotone_jumpPath (a : I) : Monotone (jumpPath a) := by
  intro s t hst
  by_cases has : a ≤ s
  · simp only [jumpPath_def, ite_eq_left has, ite_eq_left (has.trans hst), le_refl]
  · simp only [jumpPath_def, ite_eq_right has]
    split_ifs <;> norm_num

/-- Jump paths have bounded variation, although they need not be continuous. -/
theorem boundedVariationOn_jumpPath (a : I) : BoundedVariationOn (jumpPath a) univ := by
  refine ((monotone_jumpPath a).monotoneOn univ).boundedVariationOn (C := 1) fun t _ ↦ ?_
  rw [jumpPath_def]
  split_ifs <;> norm_num

/-- A jump path is right-continuous and has a left limit at every time. -/
theorem isCadlag_jumpPath (a : I) : IsCadlag (jumpPath a) where
  isRightContinuous t := by
    by_cases hat : a ≤ t
    · rw [ContinuousWithinAt, jumpPath_def, ite_eq_left hat]
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with u hu
      simp [hat.trans hu.le]
    · rw [ContinuousWithinAt, jumpPath_def, ite_eq_right hat]
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (gt_mem_nhds (not_le.mp hat))] with u hu
      simp [jumpPath_def, not_le.mpr hu]
  tendsto_nhdsLT t := by
    by_cases hta : t ≤ a
    · refine ⟨0, Filter.Tendsto.congr' ?_ tendsto_const_nhds⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hua : ¬ a ≤ u := not_le.mpr (lt_of_lt_of_le hu hta)
      simp only [jumpPath_def, ite_eq_right hua]
    · refine ⟨1, Filter.Tendsto.congr' ?_ tendsto_const_nhds⟩
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (lt_mem_nhds (not_le.mp hta))] with u hu
      simp [hu.le]

/-- At a fixed time, the jump path is a measurable function of its jump time. -/
@[fun_prop] theorem measurable_jumpPath (t : I) : Measurable fun a ↦ jumpPath a t := by
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- Uniform jump times realize exactly the two-point mixture at every time, including endpoints.
The paths here are functions, not elements of continuous path space. -/
theorem map_jumpPath (t : I) : volume.map (fun a ↦ jumpPath a t) = Ber((1 : ℝ), 0, t) := by
  have hpath : (fun a ↦ jumpPath a t) = (Iic t).indicator (1 : I → ℝ) := by
    funext a
    by_cases h : a ≤ t
    · simp [h]
    · simp [not_le.mp h, Set.indicator_of_notMem, h]
  rw [hpath]
  have hparam : (⟨volume.real (Iic t), by simp⟩ : I) = t := by
    ext
    simp [measureReal_def, unitInterval.volume_Iic, ENNReal.toReal_ofReal t.2.1]
  simpa only [hparam] using
    (hasLaw_indicator_one_bernoulliMeasure
      (P := volume) (M := ℝ) (s := Iic t) measurableSet_Iic.nullMeasurableSet).map_eq

/-- The exact `W₁` distance along the mixture curve: mass moves by jumps, but its law moves
at constant unit speed. -/
theorem wassersteinEDist_one_bernoulliMeasure_one_zero (s t : I) :
    wassersteinEDist 1 Ber((1 : ℝ), 0, s) Ber((1 : ℝ), 0, t) = edist s t := by
  suffices h : ∀ s t : I, s ≤ t →
      wassersteinEDist 1 Ber((1 : ℝ), 0, s) Ber((1 : ℝ), 0, t) =
        ENNReal.ofReal ((t : ℝ) - s) by
    rcases le_total s t with hst | hts
    · have hst' : (s : ℝ) ≤ t := hst
      simpa [edist_dist, Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hst'),
        neg_sub] using h s t hst
    · have hts' : (t : ℝ) ≤ s := hts
      rw [wassersteinEDist_comm measurable_edist, edist_comm s t]
      simpa [edist_dist, Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hts'),
        neg_sub] using h t s hts
  intro s t hst
  apply le_antisymm
  · have hst' : (s : ℝ) ≤ t := hst
    simpa [edist_dist, Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hst'), neg_sub]
      using wassersteinEDist_one_bernoulliMeasure_le measurable_edist (1 : ℝ) 0 s t
  · -- The difference of means gives the matching lower bound.
    simpa [integral_bernoulliMeasure] using ofReal_integral_sub_integral_le_wassersteinEDist_one
      LipschitzWith.id (integrable_bernoulliMeasure 1 0 t id)
      (integrable_bernoulliMeasure 1 0 s id)
      |>.trans_eq (wassersteinEDist_comm measurable_edist 1 Ber((1 : ℝ), 0, t) Ber(1, 0, s))

/-- The two-point mixture curve in the finite-first-moment Wasserstein space. -/
noncomputable def bernoulliMixtureCurve (t : I) : WassersteinSpace 1 ℝ :=
  WassersteinSpace.mk ⟨Ber((1 : ℝ), 0, t), inferInstance⟩
    (hasFiniteMoment_bernoulliMeasure 1 1 0 t)

@[simp] theorem coe_bernoulliMixtureCurve (t : I) :
    ((bernoulliMixtureCurve t : ProbabilityMeasure ℝ) : Measure ℝ) = Ber((1 : ℝ), 0, t) := by
  exact congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk _ _)

/-- The mixture curve is an isometric copy of the unit interval in `P₁(ℝ)`, hence a
constant-speed Wasserstein geodesic from `δ₀` to `δ₁`. -/
theorem isometry_bernoulliMixtureCurve : Isometry bernoulliMixtureCurve := by
  intro s t
  rw [WassersteinSpace.edist_def, coe_bernoulliMixtureCurve, coe_bernoulliMixtureCurve,
    wassersteinEDist_one_bernoulliMeasure_one_zero]

/-- No probability law on continuous real paths has the two-point mixture as every time marginal.
Thus even a `W₁` geodesic need not admit continuous-path superposition. -/
theorem not_exists_timeMarginal_eq_bernoulliMeasure_one_zero :
    ¬ ∃ η : Measure C(I, ℝ), IsProbabilityMeasure η ∧
      ∀ t, η.timeMarginal t = Ber((1 : ℝ), 0, t) := by
  rintro ⟨η, hη, h⟩
  let := hη
  have hstay : ∀ᵐ γ ∂η, ∀ t, γ t ∈ ({0, 1} : Set ℝ) := by
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense I
    refine ae_forall_apply_mem_of_dense hDc hDd (Set.toFinite {0, 1}).isClosed fun t _ ↦ ?_
    apply (Measure.ae_timeMarginal_iff (Set.toFinite {0, 1}).measurableSet).1
    rw [h t]
    apply mem_ae_iff.mpr
    simp [bernoulliMeasure_def]
  have hstart := Measure.ae_eq_of_timeMarginal_eq_dirac (by simpa using h 0)
  have hend := Measure.ae_eq_of_timeMarginal_eq_dirac (by simpa using h 1)
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hstay.and (hstart.and hend)).exists
  have hhalf : (1 / 2 : ℝ) ∈ Icc (γ 0) (γ 1) := by rw [hγ0, hγ1]; norm_num
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : I) 1 γ.continuous hhalf
  have := hγ t
  norm_num [ht] at this

end TauCeti
