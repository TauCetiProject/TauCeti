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

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace TauCeti

/-- The two-point mixture moving mass from zero to one, rather than moving either atom. -/
noncomputable def jumpMarginal (t : I) : Measure ℝ :=
  ENNReal.ofReal (1 - (t : ℝ)) • Measure.dirac 0 +
    ENNReal.ofReal (t : ℝ) • Measure.dirac 1

/-- The defining mixture formula. -/
theorem jumpMarginal_def (t : I) : jumpMarginal t =
    ENNReal.ofReal (1 - (t : ℝ)) • Measure.dirac 0 +
      ENNReal.ofReal (t : ℝ) • Measure.dirac 1 :=
  (rfl)

/-- Every two-point mixture has unit mass. -/
instance (t : I) : IsProbabilityMeasure (jumpMarginal t) where
  measure_univ := by
    simp only [jumpMarginal_def, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (sub_nonneg.2 t.2.2) t.2.1]
    simp

@[simp] theorem jumpMarginal_zero : jumpMarginal 0 = Measure.dirac 0 := by
  simp [jumpMarginal_def]

@[simp] theorem jumpMarginal_one : jumpMarginal 1 = Measure.dirac 1 := by
  simp [jumpMarginal_def]

/-- The mixture is concentrated on its two atoms. -/
theorem ae_mem_jumpMarginal (t : I) : ∀ᵐ x ∂jumpMarginal t, x ∈ ({0, 1} : Set ℝ) := by
  rw [jumpMarginal_def, ae_add_measure_iff]
  constructor <;> exact Measure.ae_smul_measure (by simp) _

/-- The mixture has finite moments at every exponent, including the bounded-support endpoint. -/
theorem hasFiniteMoment_jumpMarginal (p : ℝ≥0∞) (t : I) : HasFiniteMoment p (jumpMarginal t) := by
  apply hasFiniteMoment_of_ae_mem_finset (p := p) (s := {0, 1}) (0 : ℝ)
  simpa using ae_mem_jumpMarginal t

/-- The sample path that jumps from zero to one at time `a`. -/
noncomputable def jumpPath (a t : I) : ℝ := if a ≤ t then 1 else 0

/-- The value of a jump path, including its value at the jump itself. -/
theorem jumpPath_def (a t : I) : jumpPath a t = if a ≤ t then 1 else 0 :=
  (rfl)

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
      simp [jumpPath_def, hat.trans hu.le]
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
      simp [jumpPath_def, hu.le]

/-- At a fixed time, the jump path is a measurable function of its jump time. -/
@[fun_prop] theorem measurable_jumpPath (t : I) : Measurable fun a ↦ jumpPath a t := by
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- Uniform jump times realize exactly the two-point mixture at every time, including endpoints.
The paths here are functions, not elements of continuous path space. -/
theorem map_jumpPath (t : I) : volume.map (fun a ↦ jumpPath a t) = jumpMarginal t := by
  ext S hS
  rw [Measure.map_apply (measurable_jumpPath t) hS, jumpMarginal_def]
  by_cases h0 : (0 : ℝ) ∈ S <;> by_cases h1 : (1 : ℝ) ∈ S
  · have heq : (fun a ↦ jumpPath a t) ⁻¹' S = univ := by
      ext a
      by_cases hat : a ≤ t <;> simp [jumpPath, hat, h0, h1]
    simp [heq, h0, h1, ← ENNReal.ofReal_add (sub_nonneg.2 t.2.2) t.2.1]
  · have heq : (fun a ↦ jumpPath a t) ⁻¹' S = Ioi t := by
      ext a
      by_cases hat : a ≤ t <;> simp [jumpPath, hat, h0, h1, not_le.mp]
    simp [heq, h0, h1, unitInterval.volume_Ioi]
  · have heq : (fun a ↦ jumpPath a t) ⁻¹' S = Iic t := by
      ext a
      by_cases hat : a ≤ t <;> simp [jumpPath, hat, h0, h1]
    simp [heq, h0, h1, unitInterval.volume_Iic]
  · have heq : (fun a ↦ jumpPath a t) ⁻¹' S = ∅ := by
      ext a
      by_cases hat : a ≤ t <;> simp [jumpPath, hat, h0, h1]
    simp [heq, h0, h1]

/-- The mean of the two-point mixture equals its time parameter. -/
@[simp] theorem integral_id_jumpMarginal (t : I) : ∫ x, x ∂jumpMarginal t = (t : ℝ) := by
  have h0 : Integrable (fun x : ℝ ↦ x) (Measure.dirac 0) := integrable_dirac (by simp)
  have h1 : Integrable (fun x : ℝ ↦ x) (Measure.dirac 1) := integrable_dirac (by simp)
  rw [jumpMarginal_def, integral_add_measure (h0.smul_measure ENNReal.ofReal_ne_top)
    (h1.smul_measure ENNReal.ofReal_ne_top)]
  simp [integral_smul_measure, ENNReal.toReal_ofReal t.2.1]

/-- The exact `W₁` distance along the mixture curve: mass moves by jumps, but its law moves
at constant unit speed. -/
theorem wassersteinEDist_one_jumpMarginal (s t : I) :
    wassersteinEDist 1 (jumpMarginal s) (jumpMarginal t) = edist s t := by
  suffices h : ∀ s t : I, s ≤ t →
      wassersteinEDist 1 (jumpMarginal s) (jumpMarginal t) = ENNReal.ofReal ((t : ℝ) - s) by
    rcases le_total s t with hst | hts
    · rw [h s t hst, edist_dist, Subtype.dist_eq, Real.dist_eq, abs_of_nonpos]
      · simp [neg_sub]
      · exact sub_nonpos.2 hst
    · rw [wassersteinEDist_comm measurable_edist, h t s hts, edist_dist,
        Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
      exact sub_nonneg.2 hts
  intro s t hst
  apply le_antisymm
  · -- Couple both laws by the same uniform jump time.
    have hm := (measurable_jumpPath s).prodMk (measurable_jumpPath t)
    have hπ : IsCoupling (volume.map fun a ↦ (jumpPath a s, jumpPath a t))
        (jumpMarginal s) (jumpMarginal t) := by
      constructor
      · rw [Measure.fst_map_prodMk (measurable_jumpPath s) (measurable_jumpPath t), map_jumpPath]
      · rw [Measure.snd_map_prodMk (measurable_jumpPath s) (measurable_jumpPath t), map_jumpPath]
    refine (wassersteinEDist_le hπ 1).trans_eq ?_
    rw [eLpNorm_map_measure measurable_edist.aestronglyMeasurable hm.aemeasurable,
      eLpNorm_one_eq_lintegral_enorm (measurable_edist.comp hm).aestronglyMeasurable]
    have heq : (fun a ↦ ‖edist (jumpPath a s) (jumpPath a t)‖ₑ) =
        (Ioc s t).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
      funext a
      by_cases has : a ≤ s <;> by_cases hat : a ≤ t
      · simp [jumpPath, has, hat, Set.indicator_of_notMem, not_lt_of_ge has]
      · exact False.elim (hat (has.trans hst))
      · simp [jumpPath, has, hat, Set.indicator_of_mem, not_le.mp has]
      · simp [jumpPath, has, hat, Set.indicator_of_notMem]
    simp only [Function.comp_apply]
    rw [heq, lintegral_indicator_const measurableSet_Ioc]
    simp
  · -- The difference of means gives the matching lower bound.
    have hint (r : I) := (hasFiniteMoment_jumpMarginal 1 r).integrable_of_lipschitzWith
        LipschitzWith.id
    simpa using ofReal_integral_sub_integral_le_wassersteinEDist_one
      LipschitzWith.id (hint t) (hint s)
      |>.trans_eq (wassersteinEDist_comm measurable_edist 1 (jumpMarginal t) (jumpMarginal s))

/-- The mixture curve is an isometric copy of the unit interval in `P₁(ℝ)`, hence a
constant-speed Wasserstein geodesic from `δ₀` to `δ₁`. -/
theorem exists_isometry_jumpMarginal :
    ∃ γ : I → WassersteinSpace 1 ℝ, Isometry γ ∧
      ∀ t, ((γ t : ProbabilityMeasure ℝ) : Measure ℝ) = jumpMarginal t := by
  let γ (t : I) : WassersteinSpace 1 ℝ :=
    WassersteinSpace.mk ⟨jumpMarginal t, inferInstance⟩ (hasFiniteMoment_jumpMarginal 1 t)
  have hγ (t : I) : ((γ t : ProbabilityMeasure ℝ) : Measure ℝ) = jumpMarginal t :=
    (congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk
      ⟨jumpMarginal t, inferInstance⟩ (hasFiniteMoment_jumpMarginal 1 t))).trans
      (ProbabilityMeasure.coe_mk _ _)
  refine ⟨γ, fun s t ↦ ?_, hγ⟩
  rw [WassersteinSpace.edist_def, hγ, hγ, wassersteinEDist_one_jumpMarginal]

/-- No probability law on continuous real paths has the two-point mixture as every time marginal.
Thus even a `W₁` geodesic need not admit continuous-path superposition. -/
theorem not_exists_timeMarginal_eq_jumpMarginal :
    ¬ ∃ η : Measure C(I, ℝ), IsProbabilityMeasure η ∧
      ∀ t, η.timeMarginal t = jumpMarginal t := by
  rintro ⟨η, hη, h⟩
  let := hη
  have hstay : ∀ᵐ γ ∂η, ∀ t, γ t ∈ ({0, 1} : Set ℝ) := by
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense I
    refine ae_forall_apply_mem_of_dense hDc hDd (Set.toFinite {0, 1}).isClosed fun t _ ↦ ?_
    apply (Measure.ae_timeMarginal_iff (Set.toFinite {0, 1}).measurableSet).1
    rw [h t]
    exact ae_mem_jumpMarginal t
  have hstart := Measure.ae_eq_of_timeMarginal_eq_dirac (by simpa using h 0)
  have hend := Measure.ae_eq_of_timeMarginal_eq_dirac (by simpa using h 1)
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hstay.and (hstart.and hend)).exists
  have hhalf : (1 / 2 : ℝ) ∈ Icc (γ 0) (γ 1) := by rw [hγ0, hγ1]; norm_num
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : I) 1 γ.continuous hhalf
  have := hγ t
  norm_num [ht] at this

end TauCeti
