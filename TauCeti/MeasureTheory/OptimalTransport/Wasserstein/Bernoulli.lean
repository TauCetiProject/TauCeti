/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic

/-!
# Wasserstein estimates for Bernoulli measures

A two-point law on a pseudometric space has finite moments at every exponent, including infinity.
Changing its parameter from `s` to `t` costs at most `edist s t * edist x y` in `W₁`.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

namespace TauCeti

/-- A Bernoulli law has finite moments at every exponent, including infinity. -/
theorem hasFiniteMoment_bernoulliMeasure {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSingletonClass X]
    (p : ℝ≥0∞) (x y : X) (t : unitInterval) :
    HasFiniteMoment p (bernoulliMeasure x y t) := by
  classical
  apply hasFiniteMoment_of_ae_mem_finset (s := {x, y}) x
  apply mem_ae_iff.mpr
  simp [bernoulliMeasure_def]

/-- Changing the parameter of a Bernoulli law moves only the difference in mass between
its two atoms, giving this `W₁` bound. -/
theorem wassersteinEDist_one_bernoulliMeasure_le {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [WeakPseudoEMetricSpace X]
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (x y : X) (s t : I) :
    wassersteinEDist 1 Ber(x, y, s) Ber(x, y, t) ≤ edist s t * edist x y := by
  suffices h : ∀ s t : I, s ≤ t →
      wassersteinEDist 1 Ber(x, y, s) Ber(x, y, t) ≤
        ENNReal.ofReal ((t : ℝ) - s) * edist x y by
    rcases le_total s t with hst | hts
    · have hst' : (s : ℝ) ≤ t := hst
      simpa [edist_dist, Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hst'),
        neg_sub] using h s t hst
    · have hts' : (t : ℝ) ≤ s := hts
      rw [wassersteinEDist_comm hd, edist_comm s t]
      simpa [edist_dist, Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hts'),
        neg_sub] using h t s hts
  intro s t hst
  -- Leave the common mass fixed and move only the remaining mass from y to x.
  let commonMass : Measure X := ENNReal.ofReal (s : ℝ) • Measure.dirac x +
    ENNReal.ofReal (1 - (t : ℝ)) • Measure.dirac y
  let movedMass : Measure X := ENNReal.ofReal ((t : ℝ) - s) • Measure.dirac y
  have hleft : ENNReal.ofReal (1 - (t : ℝ)) + ENNReal.ofReal ((t : ℝ) - s) =
      ENNReal.ofReal (1 - (s : ℝ)) := by
    rw [← ENNReal.ofReal_add (sub_nonneg.2 t.2.2) (sub_nonneg.2 hst)]
    congr 1
    ring
  have hright : ENNReal.ofReal (s : ℝ) + ENNReal.ofReal ((t : ℝ) - s) =
      ENNReal.ofReal (t : ℝ) := by
    rw [← ENNReal.ofReal_add s.2.1 (sub_nonneg.2 hst)]
    congr 1
    ring
  have hs : Ber(x, y, s) = commonMass + movedMass := by
    simp [bernoulliMeasure_def, ← Measure.coe_nnreal_smul, ENNReal.coe_nnreal_eq,
      unitInterval.coe_toNNReal, unitInterval.coe_symm_eq, commonMass, movedMass,
      add_assoc, ← add_smul, hleft]
  have ht : Ber(x, y, t) = commonMass + movedMass univ • Measure.dirac x := by
    simp only [bernoulliMeasure_def, ← Measure.coe_nnreal_smul, ENNReal.coe_nnreal_eq,
      unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
    simp only [commonMass, movedMass, smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [add_right_comm (ENNReal.ofReal (s : ℝ) • Measure.dirac x), ← add_smul, hright]
  rw [hs, ht]
  refine (wassersteinEDist_add_smul_dirac_le hd 1 commonMass movedMass x).trans_eq ?_
  have hmeas : Measurable fun z ↦ edist z x := hd.comp (measurable_id.prodMk measurable_const)
  rw [eLpNorm_one_eq_lintegral_enorm hmeas.aestronglyMeasurable]
  simp [movedMass, lintegral_smul_measure, lintegral_dirac' y hmeas, edist_comm y x]

end TauCeti
