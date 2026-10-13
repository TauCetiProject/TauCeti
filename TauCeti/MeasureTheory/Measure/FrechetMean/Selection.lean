/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.FrechetMean.Basic
public import TauCeti.MeasureTheory.MeasurableSpace.Selection
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Measurable choice of Fréchet barycenters of weighted points

Fix finitely many weights `w j ≥ 0` summing to `1`. For a family `y : J → X` of points in a
metric space, the `p`-Fréchet barycenters of the weighted law `∑ j, w j • δ_{y j}` are the
minimizers of

`x ↦ ∑ j, w j * d(x, y j) ^ p`.

On a proper metric space and for `1 ≤ p < ∞`, such a barycenter exists for every family, and this
file shows that it can be chosen Borel measurably in the family: there is a measurable
*barycenter application* `T : (J → X) → X` with `T y` a barycenter of `∑ j, w j • δ_{y j}` for
every `y`. The objective depends jointly continuously on the family and the candidate point, so
this is an instance of the measurable selection of minimizers,
`Continuous.exists_measurable_isMinOn`.

A measurable barycenter application turns a multi-marginal transport plan of finitely many laws
into a candidate barycenter law by pushforward. This is how Le Gouic and Loubes prove that a law
on Wasserstein space with finitely many atoms has a Wasserstein barycenter.

## Main statements

* `TauCeti.continuous_frechetPower_sum_smul_dirac` — the power functional of a weighted family of
  points depends jointly continuously on the points and the center;
* `TauCeti.exists_measurable_isFrechetBarycenter_sum_smul_dirac` — on a proper metric space there
  is a measurable map sending each finite family of points to a Fréchet barycenter of its weighted
  law.

## References

* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Relat. Fields 168 (2017), 901--917, Lemma 7.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {X J : Type*} [Fintype J]

/-- The `p`-Fréchet power functional of the weighted law `∑ j, w j • δ_{y j}` depends jointly
continuously on the family of points `y` and the center `x`. -/
theorem continuous_frechetPower_sum_smul_dirac [PseudoEMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (w : J → ℝ≥0) (p : ℝ≥0∞) :
    Continuous fun q : (J → X) × X ↦
      frechetPower p (∑ j, w j • Measure.dirac (q.1 j)) q.2 := by
  simp_rw [frechetPower_sum_smul_dirac, ENNReal.smul_def, smul_eq_mul]
  refine continuous_finsetSum _ fun j _ ↦ ENNReal.continuous_const_mul ENNReal.coe_ne_top
    |>.comp <| ENNReal.continuous_rpow_const.comp ?_
  exact continuous_snd.edist ((continuous_apply j).comp continuous_fst)

variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Measurable barycenter application** (Le Gouic–Loubes). On a proper metric space, for
`1 ≤ p < ∞` and finitely many weights summing to `1`, a `p`-Fréchet barycenter of the weighted
law `∑ j, w j • δ_{y j}` can be chosen measurably in the family of points `y`. -/
theorem exists_measurable_isFrechetBarycenter_sum_smul_dirac [ProperSpace X] {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ⊤) {w : J → ℝ≥0} (hw : ∑ j, w j = 1) :
    ∃ T : (J → X) → X, Measurable T ∧
      ∀ y, IsFrechetBarycenter p (∑ j, w j • Measure.dirac (y j)) (T y) := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hm (μ : Measure X) (z : X) : AEMeasurable (fun x ↦ edist z x) μ :=
    (continuous_const.edist continuous_id).measurable.aemeasurable
  -- the power functional is finite, hence so is the radius
  have hpower (y : J → X) (x : X) :
      frechetPower p (∑ j, w j • Measure.dirac (y j)) x ≠ ⊤ := by
    rw [frechetPower_sum_smul_dirac]
    refine ENNReal.sum_ne_top.2 fun j _ ↦ ?_
    rw [ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg (edist_ne_top _ _))
  have hradius (y : J → X) (x : X) :
      frechetRadius p (∑ j, w j • Measure.dirac (y j)) x ≠ ⊤ := by
    intro h
    have h' := hpower y x
    rw [← frechetRadius_rpow_eq_frechetPower hp₀ hp_top (hm _ x), h,
      ENNReal.top_rpow_of_pos (ENNReal.toReal_pos hp₀ hp_top)] at h'
    exact h' rfl
  have hbary (y : J → X) (x : X) :
      IsFrechetBarycenter p (∑ j, w j • Measure.dirac (y j)) x ↔
        IsMinOn (frechetPower p (∑ j, w j • Measure.dirac (y j))) univ x := by
    rw [isFrechetBarycenter_iff_forall_frechetPower_le hp₀ hp_top (hm _ x) (hm _),
      isMinOn_univ_iff]
    exact and_iff_right (hradius y x)
  have : Nonempty J := by
    by_contra hJ
    rw [not_nonempty_iff] at hJ
    simp at hw
  have hmin (y : J → X) :
      ∃ x, IsMinOn (frechetPower p (∑ j, w j • Measure.dirac (y j))) univ x := by
    have : IsProbabilityMeasure (∑ j, w j • Measure.dirac (y j)) := by
      constructor
      simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
        ENNReal.smul_def, smul_eq_mul, mul_one]
      rw [← ENNReal.ofNNReal_finsetSum, hw, ENNReal.coe_one]
    obtain ⟨x, hx⟩ := exists_isFrechetBarycenter hp _ (hradius y (y (Classical.arbitrary J)))
    exact ⟨x, (hbary y x).1 hx⟩
  obtain ⟨T, hT, hTmin⟩ :=
    (continuous_frechetPower_sum_smul_dirac w p).exists_measurable_isMinOn hmin
  exact ⟨T, hT, fun y ↦ (hbary y (T y)).2 (hTmin y)⟩

end TauCeti
