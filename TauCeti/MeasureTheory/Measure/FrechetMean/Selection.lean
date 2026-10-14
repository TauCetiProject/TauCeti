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
on Wasserstein space with finitely many atoms has a Wasserstein barycenter. The multi-marginal
cost of that argument is the least value `inf_x ∑ j, w j * d(x, y j) ^ p` of the power
functional. For `1 ≤ p` its `p`-th root is `1`-Lipschitz in the family `y`, for the supremum
distance on families, by Minkowski's inequality for the weights; so the cost is continuous on any
pseudo-extended-metric space.

## Main statements

* `TauCeti.continuous_frechetPower_sum_smul_dirac` — the power functional of a weighted family of
  points depends jointly continuously on the points and the center;
* `TauCeti.IsFrechetBarycenter.sum_mul_edist_rpow_eq_iInf` — a barycenter of a weighted family
  of points attains the least value of the power functional;
* `TauCeti.frechetRadius_sum_smul_dirac_le_add` and
  `TauCeti.continuous_iInf_frechetPower_sum_smul_dirac` — the Fréchet radius is `1`-Lipschitz in
  the family of points, and the least value of the power functional is continuous in it;
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

section WeightedPoints

variable [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {p : ℝ≥0∞}
  {w : J → ℝ≥0}

/-- At a `p`-Fréchet barycenter `b` of the weighted law `∑ j, w j • δ_{x j}`, for a finite nonzero
exponent `p`, the weighted sum `∑ j, w j * d(b, x j) ^ p` is its least value over all centers. -/
theorem IsFrechetBarycenter.sum_mul_edist_rpow_eq_iInf (hp0 : p ≠ 0) (hp : p ≠ ⊤) {x : J → X}
    {b : X} (hb : IsFrechetBarycenter p (∑ j, w j • Measure.dirac (x j)) b) :
    ∑ j, (w j : ℝ≥0∞) * edist b (x j) ^ p.toReal =
      ⨅ z, ∑ j, (w j : ℝ≥0∞) * edist z (x j) ^ p.toReal := by
  have hm (z : X) : AEMeasurable (fun y ↦ edist z y) (∑ j, w j • Measure.dirac (x j)) :=
    (continuous_const.edist continuous_id).measurable.aemeasurable
  have hb' := ((isFrechetBarycenter_iff_forall_frechetPower_le hp0 hp (hm b) hm).1 hb).2
  simp only [frechetPower_sum_smul_dirac, ENNReal.smul_def, smul_eq_mul] at hb'
  exact le_antisymm (le_iInf hb') (iInf_le _ b)

/-- For weights summing to `1` and `1 ≤ p`, moving the points of a weighted family changes the
`p`-Fréchet radius of its weighted law at any center by at most the largest displacement
`edist y y'`, by Minkowski's inequality for the weights. -/
theorem frechetRadius_sum_smul_dirac_le_add (hp : 1 ≤ p) (hw : ∑ j, w j = 1) (y y' : J → X)
    (x : X) :
    frechetRadius p (∑ j, w j • Measure.dirac (y j)) x ≤
      frechetRadius p (∑ j, w j • Measure.dirac (y' j)) x + edist y y' := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  -- Both weighted laws are pushforwards of one weighted law on the index type.
  let : MeasurableSpace J := ⊤
  set ν : Measure J := ∑ j, w j • Measure.dirac j
  have hν : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      ENNReal.smul_def, smul_eq_mul, mul_one]
    rw [← ENNReal.ofNNReal_finsetSum, hw, ENNReal.coe_one]⟩
  have hR (z : J → X) : frechetRadius p (∑ j, w j • Measure.dirac (z j)) x =
      eLpNorm (fun j ↦ edist x (z j)) p ν := by
    have hmap : ν.map z = ∑ j, w j • Measure.dirac (z j) := by
      simp only [ν, Measure.map_finset_sum measurable_from_top.aemeasurable,
        Measure.map_smul _ measurable_from_top.aemeasurable,
        Measure.map_dirac' measurable_from_top]
    rw [← hmap, frechetRadius_def, eLpNorm_map_measure (g := fun y ↦ edist x y)
      (continuous_const.edist continuous_id).measurable.aestronglyMeasurable
      measurable_from_top.aemeasurable]
    rfl
  have hconst : eLpNorm (fun _ : J ↦ edist y y') p ν = edist y y' := by
    rw [eLpNorm_const _ hp₀ (IsProbabilityMeasure.ne_zero ν)]
    simp
  rw [hR, hR, ← hconst]
  calc eLpNorm (fun j ↦ edist x (y j)) p ν ≤
        eLpNorm ((fun j ↦ edist x (y' j)) + fun _ ↦ edist y y') p ν :=
      eLpNorm_mono_enorm measurable_from_top.aestronglyMeasurable fun j ↦ by
        have h := edist_le_pi_edist y' y j
        rw [edist_comm y' y] at h
        simpa using (edist_triangle x (y' j) (y j)).trans (add_le_add_right h _)
    _ ≤ _ := eLpNorm_add_le hp

/-- For weights summing to `1` and `1 ≤ p < ∞`, the minimal value
`inf_x ∑ j, w j * d(x, y j) ^ p` of the `p`-Fréchet power functional of the weighted law
`∑ j, w j • δ_{y j}` depends continuously on the family of points `y`. Its `p`-th root is
`1`-Lipschitz by `TauCeti.frechetRadius_sum_smul_dirac_le_add`. -/
theorem continuous_iInf_frechetPower_sum_smul_dirac (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hw : ∑ j, w j = 1) :
    Continuous fun y : J → X ↦ ⨅ x, frechetPower p (∑ j, w j • Measure.dirac (y j)) x := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hm (y : J → X) (x : X) :
      AEMeasurable (fun z ↦ edist x z) (∑ j, w j • Measure.dirac (y j)) :=
    (continuous_const.edist continuous_id).measurable.aemeasurable
  have hrad : Continuous fun y : J → X ↦
      ⨅ x, frechetRadius p (∑ j, w j • Measure.dirac (y j)) x := by
    refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun y y' ↦ ?_
    rw [one_mul, ENNReal.iInf_add]
    exact iInf_mono fun x ↦ frechetRadius_sum_smul_dirac_le_add hp hw y y' x
  convert (ENNReal.continuous_rpow_const (y := p.toReal)).comp hrad using 1
  funext y
  simp only [Function.comp_apply, ← frechetRadius_rpow_eq_frechetPower hp₀ hp_top (hm y _)]
  exact ((ENNReal.monotone_rpow_of_nonneg ENNReal.toReal_nonneg).map_iInf_of_continuousAt
    ENNReal.continuous_rpow_const.continuousAt
    (ENNReal.top_rpow_of_pos (ENNReal.toReal_pos hp₀ hp_top))).symm

end WeightedPoints

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
