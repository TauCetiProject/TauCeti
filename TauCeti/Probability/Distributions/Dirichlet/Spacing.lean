/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Group.TupleSpacings
public import TauCeti.MeasureTheory.Measure.Lebesgue.PartialSums
public import TauCeti.Probability.Distributions.Dirichlet.Density
public import TauCeti.Probability.Distributions.OrderStatistic.Joint

/-!
# Uniform spacings have a Dirichlet law

The gaps between increasingly sorted independent unit-uniform points, with endpoints
zero and one adjoined, have the Dirichlet law with every shape equal to one. The joint
law follows by transporting the ordered-cube density through successive differences;
the inverse coordinate map takes partial sums and has determinant one. The empty
sample has the single gap one.

The density inputs are `map_orderStatistics_pi_uniformMeasure` and
`dirichletMeasure_eq_map_withDensity_dirichletChartPDF`.

## References

* H. A. David and H. N. Nagaraja, *Order Statistics*, 3rd ed., Wiley, 2003.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

private noncomputable def dirichletCumulative (n : ℕ)
    (z : {i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) : Fin n → ℝ :=
  partialSumsLinearEquiv ℝ n (fun i ↦ z ⟨i.castSucc, Fin.castSucc_ne_last i⟩)

private theorem measurable_dirichletCumulative (n : ℕ) :
    Measurable (dirichletCumulative n) := by
  exact (partialSumsLinearEquiv ℝ n).toContinuousLinearEquiv.continuous.measurable.comp
    (Measurable.of_eval fun i ↦ measurable_pi_apply _)

private theorem map_dirichletCumulative_chart (n : ℕ) :
    (volume.withDensity (dirichletChartPDF (fun _ : Fin (n + 1) ↦ 1) (Fin.last n))).map
        (dirichletCumulative n) =
      volume.withDensity
        ({y : Fin n → ℝ | StrictMono y ∧ ∀ i, y i ∈ Ioo (0 : ℝ) 1}.indicator
          fun _ ↦ (n.factorial : ℝ≥0∞)) := by
  classical
  let J := {i : Fin (n + 1) // i ≠ Fin.last n}
  let e : Fin n ≃ J := finSuccAboveEquiv (Fin.last n)
  let r := (MeasurableEquiv.piCongrLeft (fun _ : J ↦ ℝ) e).symm
  have hr (z : J → ℝ) : r z = fun i ↦ z ⟨i.castSucc, Fin.castSucc_ne_last i⟩ := by
    ext i
    calc r z i = z (e i) := by
           simpa only [MeasurableEquiv.piCongrLeft_apply_apply] using
             congrFun ((MeasurableEquiv.piCongrLeft (fun _ : J ↦ ℝ) e).apply_symm_apply z) (e i)
         _ = z ⟨i.castSucc, Fin.castSucc_ne_last i⟩ :=
           congrArg z (finSuccAboveEquiv_last_apply n i)
  have hg : dirichletCumulative n = (partialSumsLinearEquiv ℝ n) ∘ r := by
    funext z
    simp only [dirichletCumulative, Function.comp_apply, hr]
  -- Relabel the chart coordinates, then apply the determinant-one partial-sum map.
  have hrvol : (volume : Measure (J → ℝ)).map r = volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : J ↦ ℝ) e).symm.map_eq
  have hvol : (volume : Measure (J → ℝ)).map (dirichletCumulative n) = volume := by
    rw [hg, ← Measure.map_map (measurePreserving_partialSumsLinearEquiv n).measurable
      r.measurable, hrvol, (measurePreserving_partialSumsLinearEquiv n).map_eq]
  -- The positive simplex chart corresponds exactly to the ordered open unit cube.
  let C := {y : Fin n → ℝ | StrictMono y ∧ ∀ i, y i ∈ Ioo (0 : ℝ) 1}
  have hC : MeasurableSet C := measurableSet_strictMono_mem_Ioo n 0 1
  have hpre : dirichletCumulative n ⁻¹' C = dirichletChartRegion (Fin.last n) := by
    ext z
    have hcube := strictMono_partialSumsLinearEquiv_and_mem_Ioo_iff (0 : ℝ) 1 (r z)
    simp only [zero_add, zero_lt_one, and_true, sub_zero] at hcube
    rw [mem_preimage, hg]
    simp only [Function.comp_apply, C, mem_ofPred_eq, mem_dirichletChartRegion_iff]
    rw [hcube]
    simp only [hr, sum_finSuccAboveEquiv_last]
    apply and_congr_left
    intro _
    exact e.forall_congr fun i ↦ by rw [finSuccAboveEquiv_last_apply]
  have hpdf : dirichletChartPDF (fun _ : Fin (n + 1) ↦ 1) (Fin.last n) =
      (dirichletChartRegion (Fin.last n)).indicator fun _ ↦ (n.factorial : ℝ≥0∞) := by
    ext z
    by_cases hz : z ∈ dirichletChartRegion (Fin.last n)
    · simp [hz, Real.Gamma_nat_eq_factorial]
    · simp [hz]
  rw [hpdf, withDensity_indicator (measurableSet_dirichletChartRegion _), withDensity_const,
    Measure.map_smul _ (measurable_dirichletCumulative n).aemeasurable, ← hpre,
    ← Measure.restrict_map (measurable_dirichletCumulative n) hC, hvol,
    withDensity_indicator hC, withDensity_const]

private theorem spacings_dirichletCumulative (n : ℕ)
    (z : {i : Fin (n + 1) // i ≠ Fin.last n} → ℝ) :
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
      (tupleSpacings 0 1 (dirichletCumulative n z)) = dirichletChart (Fin.last n) z := by
  have hg := tupleSpacings_partialSumsLinearEquiv (0 : ℝ) 1
    (fun i : Fin n ↦ z ⟨i.castSucc, Fin.castSucc_ne_last i⟩)
  simp only [zero_add, sub_zero] at hg
  ext i
  induction i using Fin.lastCases with
  | last => simp [dirichletCumulative, hg, sum_finSuccAboveEquiv_last]
  | cast i => simp [dirichletCumulative, hg]

private theorem measurable_euclidean_tupleSpacings (n : ℕ) :
    Measurable (fun y : Fin n → ℝ ↦
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (tupleSpacings 0 1 y)) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.measurable.comp
    (measurable_tupleSpacings 0 1)

/-- The joint law of the gaps between sorted independent unit-uniform points is Dirichlet
with all shapes one. With no sample points, the sole gap is one. -/
theorem map_tupleSpacings_orderStatistics_pi_uniformMeasure (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ uniformMeasure 0 1).map
        (fun x ↦ (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
          (tupleSpacings 0 1 (fun i ↦ orderStatistic i x))) =
      dirichletMeasure (fun _ : Fin (n + 1) ↦ 1) := by
  have hs : Measurable (fun x : Fin n → ℝ ↦ fun i ↦ orderStatistic i x) := by fun_prop
  calc
    _ = ((Measure.pi fun _ : Fin n ↦ uniformMeasure 0 1).map
        (fun x i ↦ orderStatistic i x)).map
        (fun y ↦ (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (tupleSpacings 0 1 y)) := by
      rw [Measure.map_map (measurable_euclidean_tupleSpacings n) hs]
      simp only [Function.comp_def]
    _ = ((volume.withDensity
        (dirichletChartPDF (fun _ : Fin (n + 1) ↦ 1) (Fin.last n))).map
        (dirichletCumulative n)).map
        (fun y ↦ (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (tupleSpacings 0 1 y)) := by
      rw [map_orderStatistics_pi_uniformMeasure, map_dirichletCumulative_chart]
    _ = _ := by
      rw [Measure.map_map (measurable_euclidean_tupleSpacings n)
        (measurable_dirichletCumulative n)]
      simp only [Function.comp_def, spacings_dirichletCumulative]
      exact (dirichletMeasure_eq_map_withDensity_dirichletChartPDF
        (fun _ ↦ zero_lt_one) (Fin.last n)).symm

/-- Spacings of any independent unit-uniform sample have the uniform-simplex Dirichlet law. -/
theorem hasLaw_tupleSpacings_orderStatistics_iid_uniformMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {X : Fin n → Ω → ℝ} (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (uniformMeasure 0 1) P) :
    HasLaw (fun ω ↦ (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
      (tupleSpacings 0 1 (fun i ↦ orderStatistic i (fun j ↦ X j ω))))
        (dirichletMeasure (fun _ : Fin (n + 1) ↦ 1)) P := by
  rw [← map_tupleSpacings_orderStatistics_pi_uniformMeasure]
  refine (hasLaw_map (X := fun x : Fin n → ℝ ↦
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
      (tupleSpacings 0 1 (fun i ↦ orderStatistic i x))) ?_).fun_comp
        (hindep.hasLaw_pi hlaw)
  exact ((measurable_euclidean_tupleSpacings n).comp
    (by fun_prop)).aemeasurable

end TauCeti.Probability
