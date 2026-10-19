/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Data.Fin.Tuple.Spacing
public import TauCeti.LinearAlgebra.Fin.PartialSums
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

private theorem partialSums_spacings (n : ℕ) (y : Fin n → ℝ) :
    partialSumsLinearEquiv ℝ n (fun i ↦ tupleSpacings 0 1 y i.castSucc) = y := by
  ext i
  rw [partialSumsLinearEquiv_apply, ← Fin.sum_Iic_castSucc,
    sum_Iic_tupleSpacings]
  simp

private theorem spacings_partialSums (n : ℕ) (x : Fin n → ℝ) :
    tupleSpacings 0 1 (partialSumsLinearEquiv ℝ n x) =
      Fin.snoc x (1 - ∑ i, x i) := by
  have hinit := (partialSumsLinearEquiv ℝ n).injective
    (partialSums_spacings n (partialSumsLinearEquiv ℝ n x))
  ext i
  induction i using Fin.lastCases with
  | cast i => simpa using congrFun hinit i
  | last =>
    have hsum := sum_tupleSpacings (0 : ℝ) 1 (partialSumsLinearEquiv ℝ n x)
    rw [Fin.sum_univ_castSucc] at hsum
    simp_rw [congrFun hinit] at hsum
    simpa using eq_sub_of_add_eq' hsum

private theorem partialSums_mem_orderedCube_iff (n : ℕ) (x : Fin n → ℝ) :
    (StrictMono (partialSumsLinearEquiv ℝ n x) ∧
      ∀ i, partialSumsLinearEquiv ℝ n x i ∈ Ioo (0 : ℝ) 1) ↔
      (∀ i, 0 < x i) ∧ ∑ i, x i < 1 := by
  have h := tupleSpacings_pos_iff (0 : ℝ) 1 (partialSumsLinearEquiv ℝ n x)
  rw [spacings_partialSums] at h
  have hp : (∀ i, 0 < (Fin.snoc x (1 - ∑ j, x j) : Fin (n + 1) → ℝ) i) ↔
      (∀ i, 0 < x i) ∧ ∑ i, x i < 1 := by
    rw [Fin.forall_iff_castSucc]
    simp [and_comm]
  rw [hp] at h
  simpa only [mem_Ioo, forall_and, and_true, zero_lt_one] using h.symm

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
  have hr (z : J → ℝ) (i : Fin n) : r z i = z ⟨i.castSucc, Fin.castSucc_ne_last i⟩ := by
    calc r z i = z (e i) := by simp [r, MeasurableEquiv.piCongrLeft]
         _ = z ⟨i.castSucc, Fin.castSucc_ne_last i⟩ := by
           apply congrArg z
           exact (finSuccAboveEquiv_apply (Fin.last n) i).trans
             (by apply Subtype.ext; exact Fin.succAbove_last_apply i)
  have hsum (z : J → ℝ) : ∑ i, r z i = ∑ j, z j := by
    simpa [r, MeasurableEquiv.piCongrLeft] using Equiv.sum_comp e z
  have hg : dirichletCumulative n = (partialSumsLinearEquiv ℝ n) ∘ r := by
    ext z i
    simp [dirichletCumulative, hr]
  -- Relabel the chart coordinates, then apply the determinant-one partial-sum map.
  have hrvol : (volume : Measure (J → ℝ)).map r = volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : J ↦ ℝ) e).symm.map_eq
  have hlin : (volume : Measure (Fin n → ℝ)).map (partialSumsLinearEquiv ℝ n) = volume := by
    have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi
      (f := partialSumsLinearMap ℝ n) (by simp)
    have hfun : ⇑(partialSumsLinearEquiv ℝ n) = ⇑(partialSumsLinearMap ℝ n) := by
      ext x i
      simp
    simpa only [hfun, det_partialSumsLinearMap, inv_one, abs_one, ENNReal.ofReal_one,
      one_smul] using h
  have hf : Measurable (partialSumsLinearEquiv ℝ n) :=
    (partialSumsLinearEquiv ℝ n).toContinuousLinearEquiv.continuous.measurable
  have hvol : (volume : Measure (J → ℝ)).map (dirichletCumulative n) = volume := by
    rw [hg, ← Measure.map_map hf r.measurable, hrvol, hlin]
  -- The positive simplex chart corresponds exactly to the ordered open unit cube.
  let C := {y : Fin n → ℝ | StrictMono y ∧ ∀ i, y i ∈ Ioo (0 : ℝ) 1}
  have hC : MeasurableSet C := by
    simp only [C, StrictMono, ofPred_and, ofPred_forall]
    exact (MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun _ ↦ measurableSet_lt (measurable_pi_apply i)
        (measurable_pi_apply j)).inter
      (MeasurableSet.iInter fun i ↦ measurable_pi_apply i measurableSet_Ioo)
  have hpre : dirichletCumulative n ⁻¹' C = dirichletChartRegion (Fin.last n) := by
    ext z
    rw [mem_preimage, hg]
    simp only [Function.comp_apply, C, mem_ofPred_eq, partialSums_mem_orderedCube_iff,
      mem_dirichletChartRegion_iff, hsum]
    apply and_congr_left
    intro _
    have hr' (i : Fin n) : r z i = z (e i) := by
      simp [r, MeasurableEquiv.piCongrLeft]
    simp_rw [hr']
    exact e.forall_congr fun _ ↦ Iff.rfl
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
  let e := finSuccAboveEquiv (Fin.last n)
  have hsum : ∑ i : Fin n, z ⟨i.castSucc, Fin.castSucc_ne_last i⟩ = ∑ j, z j := by
    simpa only [e, finSuccAboveEquiv_apply, Fin.succAbove_last_apply] using Equiv.sum_comp e z
  have hg := spacings_partialSums n (fun i ↦ z ⟨i.castSucc, Fin.castSucc_ne_last i⟩)
  ext i
  induction i using Fin.lastCases with
  | last => simp [dirichletCumulative, hg, hsum]
  | cast i => simp [dirichletCumulative, hg]

/-- The joint law of the gaps between sorted independent unit-uniform points is Dirichlet
with all shapes one. With no sample points, the sole gap is one. -/
theorem map_spacings_orderStatistics_pi_uniformMeasure (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ uniformMeasure 0 1).map
        (fun x ↦ (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
          (tupleSpacings 0 1 (fun i ↦ orderStatistic i x))) =
      dirichletMeasure (fun _ : Fin (n + 1) ↦ 1) := by
  have hF : Measurable (fun y : Fin n → ℝ ↦
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (tupleSpacings 0 1 y)) :=
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.measurable.comp
      (measurable_tupleSpacings 0 1)
  have hs : Measurable (fun x : Fin n → ℝ ↦ fun i ↦ orderStatistic i x) :=
    Measurable.of_eval fun i ↦ measurable_orderStatistic i
  calc
    _ = ((Measure.pi fun _ : Fin n ↦ uniformMeasure 0 1).map
        (fun x i ↦ orderStatistic i x)).map
        (fun y ↦ (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (tupleSpacings 0 1 y)) := by
      rw [Measure.map_map hF hs]
      simp only [Function.comp_def]
    _ = ((volume.withDensity
        (dirichletChartPDF (fun _ : Fin (n + 1) ↦ 1) (Fin.last n))).map
        (dirichletCumulative n)).map
        (fun y ↦ (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (tupleSpacings 0 1 y)) := by
      rw [map_orderStatistics_pi_uniformMeasure, map_dirichletCumulative_chart]
    _ = _ := by
      rw [Measure.map_map hF (measurable_dirichletCumulative n)]
      simp only [Function.comp_def, spacings_dirichletCumulative]
      exact (dirichletMeasure_eq_map_withDensity_dirichletChartPDF
        (fun _ ↦ zero_lt_one) (Fin.last n)).symm

/-- Spacings of any independent unit-uniform sample have the uniform-simplex Dirichlet law. -/
theorem hasLaw_spacings_orderStatistics_iid_uniformMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {X : Fin n → Ω → ℝ} (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (uniformMeasure 0 1) P) :
    HasLaw (fun ω ↦ (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
      (tupleSpacings 0 1 (fun i ↦ orderStatistic i (fun j ↦ X j ω))))
        (dirichletMeasure (fun _ : Fin (n + 1) ↦ 1)) P := by
  rw [← map_spacings_orderStatistics_pi_uniformMeasure]
  refine (hasLaw_map (X := fun x : Fin n → ℝ ↦
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
      (tupleSpacings 0 1 (fun i ↦ orderStatistic i x))) ?_).fun_comp
        (hindep.hasLaw_pi hlaw)
  exact ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.measurable.comp
    ((measurable_tupleSpacings 0 1).comp
      (Measurable.of_eval fun i ↦ measurable_orderStatistic i))).aemeasurable

end TauCeti.Probability
