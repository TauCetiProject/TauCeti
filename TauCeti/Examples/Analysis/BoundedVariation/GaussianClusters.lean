/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Cluster
public import TauCeti.Analysis.BoundedVariation.Weighted.Gaussian
public import TauCeti.Analysis.BoundedVariation.Weighted.HalfSpace
public import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Checks for Gaussian clusters

For the Gaussian weight on a finite-dimensional real inner product space `E` and a unit vector `ν`:

* the two half-spaces `({⟪x, ν⟫ < s}, {⟪x, ν⟫ > s})` form a `2`-cluster
  (`TauCeti.Examples.GaussianClusters.halfSpaces`) of total perimeter `φ(s)`
  (`TauCeti.Examples.GaussianClusters.perimeter_halfSpaces`): the hyperplane between them is a null
  set, and the total perimeter of a `2`-cluster is the perimeter of either cell;
* `(E, ∅)` is a `2`-cluster (`TauCeti.Examples.GaussianClusters.univEmpty`) of total perimeter `0`
  and measure vector `(1, 0)`;
* the `1`-cluster `(E)` has total perimeter `0` and measure vector `(1)`, while the half-space
  `{⟪x, ν⟫ < 0}` is not the cell of any `1`-cluster: it leaves the set `{⟪x, ν⟫ ≥ 0}`, which
  has positive measure, uncovered
  (`TauCeti.Examples.GaussianClusters.not_exists_cluster_one_halfSpace`);
* overlapping cells such as `((−∞, 1), (0, ∞))` in `ℝ` are excluded by disjointness
  (`TauCeti.Examples.GaussianClusters.not_exists_cluster_Iio_Ioi`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

public noncomputable section

namespace TauCeti.Examples.GaussianClusters

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The two half-spaces form a `2`-cluster.** For a unit vector `ν` and a real `s`, the cells
`{⟪x, ν⟫ < s}` and `{⟪x, ν⟫ > s}` form a `2`-cluster for the Gaussian weight. -/
def halfSpaces {ν : E} (hν : ‖ν‖ = 1) (s : ℝ) : Cluster (gaussianWeight E) 2 where
  cell := ![{x | ⟪x, ν⟫ < s}, {x | s < ⟪x, ν⟫}]
  nullMeasurableSet_cell i := by
    have hc : Continuous fun x : E => ⟪x, ν⟫ := continuous_id.inner continuous_const
    fin_cases i
    · exact (isOpen_lt hc continuous_const).measurableSet.nullMeasurableSet
    · exact (isOpen_lt continuous_const hc).measurableSet.nullMeasurableSet
  pairwise_disjoint i j hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact disjoint_left.2 fun x (h1 : ⟪x, ν⟫ < s) (h2 : s < ⟪x, ν⟫) => lt_asymm h1 h2
    · exact disjoint_left.2 fun x (h1 : s < ⟪x, ν⟫) (h2 : ⟪x, ν⟫ < s) => lt_asymm h1 h2
    · exact (hij rfl).elim
  volume_compl_iUnion := by
    refine measure_mono_null (fun x hx => ?_) (Measure.addHaar_setOf_inner_eq volume
      (norm_ne_zero_iff.1 (by rw [hν]; exact one_ne_zero)) s)
    simp only [mem_compl_iff, mem_iUnion, not_exists, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, mem_ofPred_eq, not_lt] at hx
    exact le_antisymm hx.2 hx.1
  weightedPerimeter_lt_top i := by
    rw [← gaussianPerimeter_def]
    fin_cases i
    · simp [gaussianPerimeter_setOf_inner_lt hν]
    · have hν' : ‖-ν‖ = 1 := by rw [norm_neg, hν]
      have h : {x : E | s < ⟪x, ν⟫} = {x | ⟪x, -ν⟫ < -s} := by
        ext x
        simp [inner_neg_right]
      simp [h, gaussianPerimeter_setOf_inner_lt hν']

/-- **The total perimeter of the two half-spaces** is `φ(s)`. -/
theorem perimeter_halfSpaces {ν : E} (hν : ‖ν‖ = 1) (s : ℝ) :
    (halfSpaces hν s).perimeter = ENNReal.ofReal (gaussianPDFReal 0 1 s) := by
  rw [Cluster.perimeter_eq_weightedPerimeter_cell_zero contDiff_gaussianWeight,
    ← gaussianPerimeter_def]
  exact gaussianPerimeter_setOf_inner_lt hν s

/-- The pair `(E, ∅)` is a `2`-cluster for the Gaussian weight. -/
def univEmpty : Cluster (gaussianWeight E) 2 where
  cell := ![univ, ∅]
  nullMeasurableSet_cell i := by
    fin_cases i
    · exact .univ
    · exact .empty
  pairwise_disjoint i j hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact disjoint_empty _
    · exact empty_disjoint _
    · exact (hij rfl).elim
  volume_compl_iUnion := by
    refine measure_mono_null (fun x hx => ?_) measure_empty
    exact hx (mem_iUnion.2 ⟨0, mem_univ x⟩)
  weightedPerimeter_lt_top i := by
    fin_cases i
    · simp [weightedPerimeter_univ contDiff_gaussianWeight]
    · simp [weightedPerimeter_empty]

/-- The cluster `(E, ∅)` has total perimeter `0`. -/
theorem perimeter_univEmpty : (univEmpty (E := E)).perimeter = 0 := by
  rw [Cluster.perimeter_eq_weightedPerimeter_cell_zero contDiff_gaussianWeight]
  exact weightedPerimeter_univ contDiff_gaussianWeight

/-- The cluster `(E, ∅)` has measure vector `(1, 0)`. -/
theorem weightedMeasure_univEmpty_cell :
    (fun i => weightedMeasure (gaussianWeight E) ((univEmpty (E := E)).cell i)) = ![1, 0] := by
  ext i
  fin_cases i <;> simp [univEmpty, weightedMeasure_def, withDensity_exp_neg_gaussianWeight]

/-- The `1`-cluster `(E)` has total perimeter `0` and measure vector `(1)`. -/
theorem perimeter_univ_and_weightedMeasure_cell :
    (Cluster.univ (contDiff_gaussianWeight (E := E))).perimeter = 0 ∧
      ∀ i, weightedMeasure (gaussianWeight E) ((Cluster.univ (contDiff_gaussianWeight
        (E := E))).cell i) = 1 :=
  ⟨Cluster.perimeter_eq_zero_of_one contDiff_gaussianWeight _, fun i => by
    simp [Cluster.univ_cell, weightedMeasure_def, withDensity_exp_neg_gaussianWeight]⟩

/-- **A half-space is not a `1`-cluster.** No `1`-cluster for the Gaussian weight has the
half-space `{⟪x, ν⟫ < 0}` as its cell: the set `{⟪x, ν⟫ ≥ 0}`, which has positive volume, would be
left uncovered. -/
theorem not_exists_cluster_one_halfSpace (ν : E) :
    ¬ ∃ Ω : Cluster (gaussianWeight E) 1, Ω.cell 0 = {x | ⟪x, ν⟫ < 0} := by
  rintro ⟨Ω, hΩ⟩
  have hc : Continuous fun x : E => ⟪x, ν⟫ := continuous_id.inner continuous_const
  have hpos : 0 < volume {x : E | 0 ≤ ⟪x, ν⟫} := by
    rcases eq_or_ne ν 0 with rfl | hν
    · simpa using isOpen_univ.measure_pos (volume : Measure E) univ_nonempty
    · exact ((isOpen_lt continuous_const hc).measure_pos volume
        ⟨ν, show 0 < ⟪ν, ν⟫ from real_inner_self_pos.2 hν⟩).trans_le
          (measure_mono fun x (hx : 0 < ⟪x, ν⟫) => hx.le)
  refine hpos.ne' (measure_mono_null (fun x (hx : 0 ≤ ⟪x, ν⟫) => ?_) Ω.volume_compl_iUnion)
  simp only [mem_compl_iff, mem_iUnion, not_exists]
  intro i
  rw [Subsingleton.elim i 0, hΩ]
  exact fun (h : ⟪x, ν⟫ < 0) => not_lt.2 hx h

/-- **Overlapping cells are excluded.** No `2`-cluster on `ℝ` has the overlapping cells
`(−∞, 1)` and `(0, ∞)`. -/
theorem not_exists_cluster_Iio_Ioi (W : ℝ → ℝ) :
    ¬ ∃ Ω : Cluster W 2, Ω.cell 0 = Iio 1 ∧ Ω.cell 1 = Ioi 0 := by
  rintro ⟨Ω, h0, h1⟩
  have h : Disjoint (Ω.cell 0) (Ω.cell 1) := Ω.pairwise_disjoint (show (0 : Fin 2) ≠ 1 by decide)
  rw [h0, h1] at h
  exact disjoint_left.1 h (show (1 / 2 : ℝ) ∈ Iio 1 by norm_num)
    (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num)

end TauCeti.Examples.GaussianClusters
