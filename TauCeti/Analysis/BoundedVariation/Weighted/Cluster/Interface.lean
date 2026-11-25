/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Cluster.Basic
public import TauCeti.Analysis.BoundedVariation.Weighted.ReducedBoundary
import TauCeti.Analysis.BoundedVariation.Interface

/-!
# The interface decomposition of a cluster

Let `Ω = (Ω_1, …, Ω_q)` be a cluster for a `C¹` weight `W` on a Euclidean space `E` of dimension
`n ≥ 2`, with measure `μ = e^{−W} · volume`. For `i ≠ j` the **interface** between the cells
`Ω_i` and `Ω_j` is `Σ_ij = ∂*Ω_i ∩ ∂*Ω_j` (`TauCeti.Cluster.interface`), and its weighted area is
`A_ij = ∫_{Σ_ij} e^{−W} dHⁿ⁻¹` (`TauCeti.Cluster.interfaceArea`); permuting the cells permutes
the interfaces and their areas (`TauCeti.Cluster.interface_permute`,
`TauCeti.Cluster.interfaceArea_permute`). Up to an `Hⁿ⁻¹`-null set the
reduced boundary of a union of cells `⋃_{i ∈ S} Ω_i` is the union of the interfaces `Σ_ij` with
`i ∈ S` and `j ∉ S` (`TauCeti.reducedBoundary_biUnion_ae_eq`), and distinct interfaces meet in an
`Hⁿ⁻¹`-null set, since almost no point lies on the reduced boundaries of three cells
(`TauCeti.ae_notMem_reducedBoundary_of_mem_reducedBoundary_of_mem_reducedBoundary`). Hence:

* `P_μ(⋃_{i ∈ S} Ω_i) = Σ_{i ∈ S, j ∉ S} A_ij`
  (`TauCeti.Cluster.weightedPerimeter_biUnion_cell_eq_sum_interfaceArea`);
* `P_μ(Ω_i) = Σ_{j ≠ i} A_ij` (`TauCeti.Cluster.weightedPerimeter_cell_eq_sum_interfaceArea`);
* the total perimeter is `P_μ(Ω) = Σ_{i < j} A_ij`
  (`TauCeti.Cluster.perimeter_eq_sum_interfaceArea`).

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), equations (3.4)-(3.6).
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press (2012), Exercise 29.7.
-/

public section

noncomputable section

open MeasureTheory Set Module TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {q : ℕ}

namespace Cluster

/-- The **interface** `Σ_ij = ∂*Ω_i ∩ ∂*Ω_j` between two cells of a cluster. -/
def interface (Ω : Cluster W q) (i j : Fin q) : Set E :=
  reducedBoundary volume ⊤ (Ω.cell i) ∩ reducedBoundary volume ⊤ (Ω.cell j)

/-- Unfolding `TauCeti.Cluster.interface`. -/
theorem interface_def (Ω : Cluster W q) (i j : Fin q) :
    Ω.interface i j = reducedBoundary volume ⊤ (Ω.cell i) ∩ reducedBoundary volume ⊤ (Ω.cell j) :=
  (rfl)

/-- A point lies on the interface `Σ_ij` when it lies on the reduced boundaries of both cells. -/
@[simp]
theorem mem_interface {Ω : Cluster W q} {i j : Fin q} {x : E} :
    x ∈ Ω.interface i j ↔
      x ∈ reducedBoundary volume ⊤ (Ω.cell i) ∧ x ∈ reducedBoundary volume ⊤ (Ω.cell j) :=
  Iff.rfl

/-- The interface is symmetric. -/
theorem interface_comm (Ω : Cluster W q) (i j : Fin q) : Ω.interface i j = Ω.interface j i :=
  inter_comm _ _

/-- The interfaces of a permuted cluster. -/
@[simp]
theorem interface_permute (Ω : Cluster W q) (σ : Equiv.Perm (Fin q)) (i j : Fin q) :
    (Ω.permute σ).interface i j = Ω.interface (σ i) (σ j) := by
  simp only [interface_def, permute_cell]

/-- Interfaces are measurable. -/
theorem measurableSet_interface (Ω : Cluster W q) (i j : Fin q) :
    MeasurableSet (Ω.interface i j) :=
  measurableSet_reducedBoundary.inter measurableSet_reducedBoundary

/-- The **weighted area** `A_ij = ∫_{Σ_ij} e^{−W} dHⁿ⁻¹` of the interface between two cells. -/
def interfaceArea (Ω : Cluster W q) (i j : Fin q) : ℝ≥0∞ :=
  ∫⁻ x in Ω.interface i j, ENNReal.ofReal (Real.exp (-W x)) ∂μHE[finrank ℝ E - 1]

/-- Unfolding `TauCeti.Cluster.interfaceArea`. -/
theorem interfaceArea_def (Ω : Cluster W q) (i j : Fin q) :
    Ω.interfaceArea i j =
      ∫⁻ x in Ω.interface i j, ENNReal.ofReal (Real.exp (-W x)) ∂μHE[finrank ℝ E - 1] :=
  (rfl)

/-- The interface area is symmetric. -/
theorem interfaceArea_comm (Ω : Cluster W q) (i j : Fin q) :
    Ω.interfaceArea i j = Ω.interfaceArea j i := by
  rw [interfaceArea_def, interfaceArea_def, interface_comm]

/-- The interface areas of a permuted cluster. -/
@[simp]
theorem interfaceArea_permute (Ω : Cluster W q) (σ : Equiv.Perm (Fin q)) (i j : Fin q) :
    (Ω.permute σ).interfaceArea i j = Ω.interfaceArea (σ i) (σ j) := by
  rw [interfaceArea_def, interfaceArea_def, interface_permute]

/-- **The perimeter of a union of cells is the area of its interfaces with the other cells.**
For a `C¹` weight, in dimension `n ≥ 2`, `P_μ(⋃_{i ∈ S} Ω_i) = Σ_{i ∈ S} Σ_{j ∉ S} A_ij`. -/
theorem weightedPerimeter_biUnion_cell_eq_sum_interfaceArea (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (Ω : Cluster W q) (S : Finset (Fin q)) :
    weightedPerimeter W ⊤ (⋃ i ∈ S, Ω.cell i) = ∑ i ∈ S, ∑ j ∈ Sᶜ, Ω.interfaceArea i j := by
  have hm := Ω.nullMeasurableSet_cell
  have hd : ∀ i j, i ≠ j → AEDisjoint volume (Ω.cell i) (Ω.cell j) :=
    fun i j hij => (Ω.pairwise_disjoint hij).aedisjoint
  have hfin := fun i => exists_totalVariationOn_indicator_ne_top_of_weightedPerimeter_ne_top hW
    ((hm i).mono Measure.restrict_le_self) (Ω.weightedPerimeter_lt_top i).ne
  have hmS : NullMeasurableSet (⋃ i ∈ S, Ω.cell i) volume :=
    .biUnion (Finset.countable_toSet S) fun i _ => hm i
  have hPS : weightedPerimeter W ⊤ (⋃ i ∈ S, Ω.cell i) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ => (Ω.weightedPerimeter_lt_top i).ne)
      (Ω.weightedPerimeter_biUnion_cell_le hW S)
  rw [weightedPerimeter_eq_lintegral_reducedBoundary_of_ne_top hW hn
      (hmS.mono Measure.restrict_le_self) hPS,
    setLIntegral_congr (reducedBoundary_biUnion_ae_eq hn hm hd Ω.volume_compl_iUnion hfin S
      (exists_totalVariationOn_indicator_ne_top_of_weightedPerimeter_ne_top hW
        (hmS.mono Measure.restrict_le_self) hPS)),
    lintegral_biUnion_finset₀ ?_ fun p _ => (Ω.measurableSet_interface p.1 p.2).nullMeasurableSet,
    Finset.sum_product]
  · simp only [interfaceArea_def, interface_def]
  · -- distinct interfaces meet in a null set: their union would carry a triple point
    rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' hne
    simp only [Finset.coe_product, mem_prod, Finset.mem_coe, Finset.mem_compl] at hp hp'
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1
      (ae_notMem_reducedBoundary_of_mem_reducedBoundary_of_mem_reducedBoundary hn hm hd
        Ω.volume_compl_iUnion hfin))
    obtain ⟨⟨hi, hj⟩, hi', hj'⟩ := hx
    simp only [mem_ofPred_eq, not_forall, not_not]
    by_cases hii : i = i'
    · subst hii
      have hjj : j ≠ j' := fun h => hne (by rw [h])
      exact ⟨j, j', i, hjj, fun h => hp.2 (h ▸ hp.1), fun h => hp'.2 (h ▸ hp.1), hj, hj', hi⟩
    · exact ⟨i, i', j, hii, fun h => hp.2 (h ▸ hp.1), fun h => hp.2 (h ▸ hp'.1), hi, hi', hj⟩

/-- **The perimeter of a cell is the area of its interfaces.** For a `C¹` weight, in dimension
`n ≥ 2`, `P_μ(Ω_i) = Σ_{j ≠ i} A_ij`. -/
theorem weightedPerimeter_cell_eq_sum_interfaceArea (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (Ω : Cluster W q) (i : Fin q) :
    weightedPerimeter W ⊤ (Ω.cell i) = ∑ j ∈ {i}ᶜ, Ω.interfaceArea i j := by
  simpa using Ω.weightedPerimeter_biUnion_cell_eq_sum_interfaceArea hW hn {i}

/-- **The total perimeter of a cluster is the total area of its interfaces.** For a `C¹` weight,
in dimension `n ≥ 2`, `P_μ(Ω) = Σ_{i < j} A_ij`. -/
theorem perimeter_eq_sum_interfaceArea (hW : ContDiff ℝ 1 W) (hn : 2 ≤ finrank ℝ E)
    (Ω : Cluster W q) :
    Ω.perimeter = ∑ i, ∑ j ∈ Finset.Ioi i, Ω.interfaceArea i j := by
  have hsplit (i : Fin q) : ∑ j ∈ {i}ᶜ, Ω.interfaceArea i j =
      ∑ j ∈ Finset.Iio i, Ω.interfaceArea i j + ∑ j ∈ Finset.Ioi i, Ω.interfaceArea i j := by
    rw [← Finset.sum_union (Finset.disjoint_left.2 fun j hj hj' =>
      (Finset.mem_Iio.1 hj).not_gt (Finset.mem_Ioi.1 hj'))]
    congr 1
    ext j
    simp only [Finset.mem_compl, Finset.mem_singleton, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi]
    omega
  have hswap : ∑ i, ∑ j ∈ Finset.Iio i, Ω.interfaceArea i j =
      ∑ i, ∑ j ∈ Finset.Ioi i, Ω.interfaceArea i j := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.Ioi j)
      (fun i j => by simp [and_comm])]
    simp_rw [interfaceArea_comm Ω]
  rw [perimeter_def]
  simp_rw [weightedPerimeter_cell_eq_sum_interfaceArea hW hn, hsplit, Finset.sum_add_distrib,
    hswap, ← two_mul]
  rw [mul_comm]
  exact ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top

end Cluster

end TauCeti
