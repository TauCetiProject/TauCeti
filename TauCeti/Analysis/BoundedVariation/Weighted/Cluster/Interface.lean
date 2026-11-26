/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Cluster.Basic
public import TauCeti.Analysis.BoundedVariation.Weighted.ReducedBoundary
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Analysis.BoundedVariation.Interface

/-!
# The interface decomposition of a cluster

Let `Ω = (Ω_1, …, Ω_q)` be a cluster for a `C¹` weight `W` on a Euclidean space `E` of dimension
`n ≥ 2`, with measure `μ = e^{−W} · volume`. For `i ≠ j` the **interface** between the cells
`Ω_i` and `Ω_j` is `Σ_ij = ∂*Ω_i ∩ ∂*Ω_j` (`TauCeti.Cluster.interface`), and its weighted area is
`A_ij = ∫_{Σ_ij} e^{−W} dHⁿ⁻¹` (`TauCeti.Cluster.interfaceArea`); permuting the cells permutes
the interfaces and their areas (`TauCeti.Cluster.interface_permute`,
`TauCeti.Cluster.interfaceArea_permute`). The cells have locally finite perimeter
(`TauCeti.Cluster.exists_totalVariationOn_indicator_cell_ne_top`), and up to an `Hⁿ⁻¹`-null set the
reduced boundary of a union of cells `⋃_{i ∈ S} Ω_i` is the union of the interfaces `Σ_ij` with
`i ∈ S` and `j ∉ S` (`TauCeti.Cluster.reducedBoundary_biUnion_cell_ae_eq`), almost every point of
`∂*Ω_i` lies on exactly one interface `Σ_ij`
(`TauCeti.Cluster.ae_existsUnique_mem_interface_of_mem_reducedBoundary_cell`), and distinct
interfaces meet in an `Hⁿ⁻¹`-null set (`TauCeti.Cluster.aedisjoint_interface`), since almost no
point lies on the reduced boundaries of three cells
(`TauCeti.Cluster.ae_notMem_reducedBoundary_cell_of_mem_interface`). Hence:

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

/-- For a `C¹` weight, the cells of a cluster have locally finite perimeter. -/
theorem exists_totalVariationOn_indicator_cell_ne_top (hW : ContDiff ℝ 1 W)
    (Ω : Cluster W q) (i : Fin q) :
    ∀ K, IsCompact K → K ⊆ ((⊤ : Opens E) : Set E) → ∃ U : Opens E, K ⊆ (U : Set E) ∧
      totalVariationOn volume U ((Ω.cell i).indicator 1) ≠ ∞ :=
  exists_totalVariationOn_indicator_ne_top_of_weightedPerimeter_ne_top hW
    ((Ω.nullMeasurableSet_cell i).mono Measure.restrict_le_self) (Ω.weightedPerimeter_lt_top i).ne

/-- **No triple points.** For a `C¹` weight, in dimension `n ≥ 2`, `Hⁿ⁻¹`-almost no point lies
on the reduced boundaries of three distinct cells. -/
theorem ae_notMem_reducedBoundary_cell_of_mem_interface (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (Ω : Cluster W q) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], ∀ i j k, i ≠ j → i ≠ k → j ≠ k → x ∈ Ω.interface i j →
      x ∉ reducedBoundary volume ⊤ (Ω.cell k) := by
  filter_upwards [ae_notMem_reducedBoundary_of_mem_reducedBoundary_of_mem_reducedBoundary hn
    Ω.nullMeasurableSet_cell (fun i j hij => (Ω.pairwise_disjoint hij).aedisjoint)
    Ω.volume_compl_iUnion (Ω.exists_totalVariationOn_indicator_cell_ne_top hW)]
    with x hx i j k hij hik hjk hxij
  exact hx i j k hij hik hjk (mem_interface.1 hxij).1 (mem_interface.1 hxij).2

/-- For a `C¹` weight, in dimension `n ≥ 2`, the interfaces `Σ_ij` and `Σ_i'j'` of two distinct
pairs of distinct cells meet in an `Hⁿ⁻¹`-null set. -/
theorem aedisjoint_interface (hW : ContDiff ℝ 1 W) (hn : 2 ≤ finrank ℝ E) (Ω : Cluster W q)
    {i j i' j' : Fin q} (hij : i ≠ j) (hi'j' : i' ≠ j') (hne : s(i, j) ≠ s(i', j')) :
    AEDisjoint μHE[finrank ℝ E - 1] (Ω.interface i j) (Ω.interface i' j') := by
  refine measure_mono_null (fun x hx => ?_)
    (ae_iff.1 (Ω.ae_notMem_reducedBoundary_cell_of_mem_interface hW hn))
  obtain ⟨hx, hi', hj'⟩ := hx
  simp only [mem_ofPred_eq, not_forall, not_not]
  rw [Ne, Sym2.eq_iff, not_or, not_and, not_and] at hne
  by_cases hii : i = i'
  · subst hii
    exact ⟨j, j', i, hne.1 rfl, hij.symm, hi'j'.symm, mem_interface.2 ⟨(mem_interface.1 hx).2, hj'⟩,
      (mem_interface.1 hx).1⟩
  by_cases hji : j = i'
  · subst hji
    have hj'i : j' ≠ i := fun h => hne.2 h.symm rfl
    exact ⟨i, j, j', hij, hj'i.symm, hi'j', hx, hj'⟩
  · exact ⟨i, i', j, hii, hij, fun h => hji h.symm, mem_interface.2 ⟨(mem_interface.1 hx).1, hi'⟩,
      (mem_interface.1 hx).2⟩

/-- For a `C¹` weight, in dimension `n ≥ 2`, the reduced boundary of a union of cells
`⋃_{i ∈ S} Ω_i` is `Hⁿ⁻¹`-almost everywhere the union of the interfaces `Σ_ij` with `i ∈ S` and
`j ∉ S`. -/
theorem reducedBoundary_biUnion_cell_ae_eq (hW : ContDiff ℝ 1 W) (hn : 2 ≤ finrank ℝ E)
    (Ω : Cluster W q) (S : Finset (Fin q)) :
    reducedBoundary volume ⊤ (⋃ i ∈ S, Ω.cell i) =ᵐ[μHE[finrank ℝ E - 1]]
      ⋃ p ∈ S ×ˢ Sᶜ, Ω.interface p.1 p.2 := by
  simp only [interface_def]
  exact reducedBoundary_biUnion_ae_eq hn Ω.nullMeasurableSet_cell
    (fun i j hij => (Ω.pairwise_disjoint hij).aedisjoint) Ω.volume_compl_iUnion
    (Ω.exists_totalVariationOn_indicator_cell_ne_top hW) S
    (exists_totalVariationOn_indicator_ne_top_of_weightedPerimeter_ne_top hW
      ((Ω.nullMeasurableSet_biUnion_cell S).mono Measure.restrict_le_self)
      (Ω.weightedPerimeter_biUnion_cell_lt_top hW S).ne)

/-- For a `C¹` weight, in dimension `n ≥ 2`, `Hⁿ⁻¹`-almost every point of the reduced boundary
`∂*Ω_i` of a cell lies on exactly one interface `Σ_ij` with `j ≠ i`. -/
theorem ae_existsUnique_mem_interface_of_mem_reducedBoundary_cell (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (Ω : Cluster W q) (i : Fin q) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], x ∈ reducedBoundary volume ⊤ (Ω.cell i) →
      ∃! j, j ≠ i ∧ x ∈ Ω.interface i j := by
  filter_upwards [ae_existsUnique_mem_reducedBoundary_of_mem_reducedBoundary_biUnion hn
    Ω.nullMeasurableSet_cell (fun i j hij => (Ω.pairwise_disjoint hij).aedisjoint)
    Ω.volume_compl_iUnion (Ω.exists_totalVariationOn_indicator_cell_ne_top hW) {i}] with x hx hxi
  rw [Finset.set_biUnion_singleton] at hx
  obtain ⟨⟨k, j⟩, ⟨hk, hj, hxk, hxj⟩, huniq⟩ := hx hxi
  rw [Finset.mem_singleton] at hk hj
  subst hk
  refine ⟨j, ⟨hj, mem_interface.2 ⟨hxk, hxj⟩⟩, fun j' ⟨hj', hxj'⟩ => ?_⟩
  exact congrArg Prod.snd
    (huniq (k, j') ⟨Finset.mem_singleton_self k, by simpa using hj', (mem_interface.1 hxj').1,
      (mem_interface.1 hxj').2⟩)

/-- **The perimeter of a union of cells is the area of its interfaces with the other cells.**
For a `C¹` weight, in dimension `n ≥ 2`, `P_μ(⋃_{i ∈ S} Ω_i) = Σ_{i ∈ S} Σ_{j ∉ S} A_ij`. -/
theorem weightedPerimeter_biUnion_cell_eq_sum_interfaceArea (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (Ω : Cluster W q) (S : Finset (Fin q)) :
    weightedPerimeter W ⊤ (⋃ i ∈ S, Ω.cell i) = ∑ i ∈ S, ∑ j ∈ Sᶜ, Ω.interfaceArea i j := by
  rw [weightedPerimeter_eq_lintegral_reducedBoundary_of_ne_top hW hn
      ((Ω.nullMeasurableSet_biUnion_cell S).mono Measure.restrict_le_self)
      (Ω.weightedPerimeter_biUnion_cell_lt_top hW S).ne,
    setLIntegral_congr (Ω.reducedBoundary_biUnion_cell_ae_eq hW hn S),
    lintegral_biUnion_finset₀ ?_ fun p _ => (Ω.measurableSet_interface p.1 p.2).nullMeasurableSet,
    Finset.sum_product]
  · simp only [interfaceArea_def]
  · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' hne
    simp only [Finset.coe_product, mem_prod, Finset.mem_coe, Finset.mem_compl] at hp hp'
    refine Ω.aedisjoint_interface hW hn (fun h : i = j => hp.2 (h ▸ hp.1))
      (fun h : i' = j' => hp'.2 (h ▸ hp'.1)) ?_
    rw [Ne, Sym2.eq_iff]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hne rfl
    · exact hp'.2 hp.1

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
  rw [perimeter_def]
  simp_rw [weightedPerimeter_cell_eq_sum_interfaceArea hW hn, Finset.compl_singleton,
    Finset.sum_erase_univ_eq_sum_Ioi_add_sum_Iio, Finset.sum_add_distrib,
    Finset.sum_sum_Iio_eq_sum_sum_Ioi]
  simp_rw [interfaceArea_comm Ω]
  rw [← two_mul, mul_comm]
  exact ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top

end Cluster

end TauCeti
