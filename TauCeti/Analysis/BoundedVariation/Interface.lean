/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.EssentialBoundary
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Interfaces between the cells of a partition

Let `E` be a Euclidean space of dimension `n ≥ 2` with an additive Haar measure `μ`, and let
`(s i)_{i ∈ ι}` be finitely many pairwise almost disjoint null-measurable sets covering `E` up to
a null set, each of locally finite perimeter in an open set `Ω`. For every set `S` of indices,
`Hⁿ⁻¹`-almost every point of the reduced boundary of `⋃_{i ∈ S} s i` lies in the reduced boundaries
`∂*s i ∩ ∂*s j` for exactly one pair `i ∈ S`, `j ∉ S`
(`TauCeti.ae_existsUnique_mem_reducedBoundary_of_mem_reducedBoundary_biUnion`). For `S = {i}` this
says that almost every point of `∂*s i` lies on exactly one interface `∂*s i ∩ ∂*s j`.

The argument is by densities. Off an `Hⁿ⁻¹`-null set, every cell has density `0`, `1/2` or `1` at
each point of `Ω`, with density `1/2` exactly on its reduced boundary: at points of `∂*s i` the
density is `1/2` (`TauCeti.hasDensityAt_of_mem_reducedBoundary`), and off it, up to a null set,
the point lies outside the essential boundary
(`TauCeti.essentialBoundary_inter_ae_eq_reducedBoundary`), where the density is `0` or `1`.
Densities of almost disjoint sets add (`TauCeti.HasDensityAt.union`,
`TauCeti.HasDensityAt.biUnion_finset`), so at a point of the reduced boundary of
`⋃_{i ∈ S} s i` the densities of the cells in `S` add up to `1/2`, and those of the
other cells, the cells together having density `1`, add up to `1/2` as well. A sum of values in
`{0, 1/2, 1}` equal to `1/2` has exactly one term `1/2`.

This is the set-level form of the interface decomposition of the boundary of a cluster, before it
is specialised to clusters.

## References

* E. Milman and J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  195 (2022), equations (3.4)-(3.6).
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press (2012), Exercise 29.7.
-/

public section

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal Topology

namespace TauCeti

/-- If values in `{0, 1/2, 1}` indexed by a finite set add up to `1/2`, exactly one of them is
`1/2`. -/
private theorem existsUnique_eq_half_of_sum_eq_half {ι : Type*} {S : Finset ι} {d : ι → ℝ≥0∞}
    (hd : ∀ i ∈ S, d i = 0 ∨ d i = 1 / 2 ∨ d i = 1) (hsum : ∑ i ∈ S, d i = 1 / 2) :
    ∃! i, i ∈ S ∧ d i = 1 / 2 := by
  classical
  have hle (i : ι) (hi : i ∈ S) : d i ≤ 1 / 2 := hsum ▸ Finset.single_le_sum (fun _ _ => bot_le) hi
  have hlt : (1 / 2 : ℝ≥0∞) < 1 := ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top
  obtain ⟨i, hi, hdi⟩ : ∃ i ∈ S, d i = 1 / 2 := by
    by_contra! h
    have h0 : ∀ i ∈ S, d i = 0 := fun i hi => by
      rcases hd i hi with h' | h' | h'
      · exact h'
      · exact (h i hi h').elim
      · exact absurd (h' ▸ hle i hi) (not_le.2 hlt)
    rw [Finset.sum_eq_zero h0] at hsum
    exact absurd hsum.symm (by simp)
  refine ⟨i, ⟨hi, hdi⟩, fun j ⟨hj, hdj⟩ => ?_⟩
  by_contra hji
  have h2 : d i + d j ≤ ∑ k ∈ S, d k := by
    rw [← Finset.sum_pair (Ne.symm hji)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [Finset.insert_subset_iff, hi, hj])
      fun _ _ _ => bot_le
  rw [hdi, hdj, ENNReal.add_halves, hsum] at h2
  exact absurd h2 (not_le.2 hlt)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {ι : Type*} {s : ι → Set E}

/-- **The interfaces of a partition.** Let `E` have dimension `n ≥ 2`, and let `(s i)_{i ∈ ι}` be
finitely many pairwise almost disjoint null-measurable sets covering `E` up to a null set, each of
locally finite perimeter in an open set `Ω`. For every finite set `S` of indices,
`Hⁿ⁻¹`-almost every point of the reduced boundary of `⋃_{i ∈ S} s i` in `Ω` lies in
`∂*s i ∩ ∂*s j` for exactly one pair `i ∈ S`, `j ∉ S`. -/
theorem ae_existsUnique_mem_reducedBoundary_of_mem_reducedBoundary_biUnion [Finite ι]
    (hn : 2 ≤ finrank ℝ E) (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hd : ∀ i j, i ≠ j → AEDisjoint μ (s i) (s j))
    (hcov : μ (⋃ i, s i)ᶜ = 0)
    (hfin : ∀ i K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U ((s i).indicator 1) ≠ ∞)
    (S : Finset ι) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], x ∈ reducedBoundary μ Ω (⋃ i ∈ S, s i) →
      ∃! p : ι × ι, p.1 ∈ S ∧ p.2 ∉ S ∧
        x ∈ reducedBoundary μ Ω (s p.1) ∧ x ∈ reducedBoundary μ Ω (s p.2) := by
  classical
  have := Fintype.ofFinite ι
  -- The indicator of a null-measurable set is locally integrable.
  have hu (i : ι) : LocallyIntegrableOn ((s i).indicator (1 : E → ℝ)) Ω μ :=
    locallyIntegrableOn_indicator_const ((hm i).mono Measure.restrict_le_self) 1
  filter_upwards [ae_forall_exists_hasDensityAt hn hu hfin] with x hx hxS
  choose d hd01 hdens hdhalf using hx (reducedBoundary_subset hxS)
  -- The cells in `S` have densities adding up to `1/2`, all cells densities adding up to `1`.
  have hS : ∑ i ∈ S, d i = 1 / 2 :=
    (HasDensityAt.biUnion_finset (fun i _ => hdens i) (fun i _ j _ => hd i j)
      fun i _ => hm i).unique
      (hasDensityAt_of_mem_reducedBoundary hn hxS)
  have huniv : HasDensityAt μ (⋃ i ∈ (Finset.univ : Finset ι), s i) x 1 :=
    hasDensityAt_one_of_measure_compl_eq_zero (eventually_measure_closedBall_ne_zero_ne_top μ x)
      (by simpa using hcov)
  have hall : ∑ i, d i = 1 :=
    (HasDensityAt.biUnion_finset (fun i _ => hdens i) (fun i _ j _ => hd i j)
      fun i _ => hm i).unique
      huniv
  have hT : ∑ i ∈ Finset.univ.filter (· ∉ S), d i = 1 / 2 := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S) d
    have hfS : Finset.univ.filter (· ∈ S) = S := by
      ext
      simp
    rw [hfS, hall, hS, add_comm] at h
    rw [ENNReal.eq_sub_of_add_eq (by simp) h, one_div, ENNReal.one_sub_inv_two]
  obtain ⟨i, ⟨hi, hdi⟩, hi'⟩ := existsUnique_eq_half_of_sum_eq_half (fun i _ => hd01 i) hS
  obtain ⟨j, ⟨hj, hdj⟩, hj'⟩ := existsUnique_eq_half_of_sum_eq_half (fun i _ => hd01 i) hT
  refine ⟨(i, j), ⟨hi, (Finset.mem_filter.1 hj).2, (hdhalf i).1 hdi, (hdhalf j).1 hdj⟩, ?_⟩
  rintro ⟨i', j'⟩ ⟨hi'S, hj'S, hi'r, hj'r⟩
  simp only [Prod.mk.injEq]
  exact ⟨hi' i' ⟨hi'S, (hdhalf i').2 hi'r⟩,
    hj' j' ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hj'S⟩, (hdhalf j').2 hj'r⟩⟩

end TauCeti
