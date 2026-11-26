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

Almost no point lies on the reduced boundaries of three distinct cells
(`TauCeti.ae_notMem_reducedBoundary_of_mem_reducedBoundary_of_mem_reducedBoundary`), and if the
union `⋃_{i ∈ S} s i` also has locally finite perimeter, its reduced boundary is, up to an
`Hⁿ⁻¹`-null set, the union of the interfaces `∂*s i ∩ ∂*s j` with `i ∈ S`, `j ∉ S`
(`TauCeti.reducedBoundary_biUnion_ae_eq`): at a point of such an interface the cells `s i` and
`s j` have density `1/2`, so all other cells have density `0` and the union has density `1/2`.

This is the set-level form of the interface decomposition of the boundary of a cluster, before it
is specialised to clusters (`TauCeti.Cluster.weightedPerimeter_biUnion_cell_eq_sum_interfaceArea`).

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

/-- If values indexed by a finite type add up to `1` and two distinct ones are `1/2`, all the
others vanish. -/
private theorem eq_zero_of_sum_eq_one_of_eq_half {ι : Type*} [Fintype ι] {d : ι → ℝ≥0∞}
    (hsum : ∑ l, d l = 1) {i j k : ι} (hi : d i = 1 / 2) (hj : d j = 1 / 2) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) : d k = 0 := by
  classical
  have h3 : ∑ l ∈ ({k, i, j} : Finset ι), d l ≤ ∑ l, d l :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => bot_le
  rw [Finset.sum_insert (by simp [hki, hkj]), Finset.sum_pair hij, hsum, hi, hj,
    ENNReal.add_halves, add_comm] at h3
  by_contra hk
  exact absurd h3 (not_le.2 (ENNReal.lt_add_right ENNReal.one_ne_top hk))

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
  have hall : ∑ i, d i = 1 := sum_eq_one_of_hasDensityAt hm hd hcov hdens
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

/-- **No triple points.** Under the hypotheses of
`TauCeti.ae_existsUnique_mem_reducedBoundary_of_mem_reducedBoundary_biUnion`, `Hⁿ⁻¹`-almost no
point lies in the reduced boundaries of three distinct cells. -/
theorem ae_notMem_reducedBoundary_of_mem_reducedBoundary_of_mem_reducedBoundary [Finite ι]
    (hn : 2 ≤ finrank ℝ E) (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hd : ∀ i j, i ≠ j → AEDisjoint μ (s i) (s j))
    (hcov : μ (⋃ i, s i)ᶜ = 0)
    (hfin : ∀ i K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U ((s i).indicator 1) ≠ ∞) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      x ∈ reducedBoundary μ Ω (s i) → x ∈ reducedBoundary μ Ω (s j) →
        x ∉ reducedBoundary μ Ω (s k) := by
  classical
  have := Fintype.ofFinite ι
  have hu (i : ι) : LocallyIntegrableOn ((s i).indicator (1 : E → ℝ)) Ω μ :=
    locallyIntegrableOn_indicator_const ((hm i).mono Measure.restrict_le_self) 1
  filter_upwards [ae_forall_exists_hasDensityAt hn hu hfin] with x hx i j k hij hik hjk hi hj hk
  choose d _ hdens hdhalf using hx (reducedBoundary_subset hi)
  have h0 := eq_zero_of_sum_eq_one_of_eq_half (sum_eq_one_of_hasDensityAt hm hd hcov hdens)
    ((hdhalf i).2 hi) ((hdhalf j).2 hj) hij hik.symm hjk.symm
  rw [(hdhalf k).2 hk] at h0
  exact absurd h0 (by simp)

/-- **The reduced boundary of a union of cells is the union of its interfaces.** Under the
hypotheses of `TauCeti.ae_existsUnique_mem_reducedBoundary_of_mem_reducedBoundary_biUnion`, if
the union `⋃_{i ∈ S} s i` also has locally finite perimeter in `Ω`, then up to an `Hⁿ⁻¹`-null set
its reduced boundary is the union of the interfaces `∂*s i ∩ ∂*s j`, `i ∈ S`, `j ∉ S`. -/
theorem reducedBoundary_biUnion_ae_eq [Fintype ι] [DecidableEq ι]
    (hn : 2 ≤ finrank ℝ E) (hm : ∀ i, NullMeasurableSet (s i) μ)
    (hd : ∀ i j, i ≠ j → AEDisjoint μ (s i) (s j))
    (hcov : μ (⋃ i, s i)ᶜ = 0)
    (hfin : ∀ i K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U ((s i).indicator 1) ≠ ∞)
    (S : Finset ι)
    (hfinS : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U ((⋃ i ∈ S, s i).indicator 1) ≠ ∞) :
    reducedBoundary μ Ω (⋃ i ∈ S, s i) =ᵐ[μHE[finrank ℝ E - 1]]
      ⋃ p ∈ S ×ˢ Sᶜ, reducedBoundary μ Ω (s p.1) ∩ reducedBoundary μ Ω (s p.2) := by
  have hu (i : ι) : LocallyIntegrableOn ((s i).indicator (1 : E → ℝ)) Ω μ :=
    locallyIntegrableOn_indicator_const ((hm i).mono Measure.restrict_le_self) 1
  have hmS : NullMeasurableSet (⋃ i ∈ S, s i) μ :=
    .biUnion (Finset.countable_toSet S) fun i _ => hm i
  have huS : LocallyIntegrableOn ((⋃ i ∈ S, s i).indicator (1 : E → ℝ)) Ω μ :=
    locallyIntegrableOn_indicator_const (hmS.mono Measure.restrict_le_self) 1
  refine EventuallySubset.antisymm (eventuallySubset_iff.2 ?_) (eventuallySubset_iff.2 ?_)
  · filter_upwards [ae_existsUnique_mem_reducedBoundary_of_mem_reducedBoundary_biUnion hn hm hd
      hcov hfin S] with x hx hxS
    obtain ⟨⟨i, j⟩, ⟨hi, hj, hxi, hxj⟩, -⟩ := hx hxS
    exact mem_biUnion (x := (i, j)) (Finset.mem_product.2 ⟨hi, Finset.mem_compl.2 hj⟩) ⟨hxi, hxj⟩
  · filter_upwards [ae_forall_exists_hasDensityAt hn hu hfin,
      essentialBoundary_inter_ae_eq_reducedBoundary hn huS hfinS] with x hx hess hxI
    obtain ⟨⟨i, j⟩, hp, hxi, hxj⟩ := mem_iUnion₂.1 hxI
    obtain ⟨hi, hj⟩ := Finset.mem_product.1 hp
    rw [Finset.mem_compl] at hj
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    choose d _ hdens hdhalf using hx (reducedBoundary_subset hxi)
    -- the densities of `s i` and `s j` are `1/2`, so all other cells have density `0`
    have hdi := (hdhalf i).2 hxi
    have hzero (k : ι) (hki : k ≠ i) (hkj : k ≠ j) : d k = 0 :=
      eq_zero_of_sum_eq_one_of_eq_half (sum_eq_one_of_hasDensityAt hm hd hcov hdens) hdi
        ((hdhalf j).2 hxj) hij hki hkj
    have hsum : ∑ k ∈ S, d k = 1 / 2 := by
      rw [Finset.sum_eq_single_of_mem i hi fun k hk hki => hzero k hki fun h => hj (h ▸ hk), hdi]
    have hdensS : HasDensityAt μ (⋃ i ∈ S, s i) x (1 / 2) :=
      hsum ▸ HasDensityAt.biUnion_finset (fun k _ => hdens k) (fun k _ l _ => hd k l)
        fun k _ => hm k
    have hmem : x ∈ essentialBoundary μ (⋃ i ∈ S, s i) ∩ Ω :=
      ⟨mem_essentialBoundary.2 ⟨fun h => absurd (hdensS.unique (mem_essentialInterior.1 h))
        (ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top).ne,
        fun h => absurd (hdensS.unique (mem_essentialExterior.1 h)) (by simp)⟩,
        reducedBoundary_subset hxi⟩
    exact hess.1 hmem

end TauCeti
