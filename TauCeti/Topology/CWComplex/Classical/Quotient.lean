/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.CompactOpen

/-!
# A CW complex is a quotient of its base and its closed cells

The weak-topology axiom of a relative CW complex `C` with base `D` says that a subset of `C` is
closed as soon as its intersections with `D` and with every closed cell are.  Equivalently, the
map from the disjoint union of `D` and of one closed unit ball for each cell, given by the
inclusion of `D` and by the characteristic maps, is a quotient map onto `C`.

Products with a locally compact space preserve quotient maps, so a map out of `Z × C`, for `Z`
locally compact, is continuous as soon as it is continuous on `Z × D` and on the product of `Z`
with every closed cell, the latter read through the characteristic maps.  This is how homotopies
out of a CW complex (the case `Z = I`) are built cell by cell.

## Main results

* `TauCeti.isQuotientMap_sumElim_base_map`: the base inclusion and the characteristic maps
  together form a quotient map onto the complex.
* `TauCeti.continuous_complex_iff`: a map out of a CW complex is continuous exactly when it is
  continuous on the base and along every characteristic map.
* `TauCeti.continuous_prod_complex_iff`: the same criterion for maps out of `Z × C` with `Z`
  locally compact.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and the Appendix "Topology of Cell Complexes": the topology of a CW complex is the
  quotient topology from its cells, and products with locally compact spaces.
-/

public section

open Metric Set Topology Topology.RelCWComplex

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- **A relative CW complex is a quotient of its base and its closed cells.**  The map from the
disjoint union of the base `D` and of one closed unit ball for every cell, given by the inclusion
of `D` and by the characteristic maps, is a quotient map onto `C`. -/
theorem isQuotientMap_sumElim_base_map :
    IsQuotientMap (Sum.elim (fun d : D ↦ (⟨d, base_subset_complex d.2⟩ : C))
      fun p : Σ m : Σ n, cell C n, closedBall (0 : Fin m.1 → ℝ) 1 ↦
        (⟨map p.1.1 p.1.2 p.2, closedCell_subset_complex p.1.1 p.1.2 ⟨p.2, p.2.2, rfl⟩⟩ : C)) := by
  refine isQuotientMap_iff_isClosed.2 ⟨?_, fun s ↦ ⟨fun hs ↦ hs.preimage ?_, fun hs ↦ ?_⟩⟩
  · rintro ⟨x, hx⟩
    simp_rw [← union (C := C), mem_union, mem_iUnion] at hx
    obtain hx | ⟨n, j, y, hy, rfl⟩ := hx
    · exact ⟨.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨.inr ⟨⟨n, j⟩, y, hy⟩, rfl⟩
  · exact continuous_sum_dom.2 ⟨continuous_subtype_val.subtype_mk _,
      continuous_sigma fun m ↦ (continuousOn m.1 m.2).domRestrict.subtype_mk _⟩
  -- It remains to see that `s` is closed when its preimage is. Write `s` as the trace on `C` of a
  -- subset `A` of `C`; by the weak-topology axiom, it suffices that `A` meets the base and every
  -- closed cell in a closed set, which are images of closed sets under closed maps.
  obtain ⟨A, hAC, rfl⟩ : ∃ A ⊆ C, s = (↑) ⁻¹' A :=
    ⟨_, Subtype.coe_image_subset C s, (preimage_image_eq s Subtype.val_injective).symm⟩
  refine ((RelCWComplex.closed C A hAC).2 ⟨fun n j ↦ ?_, ?_⟩).preimage continuous_subtype_val
  · rw [closedCell, ← range_domRestrict, ← image_preimage_eq_inter_range]
    exact (continuousOn n j).domRestrict.isClosedMap _ (hs.preimage (continuous_inr.comp
      (continuous_sigmaMk (σ := fun m : Σ n, cell C n ↦ closedBall (0 : Fin m.1 → ℝ) 1)
        (i := ⟨n, j⟩))))
  · rw [inter_comm, ← Subtype.image_preimage_coe]
    exact (isClosedBase C).isClosedMap_subtype_val _ (hs.preimage continuous_inl)

/-- A map out of a relative CW complex is continuous exactly when it is continuous on the base
and along the characteristic map of every cell. -/
theorem continuous_complex_iff {Y : Type*} [TopologicalSpace Y] {g : C → Y} :
    Continuous g ↔ (∀ n (j : cell C n), Continuous fun y : closedBall (0 : Fin n → ℝ) 1 ↦
        g ⟨map n j y, closedCell_subset_complex n j ⟨y, y.2, rfl⟩⟩) ∧
      Continuous fun d : D ↦ g ⟨d, base_subset_complex d.2⟩ := by
  rw [isQuotientMap_sumElim_base_map.continuous_iff, continuous_sum_dom, continuous_sigma_iff,
    and_comm]
  exact and_congr_left' ⟨fun h n j ↦ h ⟨n, j⟩, fun h m ↦ h m.1 m.2⟩

/-- **Continuity criterion for maps out of `Z × C`.**  For a locally compact space `Z`, a map out
of `Z × C` is continuous exactly when it is continuous on `Z × D` and on the product of `Z` with
every closed cell, the latter read through the characteristic maps.  For `Z = I` this builds
homotopies out of a CW complex cell by cell. -/
theorem continuous_prod_complex_iff {Z Y : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z]
    [TopologicalSpace Y] {g : Z × C → Y} :
    Continuous g ↔ (∀ n (j : cell C n), Continuous fun p : Z × closedBall (0 : Fin n → ℝ) 1 ↦
        g (p.1, ⟨map n j p.2, closedCell_subset_complex n j ⟨p.2, p.2.2, rfl⟩⟩)) ∧
      Continuous fun p : Z × D ↦ g (p.1, ⟨p.2, base_subset_complex p.2.2⟩) := by
  refine ⟨fun hg ↦ ⟨fun n j ↦ hg.comp (continuous_fst.prodMk ?_), hg.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _))⟩,
    fun ⟨hcell, hbase⟩ ↦ isQuotientMap_sumElim_base_map.continuous_lift_prod_right ?_⟩
  · exact ((continuousOn n j).domRestrict.comp continuous_snd).subtype_mk _
  -- Split the product of `Z` with the disjoint union of the base and the closed cells into the
  -- products of `Z` with the summands.
  rw [← Homeomorph.prodSumDistrib.symm.comp_continuous_iff', continuous_sum_dom]
  refine ⟨hbase, ?_⟩
  rw [← (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib |>.symm.comp_continuous_iff',
    continuous_sigma_iff]
  exact fun m ↦ (hcell m.1 m.2).comp continuous_swap

end TauCeti
