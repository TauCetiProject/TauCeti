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

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- **A relative CW complex is a quotient of its base and its closed cells.**  The map from the
disjoint union of the base `D` and of one closed unit ball for every cell, given by the inclusion
of `D` and by the characteristic maps, is a quotient map onto `C`. -/
theorem isQuotientMap_sumElim_base_map :
    IsQuotientMap (Sum.elim (fun d : D ↦ (⟨d, base_subset_complex d.2⟩ : C))
      fun p : Σ m : Σ n, cell C n, closedBall (0 : Fin m.1 → ℝ) 1 ↦
        (⟨map p.1.1 p.1.2 p.2, closedCell_subset_complex p.1.1 p.1.2 ⟨p.2, p.2.2, rfl⟩⟩ : C)) := by
  refine isQuotientMap_iff_isClosed.2 ⟨?_, fun s ↦ ⟨fun hs ↦ hs.preimage ?_, fun hs ↦ ?_⟩⟩
  · rintro ⟨x, hx⟩
    rw [← union (C := C)] at hx
    obtain hx | hx := hx
    · exact ⟨.inl ⟨x, hx⟩, rfl⟩
    · obtain ⟨n, j, y, hy, rfl⟩ : ∃ n j, x ∈ closedCell n j := by
        simpa only [mem_iUnion] using hx
      exact ⟨.inr ⟨⟨n, j⟩, ⟨y, hy⟩⟩, rfl⟩
  · refine continuous_sum_dom.2 ⟨continuous_subtype_val.subtype_mk _, continuous_sigma fun m ↦ ?_⟩
    exact ((continuousOn m.1 m.2).comp_continuous continuous_subtype_val
      fun y ↦ y.2).subtype_mk _
  -- It remains to see that `s` is closed when its preimage is: by the weak-topology axiom, it
  -- suffices that its image in `X` meets the base and every closed cell in a closed set.
  have hsub : ((↑) '' s : Set X) ⊆ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  rw [← preimage_image_eq s Subtype.val_injective]
  refine IsClosed.preimage continuous_subtype_val <| (RelCWComplex.closed C _ hsub).2 ⟨?_, ?_⟩
  · intro n j
    have hK : IsClosed {y : closedBall (0 : Fin n → ℝ) 1 |
        (⟨map n j y, closedCell_subset_complex n j ⟨y, y.2, rfl⟩⟩ : C) ∈ s} :=
      hs.preimage (continuous_inr.comp (continuous_sigmaMk (σ := fun m : Σ n, cell C n ↦
        closedBall (0 : Fin m.1 → ℝ) 1) (i := ⟨n, j⟩)))
    have hcpt := (isCompact_iff_compactSpace.1 (isCompact_closedBall (0 : Fin n → ℝ) 1))
    convert (hK.isCompact.image ((continuousOn n j).comp_continuous continuous_subtype_val
      fun y ↦ y.2)).isClosed using 1
    ext x
    constructor
    · rintro ⟨⟨⟨x, hxC⟩, hxs, rfl⟩, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, hxs, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨_, hy, rfl⟩, y, y.2, rfl⟩
  · have hK : IsClosed {d : D | (⟨d, base_subset_complex d.2⟩ : C) ∈ s} :=
      hs.preimage continuous_inl
    convert (isClosedBase C).isClosedMap_subtype_val _ hK using 1
    ext x
    constructor
    · rintro ⟨⟨x, hxs, rfl⟩, hx⟩
      exact ⟨⟨x, hx⟩, hxs, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨_, hd, rfl⟩, d.2⟩

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
  · exact (((continuousOn n j).comp_continuous continuous_subtype_val fun y ↦ y.2).comp
      continuous_snd).subtype_mk _
  -- Split the product of `Z` with the disjoint union of the base and the closed cells into the
  -- products of `Z` with the summands.
  rw [← Homeomorph.prodSumDistrib.symm.comp_continuous_iff', continuous_sum_dom]
  refine ⟨hbase, ?_⟩
  rw [← (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib |>.symm.comp_continuous_iff',
    continuous_sigma_iff]
  exact fun m ↦ (hcell m.1 m.2).comp continuous_swap

end TauCeti
