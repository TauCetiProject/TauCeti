/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Independence
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Fundamental cycle bases of spanning forests

Restriction to the chords of a spanning forest identifies the incidence kernel with the
free module on those chords. The inverse of restriction constructs the fundamental cycles:
a chord traversed forward, completed by a chain in the forest returning to its source.
Their chord coordinates are unit vectors, and the coefficients in any cycle expansion are
exactly its chord coordinates.

The construction works over any ring, for infinite as well as finite graphs, without an
orientation or connectedness assumption. In particular it supplies bases of the integral
cycle lattice and the binary cycle space, retaining loops and distinct parallel edges. For finite
graphs the resulting rank is the number of edges minus the number of vertices plus the number
of components; the theorem states this additively to avoid truncated subtraction.

## References

* R. Diestel, *Graph Theory*, §1.9 (fundamental cycle bases).
* A. Hatcher, *Algebraic Topology*, §2.2 (signed incidence boundaries).
-/

public section

namespace TauCeti.SerreGraph

variable {Γ : SerreGraph} {O F : Set Γ.E} {R : Type*} [Ring R]

/-- The difference of two vertex unit chains is a boundary whenever the vertices are
connected in the support graph. No acyclicity hypothesis is needed. -/
theorem single_sub_single_mem_range_incidenceBoundary {a b : Γ.V}
    (h : (Γ.supportGraph F).Reachable a b) :
    Finsupp.single b (1 : R) - Finsupp.single a 1 ∈
      LinearMap.range (Γ.incidenceBoundary F R) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    have hedge : Finsupp.single b (1 : R) - Finsupp.single a 1 ∈
        LinearMap.range (Γ.incidenceBoundary F R) := by
      rcases (Γ.supportGraph_adj F a b).mp hab with ⟨-, h | h⟩
      · obtain ⟨e, he, rfl, rfl⟩ := h
        exact ⟨Finsupp.single ⟨e, he⟩ 1, by simp⟩
      · obtain ⟨e, he, rfl, rfl⟩ := h
        exact ⟨-Finsupp.single ⟨e, he⟩ 1, by simp [neg_sub]⟩
    convert (LinearMap.range (Γ.incidenceBoundary F R)).add_mem ih hedge using 1
    exact (sub_add_sub_cancel _ _ _).symm

/-- Chord coordinates of a cycle, as a finitely supported function on the actual non-forest
darts. This map does not require that `F` be a forest. -/
noncomputable def cycleChordCoordinates (Γ : SerreGraph) (O F : Set Γ.E) (R : Type*) [Ring R] :
    (Γ.incidenceBoundary O R).ker →ₗ[R] (↥(O \ F) →₀ R) :=
  (Finsupp.lcomapDomain (Set.inclusion Set.sdiff_subset)
    (Set.inclusion_injective Set.sdiff_subset)).comp (Γ.incidenceBoundary O R).ker.subtype

@[simp] theorem cycleChordCoordinates_apply (c : (Γ.incidenceBoundary O R).ker)
    (e : ↥(O \ F)) : Γ.cycleChordCoordinates O F R c e = c.val ⟨e.val, e.property.1⟩ := by
  simp [cycleChordCoordinates, Finsupp.lcomapDomain, Finsupp.comapDomain_apply]

/-- A forest admits a cycle with any specified unit chord coordinate. Its other nonzero
coordinates are forest edges, so it is the chord completed by its forest return chain. -/
private theorem IsSpanningForest.exists_cycle_chord (hF : Γ.IsSpanningForest O F)
    (e : ↥(O \ F)) :
    ∃ c : (Γ.incidenceBoundary O R).ker,
      Γ.cycleChordCoordinates O F R c = Finsupp.single e 1 := by
  classical
  have hreach : (Γ.supportGraph F).Reachable (Γ.src e.val) (Γ.tgt e.val) := by
    rw [hF.reachable_eq]
    by_cases h : Γ.src e.val = Γ.tgt e.val
    · rw [h]
    · exact ((Γ.supportGraph_adj O _ _).mpr
        ⟨h, Or.inl ⟨e.val, e.property.1, rfl, rfl⟩⟩).reachable
  obtain ⟨b, hb⟩ := single_sub_single_mem_range_incidenceBoundary (R := R) hreach
  let c : O →₀ R := Finsupp.single ⟨e.val, e.property.1⟩ 1 -
    Finsupp.mapDomain (Set.inclusion hF.subset) b
  have hc : Γ.incidenceBoundary O R c = 0 := by
    simp only [c, map_sub, incidenceBoundary_single, one_smul,
      incidenceBoundary_mapDomain_inclusion, hb, sub_self]
  refine ⟨⟨c, hc⟩, ?_⟩
  ext f
  have hnot : (⟨f.val, f.property.1⟩ : O) ∉ Set.range (Set.inclusion hF.subset) := by
    rintro ⟨g, hg⟩
    exact f.property.2 (congrArg Subtype.val hg ▸ g.property)
  simp only [cycleChordCoordinates_apply, c, Finsupp.sub_apply,
    Finsupp.mapDomain_of_notMem_range b _ hnot, sub_zero, Finsupp.single_apply]
  congr 1
  simp only [Subtype.ext_iff]

/-- Restriction to chords is injective on cycles: a forest supports no nonzero cycle. -/
theorem IsSpanningForest.cycleChordCoordinates_injective (hF : Γ.IsSpanningForest O F) :
    Function.Injective (Γ.cycleChordCoordinates O F R) := by
  intro c d h
  apply Subtype.ext
  apply hF.eq_of_incidenceBoundary_eq_of_forall_notMem c.val d.val
    ((LinearMap.mem_ker.mp c.property).trans (LinearMap.mem_ker.mp d.property).symm)
  intro e he
  exact congrArg (fun f => f ⟨e.val, e.property, he⟩) h

/-- Every finite chord assignment extends to a cycle, without any finiteness assumption
on the graph. -/
theorem IsSpanningForest.cycleChordCoordinates_surjective (hF : Γ.IsSpanningForest O F) :
    Function.Surjective (Γ.cycleChordCoordinates O F R) := by
  classical
  intro c
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add c d hc hd =>
    obtain ⟨c, rfl⟩ := hc
    obtain ⟨d, rfl⟩ := hd
    exact ⟨c + d, map_add _ _ _⟩
  | single e r =>
    obtain ⟨c, hc⟩ := hF.exists_cycle_chord (R := R) e
    exact ⟨r • c, by simp [hc]⟩

/-- Chord restriction identifies cycles with the free module on the non-forest darts.
The inverse uniquely completes each chord assignment by forest coordinates. -/
noncomputable def IsSpanningForest.cycleEquiv (hF : Γ.IsSpanningForest O F) (R : Type*)
    [Ring R] : (Γ.incidenceBoundary O R).ker ≃ₗ[R] (↥(O \ F) →₀ R) :=
  LinearEquiv.ofBijective (Γ.cycleChordCoordinates O F R)
    ⟨hF.cycleChordCoordinates_injective, hF.cycleChordCoordinates_surjective⟩

@[simp] theorem IsSpanningForest.cycleEquiv_apply (hF : Γ.IsSpanningForest O F)
    (c : (Γ.incidenceBoundary O R).ker) (e : ↥(O \ F)) :
    hF.cycleEquiv R c e = c.val ⟨e.val, e.property.1⟩ :=
  cycleChordCoordinates_apply c e

/-- Completing a chord assignment preserves precisely its prescribed chord coordinates. -/
@[simp] theorem IsSpanningForest.cycleEquiv_symm_apply (hF : Γ.IsSpanningForest O F)
    (c : ↥(O \ F) →₀ R) (e : ↥(O \ F)) :
    ((hF.cycleEquiv R).symm c).val ⟨e.val, e.property.1⟩ = c e := by
  rw [← hF.cycleEquiv_apply, LinearEquiv.apply_symm_apply]

/-- Fundamental cycles, indexed by actual chords, form a basis of the incidence kernel.
Specializing the ring to `ℤ` gives the integral lattice basis, and to `ZMod 2` gives the
binary cycle basis. -/
noncomputable def IsSpanningForest.cycleBasis (hF : Γ.IsSpanningForest O F) (R : Type*)
    [Ring R] : Module.Basis ↥(O \ F) R (Γ.incidenceBoundary O R).ker :=
  Module.Basis.ofRepr (hF.cycleEquiv R)

/-- The coefficient of a fundamental cycle in an arbitrary cycle is its chord coordinate. -/
@[simp] theorem IsSpanningForest.cycleBasis_repr (hF : Γ.IsSpanningForest O F)
    (c : (Γ.incidenceBoundary O R).ker) (e : ↥(O \ F)) :
    (hF.cycleBasis R).repr c e = c.val ⟨e.val, e.property.1⟩ :=
  hF.cycleEquiv_apply c e

/-- Fundamental cycles have unit chord coordinates. In particular the cycle of a loop
retains that loop's coefficient rather than discarding it. -/
@[simp] theorem IsSpanningForest.cycleBasis_apply_chord (hF : Γ.IsSpanningForest O F)
    (e f : ↥(O \ F)) :
    (hF.cycleBasis R e).val ⟨f.val, f.property.1⟩ = Finsupp.single e (1 : R) f := by
  rw [← hF.cycleBasis_repr]
  simp

/-- The fundamental cycle of a loop is the unit chain on that loop: no forest edge is
needed to return to its source. -/
@[simp] theorem IsSpanningForest.cycleBasis_of_loop (hF : Γ.IsSpanningForest O F)
    (e : ↥(O \ F)) (he : Γ.src e.val = Γ.tgt e.val) :
    (hF.cycleBasis R e).val = Finsupp.single ⟨e.val, e.property.1⟩ 1 := by
  classical
  apply hF.eq_of_incidenceBoundary_eq_of_forall_notMem
  · exact (LinearMap.mem_ker.mp (hF.cycleBasis R e).property).trans
      (incidenceBoundary_single_eq_zero_of_loop R ⟨e.val, e.property.1⟩ he).symm
  · intro f hf
    simpa [Finsupp.single_apply, Subtype.ext_iff] using
      hF.cycleBasis_apply_chord (R := R) e ⟨f.val, f.property, hf⟩

/- The basis supplies freeness via `Module.Free.of_basis`, and, for finite chord sets,
finite generation via `Module.Finite.of_basis`; no additional module structure is needed. -/

/-- The cycle rank plus the number of vertices equals the number of actual edges plus
the number of components. This applies to disconnected and empty graphs, integral cycles,
and binary cycles. Only finitely many vertices and chosen darts are required. -/
theorem finrank_ker_incidenceBoundary_add_card [StrongRankCondition R]
    [Finite Γ.V] [Finite O] :
    Module.finrank R (Γ.incidenceBoundary O R).ker + Nat.card Γ.V =
      Nat.card O + Nat.card (Γ.supportGraph O).ConnectedComponent := by
  obtain ⟨F, hF⟩ := Γ.exists_spanningForest O
  rw [Module.finrank_eq_nat_card_basis (hF.cycleBasis R)]
  have hforest := hF.card_add_card_connectedComponent
  have hchord := Set.ncard_sdiff_add_ncard_of_subset hF.subset (Set.toFinite O)
  simp only [Nat.card_coe_set_eq] at hforest ⊢
  omega

end TauCeti.SerreGraph
