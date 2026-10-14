/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
public import TauCeti.Topology.Connected.PathConnected
public import Mathlib.Topology.Sets.Opens
import Mathlib.Data.Nat.SuccPred

/-!
# Successive van Kampen pushouts

An ordered cover can be assembled one member at a time. Its partial unions give a tower
of fundamental groups, and adjoining a path-connected open member along a path-connected
overlap gives a pushout in groups. The overlap is with the entire preceding union, so no
common overlap or path-connected triple intersections are required.

The partial unions use Mathlib's `partialSups`. The binary union theorem keeps all four
maps as inclusion-induced maps. Applying `TauCeti.isPushout_fundamentalGroup_union` to
partial unions describes the actual successive amalgamations. Each step assumes path
connectedness of the preceding union, new member, and overlap, with the basepoint in the
overlap. Path connectedness of the preceding union can be obtained from
`TauCeti.isPathConnected_partialSups`, using `map_partialSups Opens.frameHom` to pass
between partial unions of subsets and of opens.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.2, Theorem 1.20.
* R. Brown, *Topology and Groupoids*, Chapters 6–7.
-/

public section

noncomputable section

open CategoryTheory Set Topology TopologicalSpace

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- **Successive amalgamation for an ordered open cover.** At each step the fundamental
group of the next partial union is the pushout of the preceding group's inclusion and
the new member's inclusion over their actual overlap. The preceding union, new member, and
overlap must be path connected, and the overlap must contain the basepoint. No triple-overlap
assumption is used. -/
theorem isPushout_fundamentalGroup_partialSups (U : ℕ → Opens X) (n : ℕ) (x : X)
    (hxP : x ∈ partialSups U n) (hxN : x ∈ U (n + 1))
    (hP : IsPathConnected (partialSups U n : Set X))
    (hN : IsPathConnected (U (n + 1) : Set X))
    (hAB : IsPathConnected ((partialSups U n : Set X) ∩ (U (n + 1) : Set X))) :
    IsPushout
      (GrpCat.ofHom (_root_.FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (⟨x, hxP, hxN⟩ :
          ↥((partialSups U n : Set X) ∩ (U (n + 1) : Set X)))))
      (GrpCat.ofHom (_root_.FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        (⟨x, hxP, hxN⟩ :
          ↥((partialSups U n : Set X) ∩ (U (n + 1) : Set X)))))
      (GrpCat.ofHom (_root_.FundamentalGroup.map
        (ContinuousMap.inclusion ((partialSups U).monotone (Nat.le_succ n)))
        (⟨x, hxP⟩ : partialSups U n)))
      (GrpCat.ofHom (_root_.FundamentalGroup.map
        (ContinuousMap.inclusion (le_partialSups U (n + 1)))
        (⟨x, hxN⟩ : U (n + 1)))) := by
  have hStep : (partialSups U (n + 1) : Set X) =
      (partialSups U n : Set X) ∪ (U (n + 1) : Set X) := by
    have h : partialSups U (n + 1) = partialSups U n ⊔ U (n + 1) := partialSups_succ U n
    exact congrArg (fun V : Opens X => (V : Set X)) h
  exact isPushout_fundamentalGroup_union hStep (partialSups U n).isOpen (U (n + 1)).isOpen
    hP hN hAB x hxP hxN

/-- For a finite ordered cover, the last successive amalgamation has the ambient
fundamental group as its pushout vertex. Together with
`isPushout_fundamentalGroup_partialSups`, applied at each step whose preceding union, new
member, and overlap are path connected and whose overlap contains the basepoint, this computes
`π₁(X, x)` by iterated pushouts along successive overlaps. -/
theorem isPushout_fundamentalGroup_partialSups_of_eq_top (U : ℕ → Opens X) (n : ℕ) (x : X)
    (hxP : x ∈ partialSups U n) (hxN : x ∈ U (n + 1))
    (hP : IsPathConnected (partialSups U n : Set X))
    (hN : IsPathConnected (U (n + 1) : Set X))
    (hAB : IsPathConnected ((partialSups U n : Set X) ∩ (U (n + 1) : Set X)))
    (hCover : partialSups U (n + 1) = ⊤) :
    IsPushout
      (GrpCat.ofHom (_root_.FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (⟨x, hxP, hxN⟩ :
          ↥((partialSups U n : Set X) ∩ (U (n + 1) : Set X)))))
      (GrpCat.ofHom (_root_.FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        (⟨x, hxP, hxN⟩ :
          ↥((partialSups U n : Set X) ∩ (U (n + 1) : Set X)))))
      (GrpCat.ofHom (_root_.FundamentalGroup.map
        (ContinuousMap.subtypeVal (partialSups U n : Set X))
        (⟨x, hxP⟩ : partialSups U n)))
      (GrpCat.ofHom (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal (U (n + 1) : Set X))
        (⟨x, hxN⟩ : U (n + 1)))) := by
  have hUnion : (partialSups U n : Set X) ∪ (U (n + 1) : Set X) = univ := by
    have hStep : partialSups U (n + 1) = partialSups U n ⊔ U (n + 1) := partialSups_succ U n
    simpa only [hStep, Opens.coe_sup, Opens.coe_top] using
      congrArg (fun V : Opens X => (V : Set X)) hCover
  have hInterior : interior (partialSups U n : Set X) ∪
      interior (U (n + 1) : Set X) = univ := by
    rwa [(partialSups U n).isOpen.interior_eq, (U (n + 1)).isOpen.interior_eq]
  exact isPushout_fundamentalGroup hInterior hP hN hAB hxP hxN

end TauCeti
