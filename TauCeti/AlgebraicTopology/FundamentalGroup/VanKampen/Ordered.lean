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
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Successive van Kampen pushouts

An ordered cover can be assembled one member at a time. Its partial unions give a tower
of fundamental groups, and adjoining a path-connected open member along a path-connected
overlap gives a pushout in groups. The overlap is with the entire preceding union, so no
common overlap or path-connected triple intersections are required.

The partial unions use Mathlib's `partialSups`. The binary union theorem keeps all four
maps as inclusion-induced maps. Applied to partial
unions, it describes the actual successive amalgamations rather than only an abstract
group presentation for the final space. The proof transports
`TauCeti.isPushout_fundamentalGroup` through the canonical subspace homeomorphisms.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.2, Theorem 1.20.
* R. Brown, *Topology and Groupoids*, Chapters 6–7.
-/

public section

noncomputable section

open CategoryTheory Set Topology TopologicalSpace

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- Based van Kampen for a union of two open subspaces. All the maps are induced by
inclusions, and neither inclusion from the overlap needs to induce an injective map. -/
theorem isPushout_fundamentalGroup_union {A B C : Set X} (hC : C = A ∪ B)
    (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsPathConnected (A ∩ B))
    (x : X) (hxA : x ∈ A) (hxB : x ∈ B) :
    IsPushout
      (GrpCat.ofHom (_root_.FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (⟨x, hxA, hxB⟩ : ↥(A ∩ B))))
      (GrpCat.ofHom (_root_.FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        (⟨x, hxA, hxB⟩ : ↥(A ∩ B))))
      (GrpCat.ofHom (_root_.FundamentalGroup.map
        (ContinuousMap.inclusion (hC.symm ▸ subset_union_left))
        (⟨x, hxA⟩ : A)))
      (GrpCat.ofHom (_root_.FundamentalGroup.map
        (ContinuousMap.inclusion (hC.symm ▸ subset_union_right))
        (⟨x, hxB⟩ : B))) := by
  subst C
  -- Apply van Kampen inside the union, then transport the three source carriers.
  -- The four compatibility checks retain the original inclusion-induced maps.
  let A' : Set ↥(A ∪ B) := Subtype.val ⁻¹' A
  let B' : Set ↥(A ∪ B) := Subtype.val ⁻¹' B
  let x' : ↥(A ∪ B) := ⟨x, Or.inl hxA⟩
  let eA : A' ≃ₜ A := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (fun a ha => ⟨⟨a, Or.inl ha⟩, rfl⟩)
  let eB : B' ≃ₜ B := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (fun b hb => ⟨⟨b, Or.inr hb⟩, rfl⟩)
  let eAB : ↥(A' ∩ B') ≃ₜ ↥(A ∩ B) :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange (s := A ∩ B)
      (fun a ha => ⟨(⟨a, Or.inl ha.1⟩ : ↥(A ∪ B)), rfl⟩)
  have hA' : IsPathConnected A' := by
    let := isPathConnected_iff_pathConnectedSpace.mp hA
    exact isPathConnected_iff_pathConnectedSpace.mpr eA.symm.pathConnectedSpace
  have hB' : IsPathConnected B' := by
    let := isPathConnected_iff_pathConnectedSpace.mp hB
    exact isPathConnected_iff_pathConnectedSpace.mpr eB.symm.pathConnectedSpace
  have hAB' : IsPathConnected (A' ∩ B') := by
    let := isPathConnected_iff_pathConnectedSpace.mp hAB
    exact isPathConnected_iff_pathConnectedSpace.mpr eAB.symm.pathConnectedSpace
  have hCover : interior A' ∪ interior B' = univ := by
    rw [(hAo.preimage continuous_subtype_val).interior_eq,
      (hBo.preimage continuous_subtype_val).interior_eq]
    ext z
    exact iff_of_true z.2 (mem_univ z)
  let iA : GrpCat.of (_root_.FundamentalGroup A' ⟨x', hxA⟩) ≅
      GrpCat.of (_root_.FundamentalGroup A ⟨x, hxA⟩) := (FundamentalGroup.homeomorphMulEquivOfEq eA
    (rfl : eA ⟨x', hxA⟩ = ⟨x, hxA⟩)).toGrpIso
  let iB : GrpCat.of (_root_.FundamentalGroup B' ⟨x', hxB⟩) ≅
      GrpCat.of (_root_.FundamentalGroup B ⟨x, hxB⟩) := (FundamentalGroup.homeomorphMulEquivOfEq eB
    (rfl : eB ⟨x', hxB⟩ = ⟨x, hxB⟩)).toGrpIso
  let iAB : GrpCat.of (_root_.FundamentalGroup ↥(A' ∩ B') ⟨x', hxA, hxB⟩) ≅
      GrpCat.of (_root_.FundamentalGroup ↥(A ∩ B) ⟨x, hxA, hxB⟩) :=
    (FundamentalGroup.homeomorphMulEquivOfEq eAB
    (rfl : eAB ⟨x', hxA, hxB⟩ = ⟨x, hxA, hxB⟩)).toGrpIso
  refine (isPushout_fundamentalGroup hCover hA' hB' hAB' hxA hxB).of_iso
    iAB iA iB (Iso.refl _) ?_ ?_ ?_ ?_
  · apply GrpCat.hom_ext
    ext g
    -- GrpCat and nested-subspace wrappers obstruct rewriting; pin the endpoint carriers.
    change _root_.FundamentalGroup.mapOfEq ⟨eA, eA.continuous⟩ rfl
      (_root_.FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (⟨x', hxA, hxB⟩ : ↥(A' ∩ B')) g) =
      _root_.FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (⟨x, hxA, hxB⟩ : ↥(A ∩ B))
        (_root_.FundamentalGroup.mapOfEq ⟨eAB, eAB.continuous⟩ rfl g)
    rw [FundamentalGroup.mapOfEq_rfl, FundamentalGroup.mapOfEq_rfl]
    have he : (⟨eA, eA.continuous⟩ : C(_, _)).comp
        (ContinuousMap.inclusion inter_subset_left) =
        (ContinuousMap.inclusion inter_subset_left).comp ⟨eAB, eAB.continuous⟩ := by
      ext z
      rfl
    have hl := FundamentalGroup.mapOfEq_comp ⟨eA, eA.continuous⟩
      (ContinuousMap.inclusion inter_subset_left) rfl rfl g
    have hr := FundamentalGroup.mapOfEq_comp (ContinuousMap.inclusion inter_subset_left)
      ⟨eAB, eAB.continuous⟩ rfl rfl g
    rw [FundamentalGroup.mapOfEq_rfl, FundamentalGroup.mapOfEq_rfl] at hl hr
    exact hl.trans ((FundamentalGroup.mapOfEq_congr he rfl rfl g).trans hr.symm)
  · apply GrpCat.hom_ext
    ext g
    -- GrpCat and nested-subspace wrappers obstruct rewriting; pin the endpoint carriers.
    change _root_.FundamentalGroup.mapOfEq ⟨eB, eB.continuous⟩ rfl
      (_root_.FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        (⟨x', hxA, hxB⟩ : ↥(A' ∩ B')) g) =
      _root_.FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        (⟨x, hxA, hxB⟩ : ↥(A ∩ B))
        (_root_.FundamentalGroup.mapOfEq ⟨eAB, eAB.continuous⟩ rfl g)
    rw [FundamentalGroup.mapOfEq_rfl, FundamentalGroup.mapOfEq_rfl]
    have he : (⟨eB, eB.continuous⟩ : C(_, _)).comp
        (ContinuousMap.inclusion inter_subset_right) =
        (ContinuousMap.inclusion inter_subset_right).comp ⟨eAB, eAB.continuous⟩ := by
      ext z
      rfl
    have hl := FundamentalGroup.mapOfEq_comp ⟨eB, eB.continuous⟩
      (ContinuousMap.inclusion inter_subset_right) rfl rfl g
    have hr := FundamentalGroup.mapOfEq_comp (ContinuousMap.inclusion inter_subset_right)
      ⟨eAB, eAB.continuous⟩ rfl rfl g
    rw [FundamentalGroup.mapOfEq_rfl, FundamentalGroup.mapOfEq_rfl] at hl hr
    exact hl.trans ((FundamentalGroup.mapOfEq_congr he rfl rfl g).trans hr.symm)
  · apply GrpCat.hom_ext
    ext g
    -- The wrappers spell the ambient basepoint differently; pin the shared subtype point.
    change _root_.FundamentalGroup.map (ContinuousMap.subtypeVal A') ⟨x', hxA⟩ g =
      _root_.FundamentalGroup.map (ContinuousMap.inclusion subset_union_left) (⟨x, hxA⟩ : A)
        (_root_.FundamentalGroup.mapOfEq ⟨eA, eA.continuous⟩ rfl g)
    rw [FundamentalGroup.mapOfEq_rfl]
    have h := FundamentalGroup.mapOfEq_comp
      (ContinuousMap.inclusion (t := A ∪ B) subset_union_left) ⟨eA, eA.continuous⟩ rfl rfl g
    rw [FundamentalGroup.mapOfEq_rfl, FundamentalGroup.mapOfEq_rfl,
      FundamentalGroup.mapOfEq_rfl] at h
    exact h.symm
  · apply GrpCat.hom_ext
    ext g
    -- The wrappers spell the ambient basepoint differently; pin the shared subtype point.
    change _root_.FundamentalGroup.map (ContinuousMap.subtypeVal B') ⟨x', hxB⟩ g =
      _root_.FundamentalGroup.map (ContinuousMap.inclusion subset_union_right) (⟨x, hxB⟩ : B)
        (_root_.FundamentalGroup.mapOfEq ⟨eB, eB.continuous⟩ rfl g)
    rw [FundamentalGroup.mapOfEq_rfl]
    have h := FundamentalGroup.mapOfEq_comp
      (ContinuousMap.inclusion (t := A ∪ B) subset_union_right) ⟨eB, eB.continuous⟩ rfl rfl g
    rw [FundamentalGroup.mapOfEq_rfl, FundamentalGroup.mapOfEq_rfl,
      FundamentalGroup.mapOfEq_rfl] at h
    exact h.symm

namespace VanKampen

/-- **Successive amalgamation for an ordered open cover.** At each step the fundamental
group of the next partial union is the pushout of the preceding group's inclusion and
the new member's inclusion over their actual overlap. No triple-overlap assumption is used. -/
theorem isPushout_partialSups (U : ℕ → Opens X) (n : ℕ) (x : X)
    (hxP : x ∈ partialSups U n) (hxN : x ∈ U (n + 1))
    (hU : ∀ i ≤ n + 1, IsPathConnected (U i : Set X))
    (hOverlap : ∀ i < n,
      ((partialSups U i : Set X) ∩ (U (i + 1) : Set X)).Nonempty)
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
  have hCoe (i : ℕ) : partialSups (fun j => (U j : Set X)) i = (partialSups U i : Set X) :=
    map_partialSups Opens.frameHom U i
  have hP := isPathConnected_partialSups (fun i => (U i : Set X)) n
    (fun i hi => hU i (by omega)) (fun i hi => by rw [hCoe]; exact hOverlap i hi)
  rw [hCoe] at hP
  have hStep : (partialSups U (n + 1) : Set X) =
      (partialSups U n : Set X) ∪ (U (n + 1) : Set X) := by
    have h : partialSups U (n + 1) = partialSups U n ⊔ U (n + 1) := partialSups_succ U n
    exact congrArg (fun V : Opens X => (V : Set X)) h
  exact isPushout_fundamentalGroup_union hStep (partialSups U n).isOpen (U (n + 1)).isOpen
    hP (hU (n + 1) le_rfl) hAB x hxP hxN

/-- For a finite ordered cover, the last successive amalgamation has the ambient
fundamental group as its pushout vertex. Together with `isPushout_partialSups`, this
computes the cover by iterated pushouts along successive overlaps. -/
theorem isPushout_partialSups_cover (U : ℕ → Opens X) (n : ℕ) (x : X)
    (hxP : x ∈ partialSups U n) (hxN : x ∈ U (n + 1))
    (hU : ∀ i ≤ n + 1, IsPathConnected (U i : Set X))
    (hOverlap : ∀ i < n,
      ((partialSups U i : Set X) ∩ (U (i + 1) : Set X)).Nonempty)
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
    have h := congrArg (fun V : Opens X => (V : Set X)) hCover
    have hStep : partialSups U (n + 1) = partialSups U n ⊔ U (n + 1) :=
      partialSups_succ U n
    simpa only [hStep, Opens.coe_sup, Opens.coe_top] using h
  have hInterior : interior (partialSups U n : Set X) ∪
      interior (U (n + 1) : Set X) = univ := by
    rwa [(partialSups U n).isOpen.interior_eq, (U (n + 1)).isOpen.interior_eq]
  have hCoe (i : ℕ) : partialSups (fun j => (U j : Set X)) i = (partialSups U i : Set X) :=
    map_partialSups Opens.frameHom U i
  have hP := isPathConnected_partialSups (fun i => (U i : Set X)) n
    (fun i hi => hU i (by omega)) (fun i hi => by rw [hCoe]; exact hOverlap i hi)
  rw [hCoe] at hP
  exact isPushout_fundamentalGroup hInterior hP (hU (n + 1) le_rfl) hAB hxP hxN

end VanKampen

end TauCeti
