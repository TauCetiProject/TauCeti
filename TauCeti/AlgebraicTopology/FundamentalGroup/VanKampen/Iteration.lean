/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
public import Mathlib.Order.SetAccumulate

import TauCeti.AlgebraicTopology.FundamentalGroup.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Successive van Kampen pushouts

The based van Kampen theorem may be applied while a space is assembled one cover member at a
time.  This file states the two-set theorem with `A ∪ B`, rather than a previously fixed ambient
space, as its target.  It then applies that form to the accumulated unions of an ordered family.

Consequently, if the relevant members, partial unions, and overlaps are path connected, the
fundamental group after adjoining the next member is the amalgamated free product of the previous
fundamental group and that member's fundamental group.  Iterating these pushout squares gives the
usual successive-amalgamation calculation for a finite open cover.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.2, Theorem 1.20.
* R. Brown, *Topology and Groupoids*, 3rd ed., Chapters 6--7.
-/

public section

open CategoryTheory Limits Set Topology

namespace TauCeti

variable {X : Type*}

section Union

variable [TopologicalSpace X]
variable {A B : Set X} {x : X}

/-- **Van Kampen with the union as target.** If `A` and `B` are open and path connected, their
intersection is path connected, and both contain `x`, then the square induced by the inclusions
of `A ∩ B` into `A` and `B`, and of `A` and `B` into `A ∪ B`, is a pushout of groups.

Unlike `isPushout_fundamentalGroup`, this result does not require `A` and `B` to cover a larger
ambient space.  This is the form used to adjoin members of a finite cover successively. -/
theorem isPushout_fundamentalGroup_union (hAopen : IsOpen A) (hBopen : IsOpen B)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsPathConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) :
    IsPushout
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (⟨x, hxA, hxB⟩ : ↥(A ∩ B))))
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        (⟨x, hxA, hxB⟩ : ↥(A ∩ B))))
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion subset_union_left)
        (⟨x, hxA⟩ : A)))
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion subset_union_right)
        (⟨x, hxB⟩ : B))) := by
  let P : Set X := A ∪ B
  let A' : Set P := ((↑) : P → X) ⁻¹' A
  let B' : Set P := ((↑) : P → X) ⁻¹' B
  let p : P := ⟨x, Or.inl hxA⟩
  have hpA : p ∈ A' := hxA
  have hpB : p ∈ B' := hxB
  have hA'open : IsOpen A' := hAopen.preimage continuous_subtype_val
  have hB'open : IsOpen B' := hBopen.preimage continuous_subtype_val
  have hCover : interior A' ∪ interior B' = univ := by
    rw [hA'open.interior_eq, hB'open.interior_eq]
    ext y
    simp only [mem_union, mem_univ, iff_true]
    exact y.2
  have hA' : IsPathConnected A' :=
    hA.preimage_coe subset_union_left
  have hB' : IsPathConnected B' :=
    hB.preimage_coe subset_union_right
  have hAB' : IsPathConnected (A' ∩ B') := by
    simpa only [A', B', preimage_inter, Set.mem_inter_iff] using
      hAB.preimage_coe (inter_subset_left.trans subset_union_left)
  have hrange {s : Set X} (hs : s ⊆ A ∪ B) :
      s ⊆ range (Subtype.val : P → X) := by
    rwa [Subtype.range_coe]
  let subsetHomeomorph (s : Set X) (hs : s ⊆ A ∪ B) :
      s ≃ₜ ((↑) : P → X) ⁻¹' s :=
    (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (hrange hs)).symm
  have subsetHomeomorph_coe (s : Set X) (hs : s ⊆ A ∪ B) (y : s) :
      ((((subsetHomeomorph s hs y : ((↑) : P → X) ⁻¹' s) : P) : X)) = y := by
    have h := congrArg Subtype.val
      ((Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange (hrange hs)).apply_symm_apply y)
    rwa [Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe] at h
  let eA : A ≃ₜ A' := subsetHomeomorph A subset_union_left
  let eB : B ≃ₜ B' := subsetHomeomorph B subset_union_right
  let eAB : ↥(A ∩ B) ≃ₜ ↥(A' ∩ B') :=
    subsetHomeomorph (A ∩ B) (inter_subset_left.trans subset_union_left)
  let eP : P ≃ₜ P := Homeomorph.refl P
  have eA_coe (y : A) : ((((eA y : A') : P) : X)) = y := by
    exact subsetHomeomorph_coe A subset_union_left y
  have eB_coe (y : B) : ((((eB y : B') : P) : X)) = y := by
    exact subsetHomeomorph_coe B subset_union_right y
  have eAB_coe (y : ↥(A ∩ B)) : ((((eAB y : ↥(A' ∩ B')) : P) : X)) = y := by
    exact subsetHomeomorph_coe (A ∩ B)
      (inter_subset_left.trans subset_union_left) y
  have heA : eA ⟨x, hxA⟩ = ⟨p, hpA⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    exact eA_coe ⟨x, hxA⟩
  have heB : eB ⟨x, hxB⟩ = ⟨p, hpB⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    exact eB_coe ⟨x, hxB⟩
  have heAB : eAB ⟨x, hxA, hxB⟩ =
      ⟨p, show p ∈ A' ∩ B' from ⟨hpA, hpB⟩⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    exact eAB_coe ⟨x, hxA, hxB⟩
  have heP : eP ⟨x, Or.inl hxA⟩ = p := rfl
  let iA : GrpCat.of (FundamentalGroup A ⟨x, hxA⟩) ≅
      GrpCat.of (FundamentalGroup A' ⟨p, hpA⟩) :=
    (FundamentalGroup.homeomorphMulEquivOfEq eA heA).toGrpIso
  let iB : GrpCat.of (FundamentalGroup B ⟨x, hxB⟩) ≅
      GrpCat.of (FundamentalGroup B' ⟨p, hpB⟩) :=
    (FundamentalGroup.homeomorphMulEquivOfEq eB heB).toGrpIso
  let iAB : GrpCat.of (FundamentalGroup ↥(A ∩ B) ⟨x, hxA, hxB⟩) ≅
      GrpCat.of (FundamentalGroup ↥(A' ∩ B')
        ⟨p, show p ∈ A' ∩ B' from ⟨hpA, hpB⟩⟩) :=
    (FundamentalGroup.homeomorphMulEquivOfEq eAB heAB).toGrpIso
  let iP : GrpCat.of (FundamentalGroup P ⟨x, Or.inl hxA⟩) ≅
      GrpCat.of (FundamentalGroup P p) :=
    (FundamentalGroup.homeomorphMulEquivOfEq eP heP).toGrpIso
  have iA_hom : iA.hom = GrpCat.ofHom
      (FundamentalGroup.mapOfEq ⟨eA, eA.continuous⟩ heA) := by
    simpa only [iA] using FundamentalGroup.homeomorphMulEquivOfEq_toGrpIso_hom eA heA
  have iB_hom : iB.hom = GrpCat.ofHom
      (FundamentalGroup.mapOfEq ⟨eB, eB.continuous⟩ heB) := by
    simpa only [iB] using FundamentalGroup.homeomorphMulEquivOfEq_toGrpIso_hom eB heB
  have iAB_hom : iAB.hom = GrpCat.ofHom
      (FundamentalGroup.mapOfEq ⟨eAB, eAB.continuous⟩ heAB) := by
    simpa only [iAB] using FundamentalGroup.homeomorphMulEquivOfEq_toGrpIso_hom eAB heAB
  have iP_hom : iP.hom = GrpCat.ofHom
      (FundamentalGroup.mapOfEq ⟨eP, eP.continuous⟩ heP) := by
    simpa only [iP] using
      FundamentalGroup.homeomorphMulEquivOfEq_toGrpIso_hom eP heP
  apply (isPushout_fundamentalGroup hCover hA' hB' hAB' hpA hpB).of_iso'
    iAB iA iB iP
  · rw [iAB_hom, iA_hom]
    simp only [← FundamentalGroup.mapOfEq_rfl]
    apply FundamentalGroup.mapOfEq_square
    ext y
    exact (eAB_coe y).trans (eA_coe ⟨y, y.2.1⟩).symm
  · rw [iAB_hom, iB_hom]
    simp only [← FundamentalGroup.mapOfEq_rfl]
    apply FundamentalGroup.mapOfEq_square
    ext y
    exact (eAB_coe y).trans (eB_coe ⟨y, y.2.2⟩).symm
  · rw [iA_hom, iP_hom]
    simp only [← FundamentalGroup.mapOfEq_rfl]
    apply FundamentalGroup.mapOfEq_square
    ext y
    exact eA_coe y
  · rw [iB_hom, iP_hom]
    simp only [← FundamentalGroup.mapOfEq_rfl]
    apply FundamentalGroup.mapOfEq_square
    ext y
    exact eB_coe y

end Union

section Successive

variable [TopologicalSpace X]
variable (U : ℕ → Set X) (x : X)

/-- **Successive van Kampen pushout.** The fundamental group of the union accumulated through
index `n + 1` is the amalgamated free product of the fundamental group accumulated through `n`
and that of `U (n + 1)`, over their intersection.

Applying this theorem for consecutive values of `n` is the ordered finite-cover iteration of van
Kampen.  Its path-connectedness assumptions mention precisely the three spaces occurring at this
step, while openness is required only through the next member. -/
theorem isPushout_fundamentalGroup_accumulate_succ (n : ℕ)
    (hUopen : ∀ i ≤ n + 1, IsOpen (U i))
    (hPartial : IsPathConnected (Set.accumulate U n))
    (hNext : IsPathConnected (U (n + 1)))
    (hInter : IsPathConnected (Set.accumulate U n ∩ U (n + 1)))
    (hxPartial : x ∈ Set.accumulate U n) (hxNext : x ∈ U (n + 1)) :
    IsPushout
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (⟨x, hxPartial, hxNext⟩ :
          ↥(Set.accumulate U n ∩ U (n + 1)))))
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        (⟨x, hxPartial, hxNext⟩ :
          ↥(Set.accumulate U n ∩ U (n + 1)))))
      (GrpCat.ofHom (FundamentalGroup.map
        (ContinuousMap.inclusion subset_union_left)
        (⟨x, hxPartial⟩ : Set.accumulate U n)))
      (GrpCat.ofHom (FundamentalGroup.map
        (ContinuousMap.inclusion subset_union_right)
        (⟨x, hxNext⟩ : U (n + 1)))) := by
  exact isPushout_fundamentalGroup_union
    (by
      rw [Set.accumulate_def]
      exact isOpen_biUnion fun i hi ↦ hUopen i (le_trans hi n.le_succ))
    (hUopen (n + 1) le_rfl) hPartial hNext hInter hxPartial hxNext

end Successive

end TauCeti
