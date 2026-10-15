/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic

import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Successive van Kampen pushouts

The based van Kampen theorem may be applied while a space is assembled one cover member at a
time.  This file states the two-set theorem with `A ∪ B`, rather than a previously fixed ambient
space, as its target.  It then applies that form to the partial unions of an ordered family.

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

universe u

variable {X : Type*}

private theorem fundamentalGroup_mapOfEq_square
    {X Y Z W : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
    {x : X} {y : Y} {z : Z} {w : W}
    (f : C(X, Y)) (g : C(Y, W)) (j : C(X, Z)) (k : C(Z, W))
    (hf : f x = y) (hg : g y = w) (hj : j x = z) (hk : k z = w)
    (h : g.comp f = k.comp j) :
    GrpCat.ofHom (FundamentalGroup.mapOfEq f hf) ≫
        GrpCat.ofHom (FundamentalGroup.mapOfEq g hg) =
      GrpCat.ofHom (FundamentalGroup.mapOfEq j hj) ≫
        GrpCat.ofHom (FundamentalGroup.mapOfEq k hk) := by
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro p
  -- Expose the concrete homomorphisms hidden by the categorical composition coercions.
  change FundamentalGroup.mapOfEq g hg (FundamentalGroup.mapOfEq f hf p) =
    FundamentalGroup.mapOfEq k hk (FundamentalGroup.mapOfEq j hj p)
  rw [FundamentalGroup.mapOfEq_comp, FundamentalGroup.mapOfEq_comp]
  exact FundamentalGroup.mapOfEq_congr h _ _ p

/-- The union of the first `n + 1` members of an ordered family of sets. -/
def partialUnion (U : ℕ → Set X) : ℕ → Set X
  | 0 => U 0
  | n + 1 => partialUnion U n ∪ U (n + 1)

@[simp]
lemma mem_partialUnion {U : ℕ → Set X} {n : ℕ} {x : X} :
    x ∈ partialUnion U n ↔ ∃ i : Fin (n + 1), x ∈ U i := by
  induction n with
  | zero => simp [partialUnion]
  | succ n ih =>
    rw [partialUnion, mem_union, ih]
    constructor
    · rintro (⟨i, hi⟩ | hi)
      · exact ⟨i.castSucc, hi⟩
      · exact ⟨Fin.last (n + 1), hi⟩
    · rintro ⟨i, hi⟩
      refine Fin.lastCases (motive := fun i ↦ x ∈ U i →
        (∃ j : Fin (n + 1), x ∈ U j) ∨ x ∈ U (n + 1)) ?_ (fun j ↦ ?_) i hi
      · exact Or.inr
      · exact fun hj ↦ Or.inl ⟨j, hj⟩

/-- The first partial union is the first member of the family. -/
@[simp]
lemma partialUnion_zero (U : ℕ → Set X) : partialUnion U 0 = U 0 := by
  rfl

/-- A partial union grows by adjoining the next member. -/
@[simp]
lemma partialUnion_succ (U : ℕ → Set X) (n : ℕ) :
    partialUnion U (n + 1) = partialUnion U n ∪ U (n + 1) := by
  rfl

/-- A partial union is open when each set occurring in it is open. -/
lemma isOpen_partialUnion [TopologicalSpace X] {U : ℕ → Set X} {n : ℕ}
    (hU : ∀ i ≤ n, IsOpen (U i)) : IsOpen (partialUnion U n) := by
  induction n with
  | zero => exact hU 0 le_rfl
  | succ n ih =>
    exact (ih fun i hi ↦ hU i (hi.trans n.le_succ)).union (hU (n + 1) le_rfl)

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
  let eA : A ≃ₜ A' :=
    { toFun := fun y ↦ ⟨⟨y, Or.inl y.2⟩, y.2⟩
      invFun := fun y ↦ ⟨y.1.1, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let eB : B ≃ₜ B' :=
    { toFun := fun y ↦ ⟨⟨y, Or.inr y.2⟩, y.2⟩
      invFun := fun y ↦ ⟨y.1.1, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let eAB : ↥(A ∩ B) ≃ₜ ↥(A' ∩ B') :=
    { toFun := fun y ↦ ⟨⟨y, Or.inl y.2.1⟩, y.2⟩
      invFun := fun y ↦ ⟨y.1.1, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let eP : P ≃ₜ P := Homeomorph.refl P
  let iA : GrpCat.of (FundamentalGroup A ⟨x, hxA⟩) ≅
      GrpCat.of (FundamentalGroup A' ⟨p, hpA⟩) :=
    (FundamentalGroup.homeomorphMulEquivOfEq eA rfl).toGrpIso
  let iB : GrpCat.of (FundamentalGroup B ⟨x, hxB⟩) ≅
      GrpCat.of (FundamentalGroup B' ⟨p, hpB⟩) :=
    (FundamentalGroup.homeomorphMulEquivOfEq eB rfl).toGrpIso
  let iAB : GrpCat.of (FundamentalGroup ↥(A ∩ B) ⟨x, hxA, hxB⟩) ≅
      GrpCat.of (FundamentalGroup ↥(A' ∩ B')
        ⟨p, show p ∈ A' ∩ B' from ⟨hpA, hpB⟩⟩) :=
    (FundamentalGroup.homeomorphMulEquivOfEq eAB rfl).toGrpIso
  let iP : GrpCat.of (FundamentalGroup P ⟨x, Or.inl hxA⟩) ≅
      GrpCat.of (FundamentalGroup P p) :=
    (FundamentalGroup.homeomorphMulEquivOfEq eP rfl).toGrpIso
  have iA_hom : iA.hom = GrpCat.ofHom
      (FundamentalGroup.mapOfEq ⟨eA, eA.continuous⟩ rfl) := by
    apply GrpCat.hom_ext
    ext g
    exact FundamentalGroup.homeomorphMulEquivOfEq_apply eA rfl g
  have iB_hom : iB.hom = GrpCat.ofHom
      (FundamentalGroup.mapOfEq ⟨eB, eB.continuous⟩ rfl) := by
    apply GrpCat.hom_ext
    ext g
    exact FundamentalGroup.homeomorphMulEquivOfEq_apply eB rfl g
  have iAB_hom : iAB.hom = GrpCat.ofHom
      (FundamentalGroup.mapOfEq ⟨eAB, eAB.continuous⟩ rfl) := by
    apply GrpCat.hom_ext
    ext g
    exact FundamentalGroup.homeomorphMulEquivOfEq_apply eAB rfl g
  have iP_hom : iP.hom = GrpCat.ofHom
      (FundamentalGroup.mapOfEq ⟨eP, eP.continuous⟩ rfl) := by
    apply GrpCat.hom_ext
    ext g
    exact FundamentalGroup.homeomorphMulEquivOfEq_apply eP rfl g
  apply (isPushout_fundamentalGroup hCover hA' hB' hAB' hpA hpB).of_iso'
    iAB iA iB iP
  · rw [iAB_hom, iA_hom]
    simp only [← FundamentalGroup.mapOfEq_rfl]
    apply fundamentalGroup_mapOfEq_square
    ext y
    rfl
  · rw [iAB_hom, iB_hom]
    simp only [← FundamentalGroup.mapOfEq_rfl]
    apply fundamentalGroup_mapOfEq_square
    ext y
    rfl
  · rw [iA_hom, iP_hom]
    simp only [← FundamentalGroup.mapOfEq_rfl]
    apply fundamentalGroup_mapOfEq_square
    ext y
    rfl
  · rw [iB_hom, iP_hom]
    simp only [← FundamentalGroup.mapOfEq_rfl]
    apply fundamentalGroup_mapOfEq_square
    ext y
    rfl

end Union

section Successive

variable [TopologicalSpace X]
variable (U : ℕ → Set X) (x : X)

/-- **Successive van Kampen pushout.** The fundamental group of the union of the first `n + 2`
members is the amalgamated free product of the fundamental group of the first `n + 1` members
and that of `U (n + 1)`, over their intersection.

Applying this theorem for consecutive values of `n` is the ordered finite-cover iteration of van
Kampen.  Its path-connectedness assumptions mention precisely the three spaces occurring at this
step, while openness is required only through the next member. -/
theorem isPushout_fundamentalGroup_partialUnion_succ (n : ℕ)
    (hUopen : ∀ i ≤ n + 1, IsOpen (U i))
    (hPartial : IsPathConnected (partialUnion U n))
    (hNext : IsPathConnected (U (n + 1)))
    (hInter : IsPathConnected (partialUnion U n ∩ U (n + 1)))
    (hxPartial : x ∈ partialUnion U n) (hxNext : x ∈ U (n + 1)) :
    IsPushout
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (⟨x, hxPartial, hxNext⟩ :
          ↥(partialUnion U n ∩ U (n + 1)))))
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        (⟨x, hxPartial, hxNext⟩ :
          ↥(partialUnion U n ∩ U (n + 1)))))
      (GrpCat.ofHom (FundamentalGroup.map
        (ContinuousMap.inclusion subset_union_left)
        (⟨x, hxPartial⟩ : partialUnion U n)))
      (GrpCat.ofHom (FundamentalGroup.map
        (ContinuousMap.inclusion subset_union_right)
        (⟨x, hxNext⟩ : U (n + 1)))) := by
  exact isPushout_fundamentalGroup_union
    (isOpen_partialUnion fun i hi ↦ hUopen i (hi.trans n.le_succ))
    (hUopen (n + 1) le_rfl) hPartial hNext hInter hxPartial hxNext

end Successive

end TauCeti
