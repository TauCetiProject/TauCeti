/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Presentation
public import TauCeti.AlgebraicTopology.ClassifyingSpace.PresentationComplex
public import TauCeti.AlgebraicTopology.Homotopy.KillHomotopyGroups
public import TauCeti.Topology.CWComplex.Abstract.TwoCellAttachment

/-!
# The cellular classifying space of a presented group

For a group presentation `⟨S | R⟩`, the cellular classifying space
`TauCeti.cellularClassifyingSpace R` is obtained from the presentation complex
`TauCeti.PresentationComplex R` by attaching cells of dimension at least `3` to kill all of its
higher homotopy groups: it is `TauCeti.killHomotopyGroups 2` of the presentation complex, based at
its vertex. The presentation complex is Hausdorff, since it is built from a wedge of circles by
attaching disks (`TauCeti.TwoCellAttachment.instT2Space`), and path connected. So the cellular
classifying space is a Hausdorff, path-connected `K(PresentedGroup R, 1)`
(`TauCeti.isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`). Its fundamental group is
identified with the presented group (`TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv`)
by the inclusion of the presentation complex: the generator `s` corresponds to the loop around
the `s`-th circle of the presentation complex.

Every group `G` has the tautological presentation, whose generators are the elements of `G` and
whose relators are the kernel of the evaluation map `FreeGroup G →* G`, so every group has a
cellular classifying space (`TauCeti.exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`),
with no finiteness, countability or presentation hypothesis. This is the cellular counterpart of
Milnor's classifying space `TauCeti.classifyingSpace G`.

## Main definitions

* `TauCeti.cellularClassifyingSpace R`: the presentation complex of `⟨S | R⟩` with its higher
  homotopy groups killed.
* `TauCeti.cellularClassifyingSpaceBasepoint R`: its base point, the vertex of the presentation
  complex.
* `TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv R`: the isomorphism of its
  fundamental group with `PresentedGroup R`.

## Main results

* `TauCeti.isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`: the cellular classifying space
  of `⟨S | R⟩` is a `K(PresentedGroup R, 1)`.
* `TauCeti.exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`: every group `G` is the
  fundamental group of the cellular classifying space of a presentation of `G`, which is a
  `K(G, 1)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.B, the construction of a `K(G, 1)` from the presentation complex of `G` in the proof
  of Theorem 1B.8, and Example 4.16.
-/

public section

noncomputable section

namespace TauCeti

universe u

variable {S : Type u} (R : Set (FreeGroup S))

/-- The **cellular classifying space** of the presentation `⟨S | R⟩`: the presentation complex
`TauCeti.PresentationComplex R` with cells of dimension at least `3` attached to kill all of its
higher homotopy groups at its vertex. It is a `K(PresentedGroup R, 1)`
(`TauCeti.isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`).

It is an abbreviation, so the API of `TauCeti.killHomotopyGroups` applies to it directly: it is
Hausdorff and path connected, contains the presentation complex as a closed subspace, and is a
relative CW complex over it. -/
abbrev cellularClassifyingSpace : TopCat.{u} :=
  killHomotopyGroups 2 (TopCat.of (PresentationComplex R)) (PresentationComplex.basepoint R)

/-- The base point of the cellular classifying space, the vertex of the presentation complex. -/
abbrev cellularClassifyingSpaceBasepoint : cellularClassifyingSpace R :=
  killHomotopyGroupsIncl 2 (TopCat.of (PresentationComplex R)) (PresentationComplex.basepoint R)
    (PresentationComplex.basepoint R)

/-- **The fundamental group of the cellular classifying space is the presented group.** The
inclusion of the presentation complex induces an isomorphism on fundamental groups, and the
fundamental group of the presentation complex is `PresentedGroup R`
(`TauCeti.PresentationComplex.fundamentalGroupMulEquiv`). -/
def cellularClassifyingSpaceFundamentalGroupMulEquiv :
    FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) ≃*
      PresentedGroup R :=
  (killHomotopyGroupsFundamentalGroupMulEquiv 2 _ _ one_lt_two).symm.trans
    (PresentationComplex.fundamentalGroupMulEquiv R)

/-- The inverse of `cellularClassifyingSpaceFundamentalGroupMulEquiv R` is induced by the
inclusion of the presentation complex: it sends `g` to the image of
`PresentationComplex.fundamentalGroupHom R g`, so the generator `s` goes to the loop around the
`s`-th circle. -/
@[simp]
theorem cellularClassifyingSpaceFundamentalGroupMulEquiv_symm_apply (g : PresentedGroup R) :
    (cellularClassifyingSpaceFundamentalGroupMulEquiv R).symm g =
      FundamentalGroup.map
        (killHomotopyGroupsIncl 2 (TopCat.of (PresentationComplex R))
          (PresentationComplex.basepoint R)).hom _
        (PresentationComplex.fundamentalGroupHom R g) := by
  rw [cellularClassifyingSpaceFundamentalGroupMulEquiv, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, PresentationComplex.fundamentalGroupMulEquiv_symm_apply,
    killHomotopyGroupsFundamentalGroupMulEquiv_apply, FundamentalGroup.mapOfEq_rfl]

/-- **The cellular classifying space of `⟨S | R⟩` is a `K(PresentedGroup R, 1)`**: it is path
connected, its higher homotopy groups vanish, and its fundamental group is the presented group. -/
theorem isEilenbergMacLaneSpaceOne_cellularClassifyingSpace :
    IsEilenbergMacLaneSpaceOne (PresentedGroup R) (cellularClassifyingSpace R)
      (cellularClassifyingSpaceBasepoint R) :=
  (isEilenbergMacLaneSpaceOne_killHomotopyGroups _ _).of_mulEquiv
    (PresentationComplex.fundamentalGroupMulEquiv R)

/-- **Every group has a cellular classifying space.** For every group `G` there is a set `R` of
relators on the generators `G` such that the cellular classifying space of `⟨G | R⟩` is a
`K(G, 1)`: take the tautological presentation, whose relators are the kernel of the evaluation
map `FreeGroup G →* G`. No hypothesis on the group is needed. -/
theorem exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace (G : Type u) [Group G] :
    ∃ R : Set (FreeGroup G), IsEilenbergMacLaneSpaceOne G (cellularClassifyingSpace R)
      (cellularClassifyingSpaceBasepoint R) := by
  let φ : FreeGroup G →* G := FreeGroup.lift id
  have hφ : Function.Surjective φ := fun g ↦ ⟨FreeGroup.of g, FreeGroup.lift_apply_of⟩
  let P := Group.Presentation.ofFreeGroupHom φ hφ φ.ker (Subgroup.normalClosure_eq_self _).symm
  exact ⟨P.rel,
    (isEilenbergMacLaneSpaceOne_cellularClassifyingSpace P.rel).of_mulEquiv P.presentedGroupEquiv⟩

end TauCeti
