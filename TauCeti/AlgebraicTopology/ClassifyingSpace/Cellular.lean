/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Presentation
public import TauCeti.AlgebraicTopology.ClassifyingSpace.PresentationComplex
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Homotopic
public import TauCeti.AlgebraicTopology.Homotopy.KillHomotopyGroups
public import TauCeti.Topology.CWComplex.Abstract.TwoCellAttachment

import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic

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

Maps out of this model have the expected universal property: every homomorphism from its
fundamental group to the fundamental group of a space with vanishing higher homotopy groups is
induced by a pointed map (`TauCeti.exists_mapOfEq_cellularClassifyingSpace`). The map is first
constructed on the presentation complex and then extended across the cells that kill the higher
homotopy groups.

The cellular classifying space is a CW complex
(`TauCeti.instCWComplexCellularClassifyingSpace`): the presentation complex is one
(`TauCeti.PresentationComplex.instCWComplex`), with no cells of dimension above `2`, and the cells
killing the higher homotopy groups have dimension at least `3`. In particular it has CW type, so
the theory of classical CW complexes, such as Whitehead's theorem, applies to it. Its only
`0`-cell is the base point (`TauCeti.skeletonLT_one_cellularClassifyingSpace`), so the pointed
maps realizing a homomorphism of fundamental groups are unique up to homotopy relative to the base
point (`TauCeti.homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace`).

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
* `TauCeti.exists_mapOfEq_cellularClassifyingSpace`: every homomorphism from the fundamental group
  of the cellular classifying space to that of a space with vanishing higher homotopy groups is
  induced by a pointed map.
* `TauCeti.instCWComplexCellularClassifyingSpace`: the cellular classifying space is a CW complex,
  with a single `0`-cell at its base point (`TauCeti.skeletonLT_one_cellularClassifyingSpace`).
* `TauCeti.homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace`: pointed maps from the cellular
  classifying space to a space with vanishing higher homotopy groups that induce the same
  homomorphism of fundamental groups are homotopic relative to the base point.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.B, the construction of a `K(G, 1)` from the presentation complex of `G` in the proof
  of Theorem 1B.8, Proposition 1B.9 for maps into a `K(G, 1)`, and Example 4.16.
-/

public section

noncomputable section

namespace TauCeti

open scoped Topology Topology.Homotopy

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

/-- **Homomorphisms out of the fundamental group of a cellular classifying space are induced by
pointed maps.** If the homotopy groups of `(Z, z)` vanish in dimensions at least two, every
homomorphism from the fundamental group of `cellularClassifyingSpace R` to `π₁(Z, z)` is induced
by a continuous map taking the base point to `z`.

The result is stated directly for fundamental groups, without choosing an identification of
`π₁(Z, z)` with another group. -/
theorem exists_mapOfEq_cellularClassifyingSpace {Z : Type u} [TopologicalSpace Z] {z : Z}
    (hZ : ∀ k, 2 ≤ k → Subsingleton (π_ k Z z))
    (fπ : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) →*
      FundamentalGroup Z z) :
    ∃ (f : C(cellularClassifyingSpace R, Z))
      (hf : f (cellularClassifyingSpaceBasepoint R) = z),
      FundamentalGroup.mapOfEq f hf = fπ := by
  let e := cellularClassifyingSpaceFundamentalGroupMulEquiv R
  obtain ⟨f₀, hf₀, hf₀π⟩ := PresentationComplex.exists_mapOfEq_comp_fundamentalGroupHom
    (fπ.comp e.symm.toMonoidHom)
  subst z
  obtain ⟨f, hf, hfπ⟩ := exists_mapOfEq_comp_killHomotopyGroupsFundamentalGroupMulEquiv
    (x := PresentationComplex.basepoint R) one_lt_two (TopCat.ofHom f₀) hZ
  refine ⟨f.hom, hf, MonoidHom.ext fun g ↦ ?_⟩
  obtain ⟨g, rfl⟩ := e.symm.surjective g
  rw [cellularClassifyingSpaceFundamentalGroupMulEquiv_symm_apply]
  have h₁ := DFunLike.congr_fun hfπ (PresentationComplex.fundamentalGroupHom R g)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h₁
  rw [killHomotopyGroupsFundamentalGroupMulEquiv_apply,
    FundamentalGroup.mapOfEq_rfl] at h₁
  exact h₁.trans <| by
    simpa [e, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, FundamentalGroup.mapOfEq_rfl] using
      DFunLike.congr_fun hf₀π g

/-! ### The CW structure -/

section CWComplex

open Set Topology
open Topology.RelCWComplex (map skeletonLT)

/-- **The cellular classifying space is a CW complex.** Its cells are those of the presentation
complex, one `0`-cell, one `1`-cell for each generator and one `2`-cell for each relator, together
with the cells of dimension at least `3` attached to kill the higher homotopy groups
(`TauCeti.killHomotopyGroupsCWComplexCellEquiv`). -/
instance instCWComplexCellularClassifyingSpace :
    CWComplex (univ : Set (cellularClassifyingSpace R)) :=
  killHomotopyGroupsCWComplex 2 _ _ fun _ ↦ PresentationComplex.isEmpty_cell R

/-- The cellular classifying space has a single `0`-cell, that of the presentation complex: the
tower attaches no cells of dimension `0`. -/
instance : Unique (RelCWComplex.cell (univ : Set (cellularClassifyingSpace R)) 0) :=
  have := isEmpty_killHomotopyGroupsRelativeCWComplex_attachCells_ι 2
    (TopCat.of (PresentationComplex R)) (PresentationComplex.basepoint R) (Nat.zero_le 2)
  ((killHomotopyGroupsCWComplexCellEquiv 2 _ _ _ 0).trans (Equiv.sumEmpty _ _)).unique

/-- The `0`-cell of the cellular classifying space is its base point. -/
@[simp]
theorem map_zero_cellularClassifyingSpace
    (i : RelCWComplex.cell (univ : Set (cellularClassifyingSpace R)) 0) (y : Fin 0 → ℝ) :
    map (C := (univ : Set (cellularClassifyingSpace R))) 0 i y =
      cellularClassifyingSpaceBasepoint R := by
  rw [Subsingleton.elim i ((killHomotopyGroupsCWComplexCellEquiv 2 _ _ _ 0).symm (.inl default)),
    coe_map_killHomotopyGroupsCWComplexCellEquiv_symm_inl, Function.comp_apply,
    PresentationComplex.map_zero]

/-- The `0`-skeleton of the cellular classifying space is its base point. -/
theorem skeletonLT_one_cellularClassifyingSpace :
    (skeletonLT (univ : Set (cellularClassifyingSpace R)) 1 : Set (cellularClassifyingSpace R)) =
      {cellularClassifyingSpaceBasepoint R} := by
  simp [skeletonLT_one_eq_insert]

/-- **Maps out of the cellular classifying space are determined up to pointed homotopy by their
effect on `π₁`.** If the homotopy groups of `Z` vanish in dimensions at least two, at every point,
two maps from `cellularClassifyingSpace R` to `Z` that send the base point to `z` and induce the
same homomorphism of fundamental groups are homotopic relative to the base point. Together with
`TauCeti.exists_mapOfEq_cellularClassifyingSpace`, pointed maps into `Z` up to pointed homotopy
correspond to homomorphisms of fundamental groups. -/
theorem homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace {Z : Type*} [TopologicalSpace Z]
    (hZ : ∀ (z : Z) (n : ℕ), Subsingleton (π_ (n + 2) Z z))
    {f g : C(cellularClassifyingSpace R, Z)} {z : Z}
    (hf : f (cellularClassifyingSpaceBasepoint R) = z)
    (hg : g (cellularClassifyingSpaceBasepoint R) = z)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {cellularClassifyingSpaceBasepoint R} :=
  homotopicRel_singleton_of_mapOfEq_eq_of_cwComplex hZ
    (skeletonLT_one_cellularClassifyingSpace R) hf hg hfg

end CWComplex

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
