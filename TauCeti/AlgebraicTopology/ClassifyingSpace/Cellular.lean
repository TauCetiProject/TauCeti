/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.PresentationComplex
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Homotopic
public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
public import TauCeti.AlgebraicTopology.Homotopy.KillHomotopyGroups
public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat
public import TauCeti.Topology.CWComplex.Abstract.TwoCellAttachment
public import TauCeti.Topology.CWComplex.Classical.DeltaGenerated

import Mathlib.GroupTheory.Presentation
import TauCeti.AlgebraicTopology.Homotopy.Whitehead
import TauCeti.Topology.Homotopy.Extension.CWComplex

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
cellular classifying space (`TauCeti.exists_cellularClassifyingSpace_isEilenbergMacLaneSpaceOne`),
with no finiteness, countability or presentation hypothesis. The stronger existence statement
including semilocal simple connectivity (transported from Milnor's classifying space
`TauCeti.classifyingSpace G`) is in `TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison`
(`TauCeti.exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`).

Maps out of this model have the expected universal property: every homomorphism from its
fundamental group to the fundamental group of a space with vanishing higher homotopy groups is
induced by a pointed map (`TauCeti.exists_mapOfEq_cellularClassifyingSpace`). The map is first
constructed on the presentation complex and then extended across the cells that kill the higher
homotopy groups.

The cellular classifying space is a CW complex
(`TauCeti.instCWComplexCellularClassifyingSpace`): the presentation complex is one
(`TauCeti.PresentationComplex.instCWComplex`), with no cells of dimension above `2`, and the cells
killing the higher homotopy groups have dimension at least `3`. In particular it has CW type, so
the theory of classical CW complexes, such as Whitehead's theorem, applies to it, and, as a
Hausdorff CW complex, it is delta-generated and hence locally path-connected
(`TauCeti.instDeltaGeneratedSpaceOfCWComplexUniv`). Its only
`0`-cell is the base point (`TauCeti.skeletonLT_one_cellularClassifyingSpace`), making it
well-pointed (`TauCeti.hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint`). Hence
pointed maps realizing a homomorphism of fundamental groups are unique up to homotopy relative to
the base point (`TauCeti.homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace`), so `π₁` gives a
bijection on pointed homotopy classes
(`TauCeti.fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace`),
and every isomorphism of its fundamental group with the fundamental group of an aspherical space
`Y` of CW type is realized by a homotopy equivalence
(`TauCeti.cellularClassifyingSpaceHomotopyEquiv`), upgrading to an isomorphism in
`TauCeti.PointedHomotopyCat` when `Y` is well-pointed
(`TauCeti.cellularClassifyingSpaceHomotopyEquivIso`).

If the presentation complex is already aspherical, as it is for a presentation of a free group
without relators, the cells killing the higher homotopy groups change nothing up to homotopy: by
Whitehead's theorem the inclusion of the presentation complex is a homotopy equivalence
(`TauCeti.PresentationComplex.homotopyEquivCellularClassifyingSpace`).

## Main definitions

* `TauCeti.cellularClassifyingSpace R`: the presentation complex of `⟨S | R⟩` with its higher
  homotopy groups killed.
* `TauCeti.cellularClassifyingSpaceBasepoint R`: its base point, the vertex of the presentation
  complex.
* `TauCeti.cellularClassifyingSpaceBased R`: the cellular classifying space as a based space.
* `TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv R`: the isomorphism of its
  fundamental group with `PresentedGroup R`.
* `TauCeti.cellularClassifyingSpaceHomotopyEquiv`: the homotopy equivalence from the cellular
  classifying space to an aspherical space of CW type realizing a given isomorphism of
  fundamental groups by a pointed forward map.
* `TauCeti.cellularClassifyingSpaceHomotopyEquivIso`: pointed isomorphism in `PointedHomotopyCat`
  from the cellular model to any well-pointed aspherical space of CW type realizing a prescribed
  isomorphism on `π₁`.
* `TauCeti.PresentationComplex.homotopyEquivCellularClassifyingSpace`: for an aspherical
  presentation complex, its inclusion into the cellular classifying space, as a homotopy
  equivalence.

## Main results

* `TauCeti.isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`: the cellular classifying space
  of `⟨S | R⟩` is a `K(PresentedGroup R, 1)`.
* `TauCeti.exists_cellularClassifyingSpace_isEilenbergMacLaneSpaceOne`: every group `G` has a
  presentation whose cellular classifying space is a `K(G, 1)`.
* `TauCeti.exists_mapOfEq_cellularClassifyingSpace`: every homomorphism from the fundamental group
  of the cellular classifying space to that of a space with vanishing higher homotopy groups is
  induced by a pointed map.
* `TauCeti.instCWComplexCellularClassifyingSpace`: the cellular classifying space is a CW complex,
  with a single `0`-cell at its base point (`TauCeti.skeletonLT_one_cellularClassifyingSpace`),
  making it well-pointed (`TauCeti.hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint`).
* `TauCeti.homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace`: pointed maps from the cellular
  classifying space to a space with vanishing higher homotopy groups that induce the same
  homomorphism of fundamental groups are homotopic relative to the base point.
* `TauCeti.fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace`: pointed homotopy
  classes of maps out of a cellular classifying space into a space with no higher homotopy groups
  are classified by their effect on `π₁`.
* `TauCeti.mapOfEq_cellularClassifyingSpaceHomotopyEquiv_toFun_apply`,
  `TauCeti.homotopicRel_cellularClassifyingSpaceHomotopyEquiv_toFun`,
  `TauCeti.exists_path_map_cellularClassifyingSpaceHomotopyEquiv_invFun`: fundamental-group
  and uniqueness properties of `cellularClassifyingSpaceHomotopyEquiv`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 (Proposition 0.19), Section 1.B, the construction of a `K(G, 1)` from the presentation
  complex of `G` in the proof of Theorem 1B.8, Proposition 1B.9 for maps into a `K(G, 1)`,
  Example 4.16, and Section 4.1 (Theorem 4.5).
-/

public section

noncomputable section

namespace TauCeti

open scoped Topology Topology.Homotopy ContinuousMap

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

/-- The cellular classifying space `cellularClassifyingSpace R` as a based space, based at the
vertex `cellularClassifyingSpaceBasepoint R`. -/
@[expose] def cellularClassifyingSpaceBased : BasedTopologicalSpace.{u} :=
  ⟨cellularClassifyingSpace R, cellularClassifyingSpaceBasepoint R⟩

@[simp]
theorem cellularClassifyingSpaceBased_carrier :
    (cellularClassifyingSpaceBased R).carrier = cellularClassifyingSpace R :=
  (rfl)

@[simp]
theorem cellularClassifyingSpaceBased_basepoint :
    (cellularClassifyingSpaceBased R).basepoint = cellularClassifyingSpaceBasepoint R :=
  (rfl)

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

/-- `cellularClassifyingSpaceFundamentalGroupMulEquiv R` sends the image of a loop of the
presentation complex under its inclusion to the class of that loop in the presented group. -/
@[simp]
theorem cellularClassifyingSpaceFundamentalGroupMulEquiv_map_killHomotopyGroupsIncl
    (x : FundamentalGroup (PresentationComplex R) (PresentationComplex.basepoint R)) :
    cellularClassifyingSpaceFundamentalGroupMulEquiv R
      (FundamentalGroup.map
        (killHomotopyGroupsIncl 2 (TopCat.of (PresentationComplex R))
          (PresentationComplex.basepoint R)).hom _ x) =
      PresentationComplex.fundamentalGroupMulEquiv R x := by
  rw [← MulEquiv.eq_symm_apply, cellularClassifyingSpaceFundamentalGroupMulEquiv_symm_apply,
    ← PresentationComplex.fundamentalGroupMulEquiv_symm_apply, MulEquiv.symm_apply_apply]

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

/-- The underlying space of `cellularClassifyingSpaceBased R` has CW type. -/
instance instCWTypeCellularClassifyingSpaceBased :
    CWType (cellularClassifyingSpaceBased R).carrier :=
  inferInstanceAs (CWType (cellularClassifyingSpace R))

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

/-- **The cellular classifying space is well-pointed.** Its base point is its unique `0`-cell, so
it has the homotopy extension property. -/
theorem hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint :
    HasHomotopyExtensionProperty
      ({cellularClassifyingSpaceBasepoint R} : Set (cellularClassifyingSpace R)) :=
  hasHomotopyExtensionProperty_singleton_of_mem_skeletonLT_one
    (by rw [skeletonLT_one_cellularClassifyingSpace]; exact Set.mem_singleton _)

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

variable {R}

/-- **An aspherical presentation complex is already a classifying space.** If the presentation
complex of `⟨S | R⟩` is aspherical, its inclusion into the cellular classifying space is a
homotopy equivalence (`TauCeti.PresentationComplex.homotopyEquivCellularClassifyingSpace_toFun`):
the cells of dimension at least `3` attached to kill the higher homotopy groups change nothing up
to homotopy. -/
def PresentationComplex.homotopyEquivCellularClassifyingSpace
    (h : IsAspherical (PresentationComplex R) (PresentationComplex.basepoint R)) :
    PresentationComplex R ≃ₕ cellularClassifyingSpace R :=
  have : PathConnectedSpace (PresentationComplex R) := h.pathConnectedSpace
  (isWeakHomotopyEquivalence_killHomotopyGroupsIncl 2 (TopCat.of (PresentationComplex R)) _
    fun k hk ↦ by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
      exact h.subsingleton_homotopyGroup m).homotopyEquiv

/-- The homotopy equivalence `TauCeti.PresentationComplex.homotopyEquivCellularClassifyingSpace` is
the inclusion of the presentation complex. -/
@[simp]
theorem PresentationComplex.homotopyEquivCellularClassifyingSpace_toFun
    (h : IsAspherical (PresentationComplex R) (PresentationComplex.basepoint R)) :
    (homotopyEquivCellularClassifyingSpace h).toFun =
      (killHomotopyGroupsIncl 2 (TopCat.of (PresentationComplex R))
        (PresentationComplex.basepoint R)).hom :=
  ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv_toFun _

end CWComplex

/-- **Pointed maps out of a cellular classifying space are classified by `π₁`.** If the homotopy
groups of `Y` vanish from degree `2` on, at every point, then a pointed homotopy class of maps from
the cellular classifying space `cellularClassifyingSpace R` to `Y` is determined by the homomorphism
it induces on fundamental groups, and every homomorphism is induced by such a class. -/
theorem fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace
    {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R))
      (Y := PointedHomotopyCat.quotient.obj Y)) := by
  refine ⟨fun a b hab ↦ ?_, fun ψ ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := PointedHomotopyCat.quotient.map_surjective a
    obtain ⟨g, rfl⟩ := PointedHomotopyCat.quotient.map_surjective b
    simp only [PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map] at hab
    rw [PointedHomotopyCat.quotient_map_eq_iff]
    exact homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace R hY f.map_basepoint g.map_basepoint
      (by
        have h' := congrArg GrpCat.Hom.hom hab
        rw [BasedTopologicalSpace.fundamentalGroupFunctor_map_hom,
          BasedTopologicalSpace.fundamentalGroupFunctor_map_hom] at h'
        exact h')
  · obtain ⟨f, hf, hfψ⟩ := exists_mapOfEq_cellularClassifyingSpace R
      (fun k hk ↦ by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
        exact hY _ n) ψ.hom
    exact ⟨PointedHomotopyCat.quotient.map ⟨f, hf⟩, GrpCat.hom_ext <|
      (congrArg GrpCat.Hom.hom
        (PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map _)).trans
        ((BasedTopologicalSpace.fundamentalGroupFunctor_map_hom _).trans hfψ)⟩

section General

variable {Y : Type u} [TopologicalSpace Y] [CWType Y] {y : Y} (hY : IsAspherical Y y)
  (φ : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) ≃*
    FundamentalGroup Y y)

include hY

omit [CWType Y] in
/-- A pointed map from the cellular classifying space to an aspherical space realizing a given
isomorphism of fundamental groups is a weak homotopy equivalence, packaged with the map. -/
private theorem exists_isWeakHomotopyEquivalence_mapOfEq_cellularClassifyingSpace :
    ∃ (f : C(cellularClassifyingSpace R, Y)) (hf : f (cellularClassifyingSpaceBasepoint R) = y),
      FundamentalGroup.mapOfEq f hf = φ.toMonoidHom ∧ f.IsWeakHomotopyEquivalence := by
  obtain ⟨f, hf, hfφ⟩ := exists_mapOfEq_cellularClassifyingSpace R
    (fun k hk ↦ by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
      exact hY.subsingleton_homotopyGroup n) φ.toMonoidHom
  have hC := (isEilenbergMacLaneSpaceOne_cellularClassifyingSpace R).isAspherical
  exact ⟨f, hf, hfφ, (hC.isWeakHomotopyEquivalence_iff hY hf).2 (hfφ ▸ φ.bijective)⟩

/-- **The cellular classifying space is homotopy equivalent to every aspherical space of CW type
with the same fundamental group.** For an isomorphism `φ` from the fundamental group of
`cellularClassifyingSpace R` to `π₁(Y, y)`, this is a homotopy equivalence whose forward map sends
the base point to `y` (`TauCeti.cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint`) and
induces `φ` on fundamental groups
(`TauCeti.mapOfEq_cellularClassifyingSpaceHomotopyEquiv_toFun_apply`). The forward map is unique
up to homotopy relative to the base point
(`TauCeti.homotopicRel_cellularClassifyingSpaceHomotopyEquiv_toFun`). -/
def cellularClassifyingSpaceHomotopyEquiv : cellularClassifyingSpace R ≃ₕ Y :=
  (exists_isWeakHomotopyEquivalence_mapOfEq_cellularClassifyingSpace R hY φ)
    |>.choose_spec.choose_spec.2.homotopyEquiv

/-- The forward map of `TauCeti.cellularClassifyingSpaceHomotopyEquiv` is the chosen pointed map
realizing `φ`. -/
private theorem cellularClassifyingSpaceHomotopyEquiv_toFun :
    (cellularClassifyingSpaceHomotopyEquiv R hY φ).toFun =
      (exists_isWeakHomotopyEquivalence_mapOfEq_cellularClassifyingSpace R hY φ).choose :=
  ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv_toFun _

/-- The forward map of `TauCeti.cellularClassifyingSpaceHomotopyEquiv` is pointed. -/
@[simp]
theorem cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint :
    (cellularClassifyingSpaceHomotopyEquiv R hY φ).toFun (cellularClassifyingSpaceBasepoint R) =
      y := by
  rw [cellularClassifyingSpaceHomotopyEquiv_toFun]
  exact (exists_isWeakHomotopyEquivalence_mapOfEq_cellularClassifyingSpace R hY φ)
    |>.choose_spec.choose

/-- **The forward map of `TauCeti.cellularClassifyingSpaceHomotopyEquiv` induces `φ` on
fundamental groups.** -/
@[simp]
theorem mapOfEq_cellularClassifyingSpaceHomotopyEquiv_toFun_apply
    (a : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R)) :
    FundamentalGroup.mapOfEq (cellularClassifyingSpaceHomotopyEquiv R hY φ).toFun
      (cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hY φ) a = φ a := by
  have h := exists_isWeakHomotopyEquivalence_mapOfEq_cellularClassifyingSpace R hY φ
  rw [FundamentalGroup.mapOfEq_congr (cellularClassifyingSpaceHomotopyEquiv_toFun R hY φ) _
    h.choose_spec.choose]
  exact DFunLike.congr_fun h.choose_spec.choose_spec.1 a

/-- **The forward map of `TauCeti.cellularClassifyingSpaceHomotopyEquiv` is determined by `φ` up to
pointed homotopy.** Every map from the cellular classifying space to `Y` that sends the base point
to `y` and induces `φ` on fundamental groups is homotopic to it relative to the base point. -/
theorem homotopicRel_cellularClassifyingSpaceHomotopyEquiv_toFun
    {f : C(cellularClassifyingSpace R, Y)} (hf : f (cellularClassifyingSpaceBasepoint R) = y)
    (hfφ : ∀ a, FundamentalGroup.mapOfEq f hf a = φ a) :
    f.HomotopicRel (cellularClassifyingSpaceHomotopyEquiv R hY φ).toFun
      {cellularClassifyingSpaceBasepoint R} :=
  homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace R
    (fun z n ↦ (hY.of_basepoint z).subsingleton_homotopyGroup n) hf
    (cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hY φ)
    (MonoidHom.ext fun a ↦ by simp [hfφ])

/-- **The homotopy inverse of `TauCeti.cellularClassifyingSpaceHomotopyEquiv` induces `φ⁻¹`, up to
a change of base point.** The inverse need not send `y` to the base point, but there is a path `γ`
from its value at `y` to the base point such that the induced map on fundamental groups, followed
by basepoint change along `γ`, is `φ⁻¹`. -/
theorem exists_path_map_cellularClassifyingSpaceHomotopyEquiv_invFun :
    ∃ γ : Path ((cellularClassifyingSpaceHomotopyEquiv R hY φ).invFun y)
        (cellularClassifyingSpaceBasepoint R),
      ∀ a, _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ
        (FundamentalGroup.map (cellularClassifyingSpaceHomotopyEquiv R hY φ).invFun y a) =
          φ.symm a := by
  have := (isEilenbergMacLaneSpaceOne_cellularClassifyingSpace R).isAspherical.pathConnectedSpace
  set e := cellularClassifyingSpaceHomotopyEquiv R hY φ
  -- The inverse `e⁻¹` is a homotopy right inverse of `e`, and `φ⁻¹ ∘ e_*` is the identity.
  obtain ⟨γ, hγ⟩ := e.right_inv.some.exists_path_fundamentalGroupMulEquivOfPath_map_comp
    (g := ContinuousMap.id _) (y := cellularClassifyingSpaceBasepoint R)
    (cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hY φ) (ContinuousMap.id_apply _)
    φ.symm.toMonoidHom
    (MonoidHom.ext fun a ↦ by rw [FundamentalGroup.mapOfEq_id]; simp [e])
  -- `(ContinuousMap.id _).comp e⁻¹` is `e⁻¹` by structure eta. Rewriting with
  -- `ContinuousMap.id_comp` is not possible, since the type of `γ` depends on the map.
  exact ⟨γ, hγ⟩

end General

/-- **The cellular classifying space is isomorphic in `PointedHomotopyCat` to every well-pointed
aspherical space of CW type with the same fundamental group.** Its forward morphism is the pointed
homotopy class of `cellularClassifyingSpaceHomotopyEquiv R hY φ`, inducing `φ` on `π₁`, and its
inverse induces `φ⁻¹` with no base-point change. -/
def cellularClassifyingSpaceHomotopyEquivIso {Y : BasedTopologicalSpace.{u}} [CWType Y.carrier]
    (hY : IsAspherical Y.carrier Y.basepoint)
    (hY_hep : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (φ : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) ≃*
      FundamentalGroup Y.carrier Y.basepoint) :
    PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R) ≅
      PointedHomotopyCat.quotient.obj Y :=
  PointedHomotopyCat.isoOfHomotopyEquiv
    (hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint R) hY_hep
    (cellularClassifyingSpaceHomotopyEquiv R hY φ)
    (cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hY φ)

/-- The forward morphism of `cellularClassifyingSpaceHomotopyEquivIso` is the pointed homotopy
class of `cellularClassifyingSpaceHomotopyEquiv`. -/
theorem cellularClassifyingSpaceHomotopyEquivIso_hom {Y : BasedTopologicalSpace.{u}}
    [CWType Y.carrier] (hY : IsAspherical Y.carrier Y.basepoint)
    (hY_hep : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (φ : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) ≃*
      FundamentalGroup Y.carrier Y.basepoint) :
    (cellularClassifyingSpaceHomotopyEquivIso R hY hY_hep φ).hom =
      PointedHomotopyCat.quotient.map
        ⟨(cellularClassifyingSpaceHomotopyEquiv R hY φ).toFun,
          cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hY φ⟩ :=
  PointedHomotopyCat.isoOfHomotopyEquiv_hom _ _ _ _

/-- The forward morphism of `cellularClassifyingSpaceHomotopyEquivIso` induces `φ` on `π₁`. -/
@[simp]
theorem fundamentalGroupFunctor_map_cellularClassifyingSpaceHomotopyEquivIso_hom
    {Y : BasedTopologicalSpace.{u}} [CWType Y.carrier] (hY : IsAspherical Y.carrier Y.basepoint)
    (hY_hep : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (φ : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) ≃*
      FundamentalGroup Y.carrier Y.basepoint) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (cellularClassifyingSpaceHomotopyEquivIso R hY hY_hep φ).hom =
      GrpCat.ofHom φ.toMonoidHom := by
  rw [cellularClassifyingSpaceHomotopyEquivIso_hom,
    PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map]
  refine GrpCat.hom_ext <| MonoidHom.ext fun a ↦ ?_
  exact mapOfEq_cellularClassifyingSpaceHomotopyEquiv_toFun_apply R hY φ a

/-- The inverse morphism of `cellularClassifyingSpaceHomotopyEquivIso` induces `φ⁻¹` on `π₁`. -/
@[simp]
theorem fundamentalGroupFunctor_map_cellularClassifyingSpaceHomotopyEquivIso_inv
    {Y : BasedTopologicalSpace.{u}} [CWType Y.carrier] (hY : IsAspherical Y.carrier Y.basepoint)
    (hY_hep : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (φ : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) ≃*
      FundamentalGroup Y.carrier Y.basepoint) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (cellularClassifyingSpaceHomotopyEquivIso R hY hY_hep φ).inv =
      GrpCat.ofHom φ.symm.toMonoidHom := by
  have hcomp := congrArg PointedHomotopyCat.fundamentalGroupFunctor.map
    (cellularClassifyingSpaceHomotopyEquivIso R hY hY_hep φ).inv_hom_id
  rw [CategoryTheory.Functor.map_comp,
    fundamentalGroupFunctor_map_cellularClassifyingSpaceHomotopyEquivIso_hom,
    CategoryTheory.Functor.map_id] at hcomp
  refine GrpCat.hom_ext <| MonoidHom.ext fun a ↦ φ.injective ?_
  exact (congrArg (fun f ↦ f.hom a) hcomp).trans (φ.apply_symm_apply a).symm

/-- **Every group has a cellular classifying space**: taking the tautological presentation on the
elements of `G`, with relators the kernel of `FreeGroup G →* G`, gives a presentation `R` whose
cellular classifying space is a `K(G, 1)`. For the stronger existence statement also recording
semilocal simple connectivity via Milnor's model, see
`TauCeti.exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`. -/
theorem exists_cellularClassifyingSpace_isEilenbergMacLaneSpaceOne (G : Type u) [Group G] :
    ∃ R : Set (FreeGroup G),
      IsEilenbergMacLaneSpaceOne G (cellularClassifyingSpace R)
        (cellularClassifyingSpaceBasepoint R) := by
  let φ : FreeGroup G →* G := FreeGroup.lift id
  have hφ : Function.Surjective φ := fun g ↦ ⟨FreeGroup.of g, FreeGroup.lift_apply_of⟩
  let P := Group.Presentation.ofFreeGroupHom φ hφ φ.ker (Subgroup.normalClosure_eq_self _).symm
  exact ⟨P.rel,
    (isEilenbergMacLaneSpaceOne_cellularClassifyingSpace P.rel).of_mulEquiv P.presentedGroupEquiv⟩

end TauCeti
