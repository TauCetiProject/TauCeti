/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Cellular
public import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Functoriality.Basic
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.HomotopyEquiv
import TauCeti.AlgebraicTopology.EilenbergMacLane.PointedMaps

/-!
# The cellular and the simplicial classifying spaces agree

Let `⟨S | R⟩` be a group presentation. The cellular classifying space
`TauCeti.cellularClassifyingSpace R` is a CW complex and a `K(PresentedGroup R, 1)`, and for any
aspherical space of CW type it admits a comparison homotopy equivalence
`TauCeti.cellularClassifyingSpaceHomotopyEquiv` (defined in
`TauCeti.AlgebraicTopology.ClassifyingSpace.Cellular`).

Applied to Milnor's classifying space `TauCeti.classifyingSpace G`, which is a well-pointed CW
complex and a `K(G, 1)`, this compares the two models of the classifying space of a group: for
every isomorphism `e : PresentedGroup R ≃* G`,
`TauCeti.cellularHomotopyEquivClassifyingSpace R e` is a homotopy equivalence
from the cellular to the simplicial model, inducing `e` under the identifications
`TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv` and
`TauCeti.classifyingSpaceFundamentalGroupMulEquiv` of both fundamental groups. Every group has
a presentation, for instance the tautological one, so this applies to every group.

Semilocal simple connectivity is a homotopy invariant
(`ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace`), and Milnor's classifying space has
it, so the cellular classifying space is semilocally simply connected as well
(`TauCeti.instSemilocallySimplyConnectedSpaceCellularClassifyingSpace`). Being a Hausdorff CW
complex, it is also locally path-connected. So the existence theorem for the cellular model,
`TauCeti.exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`, carries the standing
hypotheses of covering-space theory exactly as the existence theorem for Milnor's model,
`TauCeti.exists_isEilenbergMacLaneSpaceOne`, does.

## Main definitions

* `TauCeti.cellularHomotopyEquivClassifyingSpace`: the homotopy equivalence from
  the cellular classifying space of a presentation of `G` to Milnor's classifying space of `G`.
* `TauCeti.cellularHomotopyEquivClassifyingSpaceBasedHom`: the comparison of the cellular model
  with Milnor's classifying space, as a based map.

## Main results

* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace`
  and its counterpart for the inverse: the comparison of the two models induces `e` and `e⁻¹`
  under the identifications of both fundamental groups with `G`.
* `TauCeti.homotopicRel_cellularHomotopyEquivClassifyingSpace_toFun`: the comparison of the two
  models is determined by `e` up to homotopy relative to the base point.
* `TauCeti.fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace`: pointed homotopy
  classes of maps out of a cellular classifying space into a space with no higher homotopy groups
  are classified by their effect on `π₁`.
* `TauCeti.quotient_map_eq_quotient_map_comp_cellularClassifyingSpace`: a pointed map from the
  cellular model realizing a homomorphism is pointed homotopic to the comparison of the two models
  followed by the strictly functorial map.
* `TauCeti.instSemilocallySimplyConnectedSpaceCellularClassifyingSpace`: the cellular classifying
  space is semilocally simply connected.
* `TauCeti.exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`: every group `G` has a
  presentation whose cellular classifying space is a `K(G, 1)`, locally path-connected and
  semilocally simply connected.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (Proposition 0.19),
  Section 1.B, Theorem 1B.8 and Proposition 1B.9, and Section 4.1, Theorem 4.5.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open scoped Topology Topology.Homotopy ContinuousMap

open FundamentalGroup

universe u

namespace TauCeti

variable {S : Type u} (R : Set (FreeGroup S))

section ClassifyingSpace

variable {G : Type u} [Group G] (e : PresentedGroup R ≃* G)

/-- **The cellular and the simplicial classifying spaces agree.** For a presentation
`e : PresentedGroup R ≃* G` of `G`, this is a homotopy equivalence from the cellular classifying
space `cellularClassifyingSpace R` to Milnor's classifying space `classifyingSpace G`. Its forward
map is pointed, induces `e` under the identifications of both fundamental groups
(`TauCeti.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace`),
and is unique up to pointed homotopy
(`TauCeti.homotopicRel_cellularHomotopyEquivClassifyingSpace_toFun`). Its homotopy inverse
induces `e⁻¹` up to a change of base point
(`TauCeti.exists_path_map_cellularHomotopyEquivClassifyingSpace_invFun`). -/
def cellularHomotopyEquivClassifyingSpace :
    cellularClassifyingSpace R ≃ₕ classifyingSpace G :=
  cellularClassifyingSpaceHomotopyEquiv R
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
    ((cellularClassifyingSpaceFundamentalGroupMulEquiv R).trans
      (e.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm))

/-- The comparison of the two models preserves the base points. -/
@[simp]
theorem cellularHomotopyEquivClassifyingSpace_toFun_basepoint :
    (cellularHomotopyEquivClassifyingSpace R e).toFun
        (cellularClassifyingSpaceBasepoint R) =
      classifyingSpaceBasepoint G :=
  cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R _ _

/-- **The comparison of the two models induces `e` on fundamental groups**, under the
identifications `cellularClassifyingSpaceFundamentalGroupMulEquiv R` with `PresentedGroup R` and
`classifyingSpaceFundamentalGroupMulEquiv G` with `G`. -/
@[simp]
theorem classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace
    (a : FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R)) :
    classifyingSpaceFundamentalGroupMulEquiv G
        (FundamentalGroup.mapOfEq (cellularHomotopyEquivClassifyingSpace R e).toFun
          (cellularHomotopyEquivClassifyingSpace_toFun_basepoint R e) a) =
      e (cellularClassifyingSpaceFundamentalGroupMulEquiv R a) := by
  simp [cellularHomotopyEquivClassifyingSpace]

/-- **The comparison of the two models is determined by `e` up to pointed homotopy.** Every map
from the cellular classifying space to `classifyingSpace G` that preserves the base points and
induces `e` under the identifications of both fundamental groups is homotopic to it relative to the
base point. -/
theorem homotopicRel_cellularHomotopyEquivClassifyingSpace_toFun
    {f : C(cellularClassifyingSpace R, classifyingSpace G)}
    (hf : f (cellularClassifyingSpaceBasepoint R) = classifyingSpaceBasepoint G)
    (hfe : ∀ a, classifyingSpaceFundamentalGroupMulEquiv G (FundamentalGroup.mapOfEq f hf a) =
      e (cellularClassifyingSpaceFundamentalGroupMulEquiv R a)) :
    f.HomotopicRel (cellularHomotopyEquivClassifyingSpace R e).toFun
      {cellularClassifyingSpaceBasepoint R} :=
  homotopicRel_cellularClassifyingSpaceHomotopyEquiv_toFun R _ _ hf fun a ↦
    (classifyingSpaceFundamentalGroupMulEquiv G).injective (by simp [hfe])

/-- **The homotopy inverse of the comparison of the two models induces `e⁻¹`**, up to a change of
base point: there is a path `γ` from its value at the base point of `classifyingSpace G` to the base
point of the cellular classifying space such that the induced map, followed by basepoint change
along `γ`, is `e⁻¹` under the identifications of both fundamental groups. -/
theorem exists_path_map_cellularHomotopyEquivClassifyingSpace_invFun :
    ∃ γ : Path ((cellularHomotopyEquivClassifyingSpace R e).invFun
        (classifyingSpaceBasepoint G)) (cellularClassifyingSpaceBasepoint R),
      ∀ a, cellularClassifyingSpaceFundamentalGroupMulEquiv R (fundamentalGroupMulEquivOfPath γ
          (map (cellularHomotopyEquivClassifyingSpace R e).invFun _ a)) =
        e.symm (classifyingSpaceFundamentalGroupMulEquiv G a) := by
  unfold cellularHomotopyEquivClassifyingSpace
  obtain ⟨γ, hγ⟩ :=
    exists_path_map_cellularClassifyingSpaceHomotopyEquiv_invFun R
      (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
      ((cellularClassifyingSpaceFundamentalGroupMulEquiv R).trans
        (e.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm))
  exact ⟨γ, fun a ↦ by
    rw [hγ, MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm]⟩

/-- The comparison `cellularHomotopyEquivClassifyingSpace R e` of the cellular model with Milnor's
classifying space, as a based map. -/
@[expose] def cellularHomotopyEquivClassifyingSpaceBasedHom :
    cellularClassifyingSpaceBased R ⟶ classifyingSpaceFunctor.obj (GrpCat.of G) :=
  ⟨(cellularHomotopyEquivClassifyingSpace R e).toFun,
    cellularHomotopyEquivClassifyingSpace_toFun_basepoint R e⟩

@[simp]
theorem cellularHomotopyEquivClassifyingSpaceBasedHom_toContinuousMap :
    (cellularHomotopyEquivClassifyingSpaceBasedHom R e).toContinuousMap =
      (cellularHomotopyEquivClassifyingSpace R e).toFun :=
  (rfl)

/-- **The cellular classifying space is semilocally simply connected.** It is homotopy equivalent
to Milnor's classifying space of its fundamental group, which is semilocally simply connected, and
semilocal simple connectivity is a homotopy invariant. -/
instance instSemilocallySimplyConnectedSpaceCellularClassifyingSpace :
    SemilocallySimplyConnectedSpace (cellularClassifyingSpace R) :=
  (cellularHomotopyEquivClassifyingSpace R (MulEquiv.refl _)).semilocallySimplyConnectedSpace

end ClassifyingSpace

/-- **Pointed maps out of a cellular classifying space are classified by `π₁`.** If the homotopy
groups of `Y` vanish from degree `2` on, at every point, then a pointed homotopy class of maps from
the cellular classifying space `cellularClassifyingSpace R` to `Y` is determined by the homomorphism
it induces on fundamental groups, and every homomorphism is induced by such a class. -/
theorem fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace
    {Y : BasedTopologicalSpace.{u}}
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := PointedHomotopyCat.quotient.obj (cellularClassifyingSpaceBased R))
      (Y := PointedHomotopyCat.quotient.obj Y)) :=
  IsAspherical.fundamentalGroupFunctor_map_bijective
    (X := cellularClassifyingSpaceBased R)
    (isEilenbergMacLaneSpaceOne_cellularClassifyingSpace R).isAspherical
    (hasHomotopyExtensionProperty_cellularClassifyingSpaceBasepoint R) hY

open CategoryTheory in
/-- **The map induced by a homomorphism is determined up to pointed homotopy.** Let
`e : PresentedGroup R ≃* G` be a presentation and `φ : G ⟶ H`. Every pointed map from the cellular
classifying space of `R` to `classifyingSpace H` that induces `φ` under the identifications of both
fundamental groups is pointed homotopic to the comparison map of
`cellularHomotopyEquivClassifyingSpace R e` followed by `classifyingSpaceFunctor.map φ`. -/
theorem quotient_map_eq_quotient_map_comp_cellularClassifyingSpace {G H : GrpCat.{u}}
    (e : PresentedGroup R ≃* G) (φ : G ⟶ H)
    (f : cellularClassifyingSpaceBased R ⟶ classifyingSpaceFunctor.obj H)
    (hf : ∀ a, classifyingSpaceFundamentalGroupMulEquiv H
        ((BasedTopologicalSpace.fundamentalGroupFunctor.map f).hom a) =
      φ.hom (e (cellularClassifyingSpaceFundamentalGroupMulEquiv R a))) :
    PointedHomotopyCat.quotient.map f =
      PointedHomotopyCat.quotient.map
        (cellularHomotopyEquivClassifyingSpaceBasedHom R e ≫ classifyingSpaceFunctor.map φ) := by
  refine (fundamentalGroupFunctor_map_bijective_cellularClassifyingSpace R
    (fun y n ↦ subsingleton_homotopyGroup_classifyingSpace H n y)).1 ?_
  simp only [PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map]
  rw [Functor.map_comp]
  refine GrpCat.hom_ext <| MonoidHom.ext fun a ↦
    (classifyingSpaceFundamentalGroupMulEquiv H).injective ?_
  simp only [GrpCat.hom_comp, BasedTopologicalSpace.fundamentalGroupFunctor_map_hom,
    cellularHomotopyEquivClassifyingSpaceBasedHom_toContinuousMap] at hf ⊢
  -- Both sides are `φ ∘ e` under the identifications: the comparison induces `e`, and the strict
  -- map induces `φ`.
  exact (hf a).trans <| (congrArg φ.hom
    (classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace R e
      a).symm).trans (φ.hom.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq _).symm

/-- **Every group has a cellular classifying space**, satisfying the standing hypotheses of
covering-space theory: for every group `G` there is a set `R` of relators on the generators `G`
such that the cellular classifying space of `⟨G | R⟩` is a locally path-connected, semilocally
simply connected `K(G, 1)`. Take the tautological presentation, whose relators are the kernel of
the evaluation map `FreeGroup G →* G`. No hypothesis on the group is needed. This is the cellular
counterpart of `TauCeti.exists_isEilenbergMacLaneSpaceOne`. -/
theorem exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace (G : Type u) [Group G] :
    ∃ R : Set (FreeGroup G), LocallyPathConnectedSpace (cellularClassifyingSpace R) ∧
      SemilocallySimplyConnectedSpace (cellularClassifyingSpace R) ∧
      IsEilenbergMacLaneSpaceOne G (cellularClassifyingSpace R)
        (cellularClassifyingSpaceBasepoint R) :=
  ⟨_, inferInstance, inferInstance, isEilenbergMacLaneSpaceOne_cellularClassifyingSpace_ker G⟩

end TauCeti
