/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Presentation
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Cellular
public import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
public import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
public import TauCeti.AlgebraicTopology.Homotopy.Whitehead
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.HomotopyEquiv
import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence
import TauCeti.Topology.Homotopy.Extension.CWComplex
import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel

/-!
# The cellular and the simplicial classifying spaces agree

Let `⟨S | R⟩` be a group presentation. The cellular classifying space
`TauCeti.cellularClassifyingSpace R` is a CW complex and a `K(PresentedGroup R, 1)`. Out of it,
every isomorphism `φ` of its fundamental group with the fundamental group of an aspherical space
`Y` of CW type is realized by a homotopy equivalence
`TauCeti.cellularClassifyingSpaceHomotopyEquiv R hY φ : cellularClassifyingSpace R ≃ₕ Y`, whose
forward map is *pointed*: it sends the base point to `y` and induces exactly `φ` on fundamental
groups. A pointed map realizing `φ` exists (`TauCeti.exists_mapOfEq_cellularClassifyingSpace`); it
is a weak homotopy equivalence because both spaces are aspherical, hence a homotopy equivalence by
Whitehead's theorem. The forward map is determined by `φ` up to homotopy relative to the base point
(`TauCeti.homotopicRel_cellularClassifyingSpaceHomotopyEquiv_toFun`), since the cellular
classifying space has a single `0`-cell. In general the homotopy inverse need not be pointed; it
induces `φ⁻¹` after a change of base point along a path
(`TauCeti.exists_path_map_cellularClassifyingSpaceHomotopyEquiv_invFun`). When the base point `y`
of `Y` has the homotopy extension property, the inverse upgrades to a *pointed* homotopy inverse
whose composites with the forward map are homotopic to the identities relative to the base points
and which induces `φ⁻¹` directly
(`TauCeti.exists_basedInverse_cellularClassifyingSpaceHomotopyEquiv`).

Applied to Milnor's classifying space `TauCeti.classifyingSpace G`, which is a Hausdorff CW complex
and a `K(G, 1)` (so its base point has the homotopy extension property by
`TauCeti.hasHomotopyExtensionProperty_singleton_of_cwComplex`), this compares the two models
of the classifying space of a group: for every isomorphism `e : PresentedGroup R ≃* G`,
`TauCeti.cellularHomotopyEquivClassifyingSpace R e` is a *pointed* homotopy equivalence from the
cellular to the simplicial model, whose forward and inverse maps both preserve base points, whose
composites are homotopic to the identities relative to the base points, and which induce `e` and
`e⁻¹` under the identifications `TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv` and
`TauCeti.classifyingSpaceFundamentalGroupMulEquiv` of both fundamental groups. Every group has a
presentation, for instance the tautological one, so this applies to every group.

Semilocal simple connectivity is a homotopy invariant
(`ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace`), and Milnor's classifying space has
it, so the cellular classifying space is semilocally simply connected as well
(`TauCeti.instSemilocallySimplyConnectedSpaceCellularClassifyingSpace`). Being a Hausdorff CW
complex, it is also locally path-connected. So the existence theorem for the cellular model,
`TauCeti.exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`, carries the standing
hypotheses of covering-space theory exactly as the existence theorem for Milnor's model,
`TauCeti.exists_isEilenbergMacLaneSpaceOne`, does.

## Main definitions

* `TauCeti.cellularClassifyingSpaceHomotopyEquiv`: the homotopy equivalence from the cellular
  classifying space to an aspherical space of CW type realizing a given isomorphism of
  fundamental groups by a pointed forward map.
* `TauCeti.cellularHomotopyEquivClassifyingSpace`: the pointed homotopy equivalence from
  the cellular classifying space of a presentation of `G` to Milnor's classifying space of `G`.

## Main results

* `TauCeti.mapOfEq_cellularClassifyingSpaceHomotopyEquiv_toFun_apply`: the forward map induces
  `φ` on fundamental groups.
* `TauCeti.homotopicRel_cellularClassifyingSpaceHomotopyEquiv_toFun`: every pointed map realizing
  `φ` is homotopic to the forward map relative to the base point.
* `TauCeti.exists_path_map_cellularClassifyingSpaceHomotopyEquiv_invFun`:
  the homotopy inverse induces `φ⁻¹`, up to a change of base point.
* `TauCeti.exists_basedInverse_cellularClassifyingSpaceHomotopyEquiv`: when `{y}` has the homotopy
  extension property, there is a pointed homotopy inverse inducing `φ⁻¹` with both composites
  homotopic to the identities relative to the base points.
* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace`
  and `TauCeti.mapOfEq_cellularHomotopyEquivClassifyingSpace_invFun`:
  the comparison of the two models and its pointed inverse induce `e` and `e⁻¹` under the
  identifications of both fundamental groups with `G`.
* `TauCeti.cellularHomotopyEquivClassifyingSpace_left_inv_homotopicRel` and
  `TauCeti.cellularHomotopyEquivClassifyingSpace_right_inv_homotopicRel`: both composites of the
  comparison equivalence are homotopic to the identities relative to the base points.
* `TauCeti.homotopicRel_cellularHomotopyEquivClassifyingSpace_toFun`: the comparison of the two
  models is determined by `e` up to homotopy relative to the base point.
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
      ∀ a, fundamentalGroupMulEquivOfPath γ
        (map (cellularClassifyingSpaceHomotopyEquiv R hY φ).invFun y a) = φ.symm a := by
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

/-- **Based homotopy inverse of `TauCeti.cellularClassifyingSpaceHomotopyEquiv`.** When the base
point `y` of `Y` has the homotopy extension property, the forward map of
`cellularClassifyingSpaceHomotopyEquiv R hY φ` admits a pointed homotopy inverse `g` sending `y`
to `cellularClassifyingSpaceBasepoint R`, with both composites homotopic to the identities
relative to the base points, and inducing `φ⁻¹` on fundamental groups with no change of base
point. -/
theorem exists_basedInverse_cellularClassifyingSpaceHomotopyEquiv
    (hy : HasHomotopyExtensionProperty ({y} : Set Y)) :
    ∃ (g : C(Y, cellularClassifyingSpace R))
      (hg : g y = cellularClassifyingSpaceBasepoint R),
      (g.comp (cellularClassifyingSpaceHomotopyEquiv R hY φ).toFun).HomotopicRel
        (ContinuousMap.id (cellularClassifyingSpace R))
        {cellularClassifyingSpaceBasepoint R} ∧
      ((cellularClassifyingSpaceHomotopyEquiv R hY φ).toFun.comp g).HomotopicRel
        (ContinuousMap.id Y) {y} ∧
      FundamentalGroup.mapOfEq g hg = φ.symm.toMonoidHom := by
  set e := cellularClassifyingSpaceHomotopyEquiv R hY φ
  have hbase : HasHomotopyExtensionProperty
      ({cellularClassifyingSpaceBasepoint R} : Set (cellularClassifyingSpace R)) :=
    hasHomotopyExtensionProperty_singleton_of_cwComplex _
  obtain ⟨g, hg, hgf, hfg⟩ := hbase.exists_basedInverse_homotopicRel hy e
    (cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hY φ)
  refine ⟨g, hg, hgf, hfg, MonoidHom.ext fun a ↦ ?_⟩
  apply φ.injective
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have hf := cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hY φ
  have hcomp_bp : (e.toFun.comp g) y = y := by
    rw [ContinuousMap.comp_apply, hg, hf]
  have hmap := DFunLike.congr_fun
    (FundamentalGroup.mapOfEq_eq_of_homotopicRel hcomp_bp (ContinuousMap.id_apply y) rfl hfg) a
  rw [FundamentalGroup.mapOfEq_id] at hmap
  rw [← mapOfEq_cellularClassifyingSpaceHomotopyEquiv_toFun_apply R hY φ]
  exact (FundamentalGroup.mapOfEq_comp e.toFun g hg hf a).trans hmap

end General

section ClassifyingSpace

variable {G : Type u} [Group G] (e : PresentedGroup R ≃* G)

/-- The isomorphism of fundamental groups induced by `e : PresentedGroup R ≃* G` between the
cellular and simplicial classifying spaces. -/
private def comparisonMulEquiv :
    FundamentalGroup (cellularClassifyingSpace R) (cellularClassifyingSpaceBasepoint R) ≃*
      FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G) :=
  (cellularClassifyingSpaceFundamentalGroupMulEquiv R).trans
    (e.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)

private theorem exists_basedInverse_comparison :
    ∃ (g : C(classifyingSpace G, cellularClassifyingSpace R))
      (hg : g (classifyingSpaceBasepoint G) = cellularClassifyingSpaceBasepoint R),
      (g.comp (cellularClassifyingSpaceHomotopyEquiv R
        (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
        (comparisonMulEquiv R e)).toFun).HomotopicRel
        (ContinuousMap.id (cellularClassifyingSpace R))
        {cellularClassifyingSpaceBasepoint R} ∧
      ((cellularClassifyingSpaceHomotopyEquiv R
        (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
        (comparisonMulEquiv R e)).toFun.comp g).HomotopicRel
        (ContinuousMap.id (classifyingSpace G)) {classifyingSpaceBasepoint G} ∧
      FundamentalGroup.mapOfEq g hg = (comparisonMulEquiv R e).symm.toMonoidHom :=
  exists_basedInverse_cellularClassifyingSpaceHomotopyEquiv R
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
    (comparisonMulEquiv R e)
    (hasHomotopyExtensionProperty_singleton_of_cwComplex (classifyingSpaceBasepoint G))

/-- **The cellular and the simplicial classifying spaces agree.** For a presentation
`e : PresentedGroup R ≃* G` of `G`, this is a pointed homotopy equivalence from the cellular
classifying space `cellularClassifyingSpace R` to Milnor's classifying space `classifyingSpace G`.
Both its forward and inverse maps preserve base points, both composites are homotopic to the
identities relative to the base points
(`TauCeti.cellularHomotopyEquivClassifyingSpace_left_inv_homotopicRel`,
`TauCeti.cellularHomotopyEquivClassifyingSpace_right_inv_homotopicRel`), the forward map induces
`e`
(`TauCeti.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace`)
and is unique up to pointed homotopy
(`TauCeti.homotopicRel_cellularHomotopyEquivClassifyingSpace_toFun`), and the inverse induces
`e⁻¹` (`TauCeti.mapOfEq_cellularHomotopyEquivClassifyingSpace_invFun`). -/
def cellularHomotopyEquivClassifyingSpace :
    cellularClassifyingSpace R ≃ₕ classifyingSpace G where
  toFun := (cellularClassifyingSpaceHomotopyEquiv R
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
    (comparisonMulEquiv R e)).toFun
  invFun := (exists_basedInverse_comparison R e).choose
  left_inv := (exists_basedInverse_comparison R e).choose_spec.choose_spec.1.homotopic
  right_inv := (exists_basedInverse_comparison R e).choose_spec.choose_spec.2.1.homotopic

/-- The forward map of `TauCeti.cellularHomotopyEquivClassifyingSpace` preserves the base points. -/
@[simp]
theorem cellularHomotopyEquivClassifyingSpace_toFun_basepoint :
    (cellularHomotopyEquivClassifyingSpace R e).toFun
        (cellularClassifyingSpaceBasepoint R) =
      classifyingSpaceBasepoint G :=
  cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R _ _

/-- The inverse map of `TauCeti.cellularHomotopyEquivClassifyingSpace` preserves the base points. -/
@[simp]
theorem cellularHomotopyEquivClassifyingSpace_invFun_basepoint :
    (cellularHomotopyEquivClassifyingSpace R e).invFun (classifyingSpaceBasepoint G) =
      cellularClassifyingSpaceBasepoint R :=
  (exists_basedInverse_comparison R e).choose_spec.choose

/-- The left composite of `TauCeti.cellularHomotopyEquivClassifyingSpace` is homotopic to the
identity relative to the base point of the cellular classifying space. -/
theorem cellularHomotopyEquivClassifyingSpace_left_inv_homotopicRel :
    ((cellularHomotopyEquivClassifyingSpace R e).invFun.comp
        (cellularHomotopyEquivClassifyingSpace R e).toFun).HomotopicRel
      (ContinuousMap.id (cellularClassifyingSpace R)) {cellularClassifyingSpaceBasepoint R} :=
  (exists_basedInverse_comparison R e).choose_spec.choose_spec.1

/-- The right composite of `TauCeti.cellularHomotopyEquivClassifyingSpace` is homotopic to the
identity relative to the base point of Milnor's classifying space. -/
theorem cellularHomotopyEquivClassifyingSpace_right_inv_homotopicRel :
    ((cellularHomotopyEquivClassifyingSpace R e).toFun.comp
        (cellularHomotopyEquivClassifyingSpace R e).invFun).HomotopicRel
      (ContinuousMap.id (classifyingSpace G)) {classifyingSpaceBasepoint G} :=
  (exists_basedInverse_comparison R e).choose_spec.choose_spec.2.1

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
  simp [cellularHomotopyEquivClassifyingSpace, comparisonMulEquiv]

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
    (classifyingSpaceFundamentalGroupMulEquiv G).injective (by simp [comparisonMulEquiv, hfe])

/-- **The pointed inverse of the comparison of the two models induces `e⁻¹` on fundamental
groups**, under the identifications `classifyingSpaceFundamentalGroupMulEquiv G` with `G` and
`cellularClassifyingSpaceFundamentalGroupMulEquiv R` with `PresentedGroup R`. -/
@[simp]
theorem mapOfEq_cellularHomotopyEquivClassifyingSpace_invFun
    (a : FundamentalGroup (classifyingSpace G) (classifyingSpaceBasepoint G)) :
    FundamentalGroup.mapOfEq (cellularHomotopyEquivClassifyingSpace R e).invFun
        (cellularHomotopyEquivClassifyingSpace_invFun_basepoint R e) a =
      (cellularClassifyingSpaceFundamentalGroupMulEquiv R).symm
        (e.symm (classifyingSpaceFundamentalGroupMulEquiv G a)) := by
  have h := DFunLike.congr_fun
    (exists_basedInverse_comparison R e).choose_spec.choose_spec.2.2 a
  exact h.trans <| by simp [comparisonMulEquiv]

/-- **The cellular classifying space is semilocally simply connected.** It is homotopy equivalent
to Milnor's classifying space of its fundamental group, which is semilocally simply connected, and
semilocal simple connectivity is a homotopy invariant. -/
instance instSemilocallySimplyConnectedSpaceCellularClassifyingSpace :
    SemilocallySimplyConnectedSpace (cellularClassifyingSpace R) :=
  (cellularHomotopyEquivClassifyingSpace R (MulEquiv.refl _)).semilocallySimplyConnectedSpace

end ClassifyingSpace

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
        (cellularClassifyingSpaceBasepoint R) := by
  let φ : FreeGroup G →* G := FreeGroup.lift id
  have hφ : Function.Surjective φ := fun g ↦ ⟨FreeGroup.of g, FreeGroup.lift_apply_of⟩
  let P := Group.Presentation.ofFreeGroupHom φ hφ φ.ker (Subgroup.normalClosure_eq_self _).symm
  exact ⟨P.rel, inferInstance, inferInstance,
    (isEilenbergMacLaneSpaceOne_cellularClassifyingSpace P.rel).of_mulEquiv P.presentedGroupEquiv⟩

end TauCeti
