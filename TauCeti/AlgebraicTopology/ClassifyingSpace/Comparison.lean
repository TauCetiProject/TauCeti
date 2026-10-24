/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Cellular
public import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
public import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
public import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
public import TauCeti.AlgebraicTopology.Homotopy.Whitehead
import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence

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
Whitehead's theorem. The forward map
is determined by `φ` up to homotopy relative to the base point
(`TauCeti.homotopicRel_cellularClassifyingSpaceHomotopyEquiv_toFun`), since the cellular
classifying space has a single `0`-cell. The homotopy inverse need not be pointed; it induces
`φ⁻¹` after a change of base point along a path
(`TauCeti.exists_path_map_cellularClassifyingSpaceHomotopyEquiv_invFun`).

Applied to Milnor's classifying space `TauCeti.classifyingSpace G`, which is a CW complex and a
`K(G, 1)`, this compares the two models of the classifying space of a group: for every
isomorphism `e : PresentedGroup R ≃* G`,
`TauCeti.cellularHomotopyEquivClassifyingSpace R e` is a homotopy equivalence
from the cellular to the simplicial model, inducing `e` under the identifications
`TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv` and
`TauCeti.classifyingSpaceFundamentalGroupMulEquiv` of both fundamental groups. Every group has a
presentation, for instance the tautological one used in
`TauCeti.exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace`, so this applies to every
group.

## Main definitions

* `TauCeti.cellularClassifyingSpaceHomotopyEquiv`: the homotopy equivalence from the cellular
  classifying space to an aspherical space of CW type realizing a given isomorphism of
  fundamental groups by a pointed forward map.
* `TauCeti.cellularHomotopyEquivClassifyingSpace`: the homotopy equivalence from
  the cellular classifying space of a presentation of `G` to Milnor's classifying space of `G`.

## Main results

* `TauCeti.mapOfEq_cellularClassifyingSpaceHomotopyEquiv_toFun_apply`: the forward map induces
  `φ` on fundamental groups.
* `TauCeti.homotopicRel_cellularClassifyingSpaceHomotopyEquiv_toFun`: every pointed map realizing
  `φ` is homotopic to the forward map relative to the base point.
* `TauCeti.exists_path_map_cellularClassifyingSpaceHomotopyEquiv_invFun`:
  the homotopy inverse induces `φ⁻¹`, up to a change of base point.
* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace`
  and its counterpart for the inverse: the comparison of the two models induces `e` and `e⁻¹`
  under the identifications of both fundamental groups with `G`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B, Theorem 1B.8
  and Proposition 1B.9, and Section 4.1, Theorem 4.5.
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

end General

section ClassifyingSpace

variable {G : Type u} [Group G] (e : PresentedGroup R ≃* G)

/-- **The cellular and the simplicial classifying spaces agree.** For a presentation
`e : PresentedGroup R ≃* G` of `G`, this is a homotopy equivalence from the cellular classifying
space `cellularClassifyingSpace R` to Milnor's classifying space `classifyingSpace G`. Its forward
map is pointed and induces `e` under the identifications of both fundamental groups
(`TauCeti.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_cellularHomotopyEquivClassifyingSpace`),
and its homotopy inverse induces `e⁻¹` up to a change of base point
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

end ClassifyingSpace

end TauCeti
