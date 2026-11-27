/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
public import TauCeti.Topology.CWComplex.Classical.CWType
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
import TauCeti.AlgebraicTopology.ClassifyingSpace.MapsToAspherical
import TauCeti.AlgebraicTopology.EilenbergMacLane.Homotopic
import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic

/-!
# Uniqueness of `K(G, 1)` spaces of CW type

Two aspherical spaces of CW type with isomorphic fundamental groups are homotopy equivalent, and
the homotopy equivalence can be chosen to realize any prescribed isomorphism
`φ : π₁(X, x) ≃* π₁(Y, y)` (`TauCeti.IsAspherical.exists_homotopyEquiv`). A homotopy equivalence
`e` need not send `x` to `y`, so realizing `φ` means: there is a path `γ` from `e x` to `y` such
that the map induced by `e` on fundamental groups, followed by basepoint change along `γ`, is `φ`.
In particular any two `K(G, 1)` spaces of CW type are homotopy equivalent
(`TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv`), and every `K(G, 1)` space of CW
type is homotopy equivalent to Milnor's classifying space `TauCeti.classifyingSpace G`, compatibly
with the identifications of both fundamental groups with `G`
(`TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace`). So the classifying space is well
defined up to homotopy equivalence among spaces of CW type.

When `X` and `Y` carry actual Hausdorff CW structures (possibly in different universes), Hatcher's
Proposition 1B.9 (`TauCeti.exists_mapOfEq_of_cwComplex` and
`TauCeti.homotopicRel_of_mapOfEq_eq_of_cwComplex`) strengthens this to a *based* homotopy
equivalence (`TauCeti.IsAspherical.exists_basedHomotopyEquiv`): `φ` and `φ⁻¹` are realized on the
nose by basepoint-preserving maps whose two composites are homotopic to the identity relative to
`{x}` and `{y}` (in particular giving a homotopy equivalence whose forward map sends `x` to `y` and
induces `φ`, `TauCeti.exists_homotopyEquiv_of_isAspherical`). Specializing `Y` to
`classifyingSpace G` gives a based homotopy equivalence between any aspherical Hausdorff CW complex
and Milnor's classifying space (`TauCeti.IsAspherical.exists_basedHomotopyEquiv_classifyingSpace`).

For spaces merely of CW type, the cellular classifying space `C` of a presentation of `π₁(X, x)` is
homotopy equivalent to both spaces by homotopy equivalences `f : C ≃ₕ X` and `g : C ≃ₕ Y` whose
forward maps are pointed and realize an identification `ψ` and `φ ∘ ψ`
(`TauCeti.cellularClassifyingSpaceHomotopyEquiv`). The composite `g ∘ f⁻¹` is the required homotopy
equivalence. The homotopy from `f ∘ f⁻¹` to the identity moves the base point, which is why the
realization of `φ` involves a change of base point
(`ContinuousMap.Homotopy.exists_path_fundamentalGroupMulEquivOfPath_map_comp`).

The hypothesis of CW type on both spaces cannot be dropped: a point and the Warsaw circle are both
path connected with trivial homotopy groups, but they are not homotopy equivalent.

Without it, the classifying space still maps to every aspherical space by a weak homotopy
equivalence realizing a prescribed identification of the fundamental group with `G`
(`TauCeti.IsAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace`), which is the case
`n = 1` of Hatcher's Proposition 4.30. The map factors through the CW approximation of the
target, which is an aspherical space of CW type and hence homotopy equivalent to
`classifyingSpace G`. So `classifyingSpace G` computes every weak homotopy invariant, for instance
the singular homology, of an arbitrary `K(G, 1)` space, such as the loop space of a `K(G, 2)` space
for abelian `G`, which need not have CW type.

## Main results

* `TauCeti.IsAspherical.exists_homotopyEquiv`: **aspherical spaces of CW type are homotopy
  equivalent by a homotopy equivalence realizing any prescribed isomorphism of fundamental
  groups.**
* `TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv`: two `K(G, 1)` spaces of CW type are
  homotopy equivalent.
* `TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace`: an aspherical space of CW type
  with fundamental group identified with `G` is homotopy equivalent to `classifyingSpace G`,
  compatibly with the identifications of fundamental groups.
* `TauCeti.IsAspherical.exists_basedHomotopyEquiv`: **based homotopy equivalence of aspherical
  Hausdorff CW complexes** realizing any prescribed isomorphism of fundamental groups (with pointed
  inverse and homotopies relative to `{x}` and `{y}`).
* `TauCeti.exists_homotopyEquiv_of_isAspherical`: homotopy equivalence of aspherical Hausdorff CW
  complexes whose forward map sends `x` to `y` and induces `φ`.
* `TauCeti.IsAspherical.exists_basedHomotopyEquiv_classifyingSpace`: based homotopy equivalence of
  an aspherical Hausdorff CW complex with `classifyingSpace G`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B, Theorem 1B.8
  and Proposition 1B.9, and Section 4.1, Theorem 4.5 and Proposition 4.22.
* R. Schwamberger and R. M. Vogt, *Dold spaces in homotopy theory*, Algebr. Geom. Topol. 9
  (2009), 1585--1622, for the Warsaw circle.
-/

public section

open scoped Topology Topology.Homotopy ContinuousMap

open FundamentalGroup

universe u v

namespace TauCeti

/-- **Uniqueness of aspherical spaces of CW type.** Two aspherical spaces of CW type are homotopy
equivalent by a homotopy equivalence realizing any prescribed isomorphism `φ` of their fundamental
groups: there is a homotopy equivalence `e` and a path `γ` from `e x` to `y` such that the map
induced by `e` on fundamental groups, followed by basepoint change along `γ`, is `φ`.

The hypothesis of CW type on both spaces cannot be dropped: a point and the Warsaw circle are
aspherical with trivial fundamental groups, but they are not homotopy equivalent. -/
theorem IsAspherical.exists_homotopyEquiv {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [CWType X] [CWType Y] {x : X} {y : Y} (hX : IsAspherical X x)
    (hY : IsAspherical Y y) (φ : FundamentalGroup X x ≃* FundamentalGroup Y y) :
    ∃ (e : X ≃ₕ Y) (γ : Path (e.toFun x) y),
      ∀ a, fundamentalGroupMulEquivOfPath γ (map e.toFun x a) = φ a := by
  obtain ⟨R, -, -, hC⟩ :=
    exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace (FundamentalGroup X x)
  obtain ⟨ψ⟩ := hC.nonempty_fundamentalGroupMulEquiv
  have : PathConnectedSpace (cellularClassifyingSpace R) := hC.isAspherical.pathConnectedSpace
  -- Pointed homotopy equivalences from the cellular classifying space realizing `ψ` and `φ ∘ ψ`.
  set f := cellularClassifyingSpaceHomotopyEquiv R hX ψ
  set g := cellularClassifyingSpaceHomotopyEquiv R hY (ψ.trans φ)
  -- `f⁻¹` is a homotopy right inverse of `f`, so `g ∘ f⁻¹` realizes `φ` up to basepoint change.
  refine ⟨f.symm.trans g, f.right_inv.some.exists_path_fundamentalGroupMulEquivOfPath_map_comp
    (cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hX ψ)
    (cellularClassifyingSpaceHomotopyEquiv_toFun_basepoint R hY (ψ.trans φ)) φ.toMonoidHom
    (MonoidHom.ext fun a ↦ by simp [f])⟩

/-- **Two `K(G, 1)` spaces of CW type are homotopy equivalent.** See
`TauCeti.IsAspherical.exists_homotopyEquiv` for a homotopy equivalence realizing a prescribed
isomorphism of fundamental groups. -/
theorem IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv {G : Type v} [Group G]
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [CWType X] [CWType Y] {x : X} {y : Y}
    (hX : IsEilenbergMacLaneSpaceOne G X x) (hY : IsEilenbergMacLaneSpaceOne G Y y) :
    Nonempty (X ≃ₕ Y) := by
  obtain ⟨eX⟩ := hX.nonempty_fundamentalGroupMulEquiv
  obtain ⟨eY⟩ := hY.nonempty_fundamentalGroupMulEquiv
  obtain ⟨e, -⟩ := IsAspherical.exists_homotopyEquiv hX.isAspherical hY.isAspherical
    (eX.trans eY.symm)
  exact ⟨e⟩

/-- **Milnor's classifying space is the unique `K(G, 1)` of CW type.** An aspherical space `X` of
CW type whose fundamental group is identified with `G` by `eX` is homotopy equivalent to
`classifyingSpace G`, by a homotopy equivalence `e` compatible with the identifications: for a
suitable path `γ` from `e x` to the base point, the map induced by `e`, followed by basepoint
change along `γ` and the identification `classifyingSpaceFundamentalGroupMulEquiv G`, is `eX`. -/
theorem IsAspherical.exists_homotopyEquiv_classifyingSpace {G : Type u} [Group G] {X : Type u}
    [TopologicalSpace X] [CWType X] {x : X} (hX : IsAspherical X x)
    (eX : FundamentalGroup X x ≃* G) :
    ∃ (e : X ≃ₕ classifyingSpace G) (γ : Path (e.toFun x) (classifyingSpaceBasepoint G)),
      ∀ a, classifyingSpaceFundamentalGroupMulEquiv G
        (fundamentalGroupMulEquivOfPath γ (map e.toFun x a)) = eX a := by
  obtain ⟨e, γ, h⟩ := hX.exists_homotopyEquiv
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
    (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)
  exact ⟨e, γ, fun a ↦ by rw [h, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]⟩

/-- A weak homotopy equivalence `c : W → X` out of a space of CW type, followed by a homotopy
equivalence from `classifyingSpace G` to `W`, realizes a prescribed identification of the
fundamental group of an aspherical space `X` with `G`. -/
private theorem exists_isWeakHomotopyEquivalence_classifyingSpace_of_cwType {G : Type u}
    [Group G] {W X : Type u} [TopologicalSpace W] [CWType W] [TopologicalSpace X] {w : W} {x : X}
    {c : C(W, X)} (hc : c.IsWeakHomotopyEquivalence) (hcw : c w = x) (hX : IsAspherical X x)
    (eX : FundamentalGroup X x ≃* G) :
    ∃ (f : C(classifyingSpace G, X)) (γ : Path (f (classifyingSpaceBasepoint G)) x),
      f.IsWeakHomotopyEquivalence ∧
        ∀ a, eX (fundamentalGroupMulEquivOfPath γ (map f _ a)) =
          classifyingSpaceFundamentalGroupMulEquiv G a := by
  subst hcw
  -- `W` is aspherical, and `c` identifies its fundamental group with that of `X`.
  have hW : IsAspherical W w := (hc.isAspherical_iff w).2 hX
  let ψ := MulEquiv.ofBijective (map c w) (mapOfEq_rfl c ▸ hc.mapOfEq_bijective rfl)
  obtain ⟨e, γ, he⟩ :=
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical.exists_homotopyEquiv hW
      ((classifyingSpaceFundamentalGroupMulEquiv G).trans (eX.symm.trans ψ.symm))
  refine ⟨c.comp e.toFun, γ.map c.continuous, hc.comp e.isWeakHomotopyEquivalence, fun a ↦ ?_⟩
  rw [map_comp, MonoidHom.comp_apply, ← map_fundamentalGroupMulEquivOfPath, he]
  simp [ψ, MulEquiv.ofBijective_apply_symm_apply]

/-- **Every aspherical space receives a weak homotopy equivalence from the classifying space**
(Hatcher, Proposition 4.30 for `n = 1`). For an aspherical space `X`, of any kind, whose
fundamental group is identified with `G` by `eX`, there is a weak homotopy equivalence
`f : classifyingSpace G → X` compatible with the identifications: for a suitable path `γ` from
`f` of the base point to `x`, the map induced by `f`, followed by basepoint change along `γ` and
`eX`, is `classifyingSpaceFundamentalGroupMulEquiv G`.

The map is the composite of a homotopy equivalence from `classifyingSpace G` to the CW
approximation of `X` with the approximating map. Unlike
`TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace`, no hypothesis of CW type is made on
`X`, and a weak homotopy equivalence is the most one can ask for: the Warsaw circle is aspherical
with trivial fundamental group, and it is not homotopy equivalent to a point. -/
theorem IsAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace {G : Type u} [Group G]
    {X : Type u} [TopologicalSpace X] {x : X} (hX : IsAspherical X x)
    (eX : FundamentalGroup X x ≃* G) :
    ∃ (f : C(classifyingSpace G, X)) (γ : Path (f (classifyingSpaceBasepoint G)) x),
      f.IsWeakHomotopyEquivalence ∧
        ∀ a, eX (fundamentalGroupMulEquivOfPath γ (map f _ a)) =
          classifyingSpaceFundamentalGroupMulEquiv G a :=
  have : PathConnectedSpace X := hX.pathConnectedSpace
  exists_isWeakHomotopyEquivalence_classifyingSpace_of_cwType
    (isWeakHomotopyEquivalence_cwApproximationMap (TopCat.of X) x)
    (cwApproximationMap_cwApproximationBasepoint (TopCat.of X) x) hX eX

/-- **Every `K(G, 1)` space receives a weak homotopy equivalence from the classifying space.**
See `TauCeti.IsAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace` for a weak homotopy
equivalence realizing a prescribed identification of the fundamental group with `G`. -/
theorem IsEilenbergMacLaneSpaceOne.exists_isWeakHomotopyEquivalence_classifyingSpace
    {G : Type u} [Group G] {X : Type u} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpaceOne G X x) :
    ∃ f : C(classifyingSpace G, X), f.IsWeakHomotopyEquivalence := by
  obtain ⟨eX⟩ := hX.nonempty_fundamentalGroupMulEquiv
  obtain ⟨f, -, hf, -⟩ := hX.isAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace eX
  exact ⟨f, hf⟩

/-- **Based homotopy equivalence of aspherical CW complexes (Hatcher, Theorem 1B.8 and
Proposition 1B.9).** For Hausdorff CW complexes `X` and `Y` (in arbitrary universes) that are
aspherical at `x` and `y`, every isomorphism `φ : π₁(X, x) ≃* π₁(Y, y)` is induced by a homotopy
equivalence `F : X ≃ₕ Y` sending `x` to `y` whose homotopy inverse sends `y` to `x`, with both
compositions homotopic to the identity *relative to the base points* and `F.invFun` inducing
`φ.symm`. -/
theorem IsAspherical.exists_basedHomotopyEquiv {X : Type u} {Y : Type v}
    [TopologicalSpace X] [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y] [Topology.CWComplex (Set.univ : Set Y)]
    {x : X} {y : Y} (hX : IsAspherical X x) (hY : IsAspherical Y y)
    (φ : FundamentalGroup X x ≃* FundamentalGroup Y y) :
    ∃ (F : X ≃ₕ Y) (hF : F.toFun x = y) (hFinv : F.invFun y = x),
      (F.invFun.comp F.toFun).HomotopicRel (.id X) {x} ∧
      (F.toFun.comp F.invFun).HomotopicRel (.id Y) {y} ∧
      mapOfEq F.toFun hF = φ.toMonoidHom ∧
      mapOfEq F.invFun hFinv = φ.symm.toMonoidHom := by
  have : PathConnectedSpace X := hX.pathConnectedSpace
  have : PathConnectedSpace Y := hY.pathConnectedSpace
  obtain ⟨f, hf, hfφ⟩ := exists_mapOfEq_of_cwComplex hY.subsingleton_homotopyGroup φ.toMonoidHom
  obtain ⟨g, hg, hgφ⟩ :=
    exists_mapOfEq_of_cwComplex hX.subsingleton_homotopyGroup φ.symm.toMonoidHom
  have hgf₀ : (g.comp f) x = x := (congrArg g hf).trans hg
  have hfg₀ : (f.comp g) y = y := (congrArg f hg).trans hf
  have hgf_rel : (g.comp f).HomotopicRel (.id X) {x} :=
    homotopicRel_of_mapOfEq_eq_of_cwComplex hX.subsingleton_homotopyGroup hgf₀
      (rfl : ContinuousMap.id X x = x) <| MonoidHom.ext fun a ↦ by
        rw [← mapOfEq_comp g f hf hg, hgφ, hfφ]
        exact (φ.symm_apply_apply a).trans (mapOfEq_id _ a).symm
  have hfg_rel : (f.comp g).HomotopicRel (.id Y) {y} :=
    homotopicRel_of_mapOfEq_eq_of_cwComplex hY.subsingleton_homotopyGroup hfg₀
      (rfl : ContinuousMap.id Y y = y) <| MonoidHom.ext fun b ↦ by
        rw [← mapOfEq_comp f g hg hf, hfφ, hgφ]
        exact (φ.apply_symm_apply b).trans (mapOfEq_id _ b).symm
  exact ⟨⟨f, g, hgf_rel.homotopic, hfg_rel.homotopic⟩, hf, hg, hgf_rel, hfg_rel, hfφ, hgφ⟩

/-- **Homotopy equivalence of aspherical CW complexes realizing a prescribed `π₁`-isomorphism
(Hatcher, Theorem 1B.8).** Two aspherical Hausdorff CW complexes with isomorphic fundamental groups
are homotopy equivalent by a homotopy equivalence whose forward map is basepoint-preserving and
induces any prescribed isomorphism `φ` on fundamental groups; see
`TauCeti.IsAspherical.exists_basedHomotopyEquiv` for the pointed homotopy inverse and
basepoint-relative homotopies, and `TauCeti.homotopicRel_of_mapOfEq_eq_of_cwComplex` for uniqueness
of the forward map up to pointed homotopy. -/
theorem exists_homotopyEquiv_of_isAspherical {X : Type u} {Y : Type v}
    [TopologicalSpace X] [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [TopologicalSpace Y] [T2Space Y] [Topology.CWComplex (Set.univ : Set Y)]
    {x : X} {y : Y} (hX : IsAspherical X x) (hY : IsAspherical Y y)
    (φ : FundamentalGroup X x ≃* FundamentalGroup Y y) :
    ∃ (F : X ≃ₕ Y) (hF : F.toFun x = y), mapOfEq F.toFun hF = φ.toMonoidHom := by
  obtain ⟨F, hF, -, -, -, hFφ, -⟩ := hX.exists_basedHomotopyEquiv hY φ
  exact ⟨F, hF, hFφ⟩

/-- **Based homotopy equivalence of an aspherical CW complex with Milnor's classifying space.** An
aspherical Hausdorff CW complex `X` whose fundamental group at `x` is identified with `G` (in any
universe) by `eX` is homotopy equivalent to `classifyingSpace G` via a based homotopy equivalence
whose forward map sends `x` to `classifyingSpaceBasepoint G` and realizes `eX`, with both
compositions homotopic to the identity relative to the base points. -/
theorem IsAspherical.exists_basedHomotopyEquiv_classifyingSpace {G : Type v} [Group G]
    {X : Type u} [TopologicalSpace X] [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    {x : X} (hX : IsAspherical X x) (eX : FundamentalGroup X x ≃* G) :
    ∃ (e : X ≃ₕ classifyingSpace G) (he : e.toFun x = classifyingSpaceBasepoint G),
      e.invFun (classifyingSpaceBasepoint G) = x ∧
      (e.invFun.comp e.toFun).HomotopicRel (.id X) {x} ∧
      (e.toFun.comp e.invFun).HomotopicRel (.id (classifyingSpace G))
        {classifyingSpaceBasepoint G} ∧
      ∀ a, classifyingSpaceFundamentalGroupMulEquiv G (mapOfEq e.toFun he a) = eX a := by
  obtain ⟨e, he, he_inv, hleft, hright, heφ, -⟩ := hX.exists_basedHomotopyEquiv
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical
    (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)
  refine ⟨e, he, he_inv, hleft, hright, fun a ↦ ?_⟩
  rw [heφ, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

end TauCeti
