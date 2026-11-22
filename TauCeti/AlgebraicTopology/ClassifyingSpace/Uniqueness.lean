/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
public import TauCeti.AlgebraicTopology.EilenbergMacLane.PointedMaps
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Uniqueness
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic

/-!
# Uniqueness of Milnor's classifying space

Every `K(G, 1)` space of CW type is homotopy equivalent to Milnor's classifying space
`TauCeti.classifyingSpace G`, compatibly with the identifications of both fundamental groups with
`G` (`TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace`), by specializing the generic
uniqueness theorem `TauCeti.IsAspherical.exists_homotopyEquiv` from
`TauCeti.AlgebraicTopology.EilenbergMacLane.Uniqueness`. So the classifying space is well defined
up to homotopy equivalence among spaces of CW type.

When a space is well-pointed (its base point has the homotopy extension property), the generic
pointed uniqueness isomorphism `TauCeti.IsAspherical.pointedHomotopyCatIso` from
`TauCeti.AlgebraicTopology.EilenbergMacLane.PointedMaps` specializes to a canonical isomorphism
`TauCeti.IsAspherical.pointedHomotopyCatIsoClassifyingSpace` in `TauCeti.PointedHomotopyCat`
with Milnor's classifying space `classifyingSpace G`. Well-pointedness cannot be dropped: the comb
space based at a non-locally-contractible point is contractible without being pointed homotopy
equivalent to a point.

The hypothesis of CW type on the space cannot be dropped: a point and the Warsaw circle are both
path connected with trivial homotopy groups, but they are not homotopy equivalent.

Without it, the classifying space still maps to every aspherical space by a weak homotopy
equivalence realizing a prescribed identification of the fundamental group with `G`
(`TauCeti.IsAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace`), which is the case
`n = 1` of Hatcher's Proposition 4.30. The map factors through the CW approximation of the
target, which is an aspherical space of CW type and hence homotopy equivalent to
`classifyingSpace G`. So `classifyingSpace G` computes every weak homotopy invariant, for instance
the singular homology, of an arbitrary `K(G, 1)` space, such as the loop space of a `K(G, 2)` space
for abelian `G`, which need not have CW type.

## Main definitions

* `TauCeti.IsAspherical.pointedHomotopyCatIsoClassifyingSpace`: **the unique isomorphism in
  `PointedHomotopyCat` from a well-pointed aspherical space of CW type to `classifyingSpace G`
  realizing a given identification on `π₁`.**

## Main results

* `TauCeti.IsAspherical.exists_homotopyEquiv_classifyingSpace`: an aspherical space of CW type
  with fundamental group identified with `G` is homotopy equivalent to `classifyingSpace G`,
  compatibly with the identifications of fundamental groups.
* `TauCeti.IsAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace`: every aspherical space
  receives a weak homotopy equivalence from `classifyingSpace G` realizing a given identification of
  `π₁`.
* `TauCeti.IsEilenbergMacLaneSpaceOne.exists_isWeakHomotopyEquivalence_classifyingSpace`: every
  `K(G, 1)` space receives a weak homotopy equivalence from `classifyingSpace G`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (Proposition 0.19),
  Section 1.B, Theorem 1B.8 and Proposition 1B.9, and Section 4.1, Theorem 4.5 and Proposition 4.22.
* R. Schwamberger and R. M. Vogt, *Dold spaces in homotopy theory*, Algebr. Geom. Topol. 9
  (2009), 1585--1622, for the Warsaw circle.
-/

public section

noncomputable section

open scoped Topology Topology.Homotopy ContinuousMap

open FundamentalGroup

universe u v

namespace TauCeti

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

/-- **Every well-pointed `K(G, 1)` of CW type is canonically isomorphic in `PointedHomotopyCat` to
Milnor's classifying space `classifyingSpace G`.** -/
def IsAspherical.pointedHomotopyCatIsoClassifyingSpace {G : Type u} [Group G]
    {X : BasedTopologicalSpace.{u}} [CWType X.carrier] (hX : IsAspherical X.carrier X.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (eX : FundamentalGroup X.carrier X.basepoint ≃* G) :
    PointedHomotopyCat.quotient.obj X ≅
      PointedHomotopyCat.quotient.obj ⟨classifyingSpace G, classifyingSpaceBasepoint G⟩ :=
  hX.pointedHomotopyCatIso (Y := ⟨classifyingSpace G, classifyingSpaceBasepoint G⟩)
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical hX_hep
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G)
    (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)

/-- The forward morphism of `IsAspherical.pointedHomotopyCatIsoClassifyingSpace` realizes `eX`
under the identification of `π₁(classifyingSpace G)` with `G`. -/
@[simp]
theorem IsAspherical.fundamentalGroupFunctor_map_pointedHomotopyCatIsoClassifyingSpace_hom
    {G : Type u} [Group G] {X : BasedTopologicalSpace.{u}} [CWType X.carrier]
    (hX : IsAspherical X.carrier X.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (eX : FundamentalGroup X.carrier X.basepoint ≃* G) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (hX.pointedHomotopyCatIsoClassifyingSpace hX_hep eX).hom =
      GrpCat.ofHom (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm).toMonoidHom :=
  hX.fundamentalGroupFunctor_map_pointedHomotopyCatIso_hom
    (Y := ⟨classifyingSpace G, classifyingSpaceBasepoint G⟩)
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical hX_hep
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G)
    (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)

/-- The inverse morphism of `IsAspherical.pointedHomotopyCatIsoClassifyingSpace` realizes `eX⁻¹`
under the identification of `π₁(classifyingSpace G)` with `G`. -/
@[simp]
theorem IsAspherical.fundamentalGroupFunctor_map_pointedHomotopyCatIsoClassifyingSpace_inv
    {G : Type u} [Group G] {X : BasedTopologicalSpace.{u}} [CWType X.carrier]
    (hX : IsAspherical X.carrier X.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (eX : FundamentalGroup X.carrier X.basepoint ≃* G) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (hX.pointedHomotopyCatIsoClassifyingSpace hX_hep eX).inv =
      GrpCat.ofHom ((classifyingSpaceFundamentalGroupMulEquiv G).trans eX.symm).toMonoidHom :=
  hX.fundamentalGroupFunctor_map_pointedHomotopyCatIso_inv
    (Y := ⟨classifyingSpace G, classifyingSpaceBasepoint G⟩)
    (isEilenbergMacLaneSpaceOne_classifyingSpace G).isAspherical hX_hep
    (hasHomotopyExtensionProperty_classifyingSpaceBasepoint G)
    (eX.trans (classifyingSpaceFundamentalGroupMulEquiv G).symm)

end TauCeti
