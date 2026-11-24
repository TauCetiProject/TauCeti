/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.Topology.CWComplex.Classical.CWType
import TauCeti.AlgebraicTopology.ClassifyingSpace.Contractible
import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
import TauCeti.AlgebraicTopology.WarsawCircle.Homotopy

/-!
# Sharpness of CW type in `K(G, 1)` uniqueness via the Warsaw circle

`TauCeti.IsAspherical.exists_homotopyEquiv` and
`TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv` show that two aspherical or `K(G, 1)`
spaces of CW type with isomorphic fundamental groups are homotopy equivalent, while
`TauCeti.IsAspherical.exists_isWeakHomotopyEquivalence_classifyingSpace` constructs a weak homotopy
equivalence `classifyingSpace G → X` into an arbitrary `K(G, 1)` space without assuming CW type on
`X`.

This file records the concrete counterexamples supplied by the Warsaw circle `TauCeti.WarsawCircle`
demonstrating that the `CWType` hypothesis on **both** spaces in
`IsAspherical.exists_homotopyEquiv` and `IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv` cannot
be weakened to `CWType` on just one side (see `TauCeti.AlgebraicTopology.WarsawCircle.Homotopy` for
the corresponding sharpness counterexamples for Whitehead's theorem):

* For any trivial group `G`, both `classifyingSpace G` and `WarsawCircle` are `K(G, 1)` spaces, and
  every continuous map in either direction between `classifyingSpace G` and `WarsawCircle` is a weak
  homotopy equivalence (`ContinuousMap.isWeakHomotopyEquivalence_of_subsingleton_homotopyGroup`).
* Yet `classifyingSpace G` is contractible (`instContractibleSpaceClassifyingSpace`) and of CW type,
  whereas `WarsawCircle` is not contractible (`WarsawCircle.not_contractibleSpace`), so there is no
  homotopy equivalence between `classifyingSpace G` and `WarsawCircle` in either direction
  (`WarsawCircle.isEmpty_homotopyEquiv_contractibleSpace`,
  `WarsawCircle.isEmpty_contractibleSpace_homotopyEquiv`).

## Main results

* `TauCeti.exists_isAspherical_cwType_left_isEmpty_homotopyEquiv` and
  `TauCeti.exists_isAspherical_cwType_right_isEmpty_homotopyEquiv`: `CWType` on only the left or
  only the right space does not suffice in `IsAspherical.exists_homotopyEquiv`.
* `TauCeti.exists_isEilenbergMacLaneSpaceOne_cwType_left_isEmpty_homotopyEquiv` and
  `TauCeti.exists_isEilenbergMacLaneSpaceOne_cwType_right_isEmpty_homotopyEquiv`: `CWType` on only
  one space does not suffice in `IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv`.

## References

* R. Schwamberger and R. M. Vogt, *Dold spaces in homotopy theory*, Algebr. Geom. Topol. **9**
  (2009), 1585--1622.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B and Section 4.1.
-/

public section

open scoped ContinuousMap

universe u

namespace TauCeti

/-- **Sharpness of left-only `CWType` in `IsAspherical.exists_homotopyEquiv`.** There exist based
aspherical spaces `(X, x)` and `(Y, y)` in `Type` with `CWType X` and isomorphic fundamental groups
such that `X ≃ₕ Y` is empty: take `X = classifyingSpace Unit` and `Y = WarsawCircle`. -/
theorem exists_isAspherical_cwType_left_isEmpty_homotopyEquiv :
    ∃ (X Y : Type) (_ : TopologicalSpace X) (_ : TopologicalSpace Y) (x : X) (y : Y),
      CWType X ∧ IsAspherical X x ∧ IsAspherical Y y ∧
        Nonempty (FundamentalGroup X x ≃* FundamentalGroup Y y) ∧ IsEmpty (X ≃ₕ Y) := by
  refine ⟨classifyingSpace Unit, WarsawCircle, inferInstance, inferInstance,
    classifyingSpaceBasepoint Unit, WarsawCircle.basepoint, inferInstance,
    (isEilenbergMacLaneSpaceOne_classifyingSpace Unit).isAspherical,
    WarsawCircle.isAspherical WarsawCircle.basepoint, ?_,
    WarsawCircle.isEmpty_contractibleSpace_homotopyEquiv⟩
  obtain ⟨e⟩ := (isEilenbergMacLaneSpaceOne_classifyingSpace Unit).nonempty_fundamentalGroupMulEquiv
  exact ⟨e.trans (MulEquiv.ofBijective (1 : Unit →* _) (Function.bijective_of_subsingleton' _))⟩

/-- **Sharpness of right-only `CWType` in `IsAspherical.exists_homotopyEquiv`.** There exist based
aspherical spaces `(X, x)` and `(Y, y)` in `Type` with `CWType Y` and isomorphic fundamental groups
such that `X ≃ₕ Y` is empty: take `X = WarsawCircle` and `Y = classifyingSpace Unit`. -/
theorem exists_isAspherical_cwType_right_isEmpty_homotopyEquiv :
    ∃ (X Y : Type) (_ : TopologicalSpace X) (_ : TopologicalSpace Y) (x : X) (y : Y),
      CWType Y ∧ IsAspherical X x ∧ IsAspherical Y y ∧
        Nonempty (FundamentalGroup X x ≃* FundamentalGroup Y y) ∧ IsEmpty (X ≃ₕ Y) := by
  obtain ⟨X, Y, _, _, x, y, hCW, hX, hY, ⟨e⟩, hEmpty⟩ :=
    exists_isAspherical_cwType_left_isEmpty_homotopyEquiv
  exact ⟨Y, X, inferInstance, inferInstance, y, x, hCW, hY, hX, ⟨e.symm⟩,
    ⟨fun h ↦ hEmpty.false h.symm⟩⟩

/-- **Sharpness of left-only `CWType` in `IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv`.** For
any trivial group `G`, there exist `K(G, 1)` spaces `(X, x)` and `(Y, y)` in `Type` with `CWType X`
that are not homotopy equivalent. -/
theorem exists_isEilenbergMacLaneSpaceOne_cwType_left_isEmpty_homotopyEquiv
    (G : Type u) [Group G] [Subsingleton G] :
    ∃ (X Y : Type) (_ : TopologicalSpace X) (_ : TopologicalSpace Y) (x : X) (y : Y),
      CWType X ∧ IsEilenbergMacLaneSpaceOne G X x ∧ IsEilenbergMacLaneSpaceOne G Y y ∧
        IsEmpty (X ≃ₕ Y) := by
  refine ⟨classifyingSpace Unit, WarsawCircle, inferInstance, inferInstance,
    classifyingSpaceBasepoint Unit, WarsawCircle.basepoint, inferInstance, ?_,
    WarsawCircle.isEilenbergMacLaneSpaceOne G WarsawCircle.basepoint,
    WarsawCircle.isEmpty_contractibleSpace_homotopyEquiv⟩
  exact (isEilenbergMacLaneSpaceOne_classifyingSpace Unit).of_mulEquiv
    (MulEquiv.ofBijective (1 : Unit →* G) (Function.bijective_of_subsingleton' _))

/-- **Sharpness of right-only `CWType` in `IsEilenbergMacLaneSpaceOne.nonempty_homotopyEquiv`.** For
any trivial group `G`, there exist `K(G, 1)` spaces `(X, x)` and `(Y, y)` in `Type` with `CWType Y`
that are not homotopy equivalent. -/
theorem exists_isEilenbergMacLaneSpaceOne_cwType_right_isEmpty_homotopyEquiv
    (G : Type u) [Group G] [Subsingleton G] :
    ∃ (X Y : Type) (_ : TopologicalSpace X) (_ : TopologicalSpace Y) (x : X) (y : Y),
      CWType Y ∧ IsEilenbergMacLaneSpaceOne G X x ∧ IsEilenbergMacLaneSpaceOne G Y y ∧
        IsEmpty (X ≃ₕ Y) := by
  obtain ⟨X, Y, _, _, x, y, hCW, hX, hY, hEmpty⟩ :=
    exists_isEilenbergMacLaneSpaceOne_cwType_left_isEmpty_homotopyEquiv G
  exact ⟨Y, X, inferInstance, inferInstance, y, x, hCW, hY, hX, ⟨fun h ↦ hEmpty.false h.symm⟩⟩

end TauCeti
