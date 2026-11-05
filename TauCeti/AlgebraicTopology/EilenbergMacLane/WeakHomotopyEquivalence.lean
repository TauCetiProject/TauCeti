/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Degree
public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# Weak homotopy equivalences between aspherical and Eilenberg--Mac Lane spaces

An aspherical space is path-connected and its homotopy groups vanish in every dimension except
one, so the only homotopy invariant a map between aspherical spaces can fail to preserve is the
fundamental group. Accordingly, a map between aspherical spaces is a weak homotopy equivalence
exactly when it induces an isomorphism of fundamental groups at one base point
(`TauCeti.IsAspherical.isWeakHomotopyEquivalence_iff`).

Combined with Whitehead's theorem `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv`, this is
the last step in the uniqueness of `K(G, 1)` spaces: a map between two `K(G, 1)` spaces of CW type
that induces an isomorphism of fundamental groups is a homotopy equivalence. The hypothesis on
both spaces cannot be dropped, because the Warsaw circle and a point are both aspherical with
trivial fundamental group, but they are not homotopy equivalent.

In the same way, a map between Eilenberg--Mac Lane spaces in the same degree `n` is a weak
homotopy equivalence exactly when it induces a bijection on `πₙ` at one base point
(`TauCeti.IsEilenbergMacLaneSpace.isWeakHomotopyEquivalence_iff`), so by Whitehead's theorem such
a map between two `K(G, n)` spaces of CW type is a homotopy equivalence.

## Main results

* `TauCeti.IsAspherical.isWeakHomotopyEquivalence_iff`: a map between aspherical spaces is a weak
  homotopy equivalence exactly when it induces a bijection of fundamental groups.
* `TauCeti.IsEilenbergMacLaneSpace.isWeakHomotopyEquivalence_iff`: a map between `K(G, n)` and
  `K(H, n)` spaces is a weak homotopy equivalence exactly when it is bijective on `πₙ`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B, Theorem 1B.8,
  Section 4.1, Theorem 4.5, and Section 4.2, Proposition 4.30.
-/

public section

namespace TauCeti

open scoped Topology Topology.Homotopy

namespace IsAspherical

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y} {f : C(X, Y)}

/-- **A map between aspherical spaces is a weak homotopy equivalence exactly when it induces an
isomorphism of fundamental groups.** Bijectivity at the single base point `x` suffices. -/
theorem isWeakHomotopyEquivalence_iff (hX : IsAspherical X x) (hY : IsAspherical Y y)
    (hxy : f x = y) :
    f.IsWeakHomotopyEquivalence ↔ Function.Bijective (FundamentalGroup.mapOfEq f hxy) := by
  refine ⟨fun hf ↦ hf.mapOfEq_bijective hxy, fun h ↦ ?_⟩
  subst hxy
  have := hX.pathConnectedSpace
  have := hY.pathConnectedSpace
  refine (ContinuousMap.isWeakHomotopyEquivalence_iff_forall_bijective x).2 fun n ↦ ?_
  match n with
  | 0 =>
    -- Both `π_0` are the sets of path components, which are singletons.
    have : Subsingleton (π_ 0 X x) := HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
    have : Subsingleton (π_ 0 Y (f x)) := HomotopyGroup.pi0EquivZerothHomotopy.subsingleton
    exact Function.bijective_of_subsingleton' _
  | 1 => exact (HomotopyGroup.bijective_map_iff_bijective_mapOfEq f rfl).2 h
  | n + 2 =>
    have := hX.subsingleton_homotopyGroup n
    have := hY.subsingleton_homotopyGroup n
    exact Function.bijective_of_subsingleton' _

end IsAspherical

namespace IsEilenbergMacLaneSpace

variable {G H : Type*} [Group G] [Group H] {n : ℕ} [NeZero n]
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- **A map between Eilenberg--Mac Lane spaces in the same degree is a weak homotopy equivalence
exactly when it induces a bijection on `πₙ`.** Bijectivity at the single base point `x`
suffices, and the groups `G` and `H` play no role. -/
theorem isWeakHomotopyEquivalence_iff (hX : IsEilenbergMacLaneSpace G n X x)
    (hY : IsEilenbergMacLaneSpace H n Y y) {f : C(X, Y)} (hxy : f x = y) :
    f.IsWeakHomotopyEquivalence ↔ Function.Bijective (HomotopyGroup.map (N := Fin n) f hxy) := by
  subst hxy
  have := hX.pathConnectedSpace
  refine ⟨fun hf ↦ hf.bijective n x, fun hf ↦ ?_⟩
  refine (ContinuousMap.isWeakHomotopyEquivalence_iff_forall_bijective x).2 fun k ↦ ?_
  rcases eq_or_ne k n with rfl | hk
  · exact hf
  · -- Outside dimension `n` both homotopy groups are trivial.
    have := hX.subsingleton_homotopyGroup hk
    have := hY.subsingleton_homotopyGroup hk
    exact Function.bijective_of_subsingleton' _

end IsEilenbergMacLaneSpace

end TauCeti
