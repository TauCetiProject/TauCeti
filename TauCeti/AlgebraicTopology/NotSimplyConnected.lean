/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible

/-!
# Consequences of a space not being simply connected

A space whose fundamental group at some basepoint is nontrivial is not simply connected, and a
non-simply-connected space inherits the standard topological obstructions: it is not
contractible, and it is not homotopy equivalent (in particular, not homeomorphic) to any simply
connected space — for instance to any real topological vector space, such as `ℝ`.

These facts use the space only through the (non-)triviality of its fundamental group, so they are
stated once here for an arbitrary space and then specialised to concrete spaces such as circles
and real projective spaces. Non-simple-connectivity follows because a simply connected space
has a subsingleton fundamental group; the homotopy-equivalence statements consume Mathlib's
transfer of `SimplyConnectedSpace` along a homotopy equivalence
(`ContinuousMap.HomotopyEquiv.simplyConnectedSpace`) and the contractibility of a real
topological vector space (`RealTopologicalVectorSpace.contractibleSpace`). A homeomorphism `e`
is turned into a homotopy equivalence by `e.toHomotopyEquiv`.

## Main declarations

* `TauCeti.not_simplyConnectedSpace_of_nontrivial_fundamentalGroup`: a space with a nontrivial
  fundamental group at some basepoint is not simply connected.
* `TauCeti.not_contractibleSpace_of_not_simplyConnectedSpace`: a non-simply-connected space is
  not contractible.
* `TauCeti.isEmpty_homotopyEquiv_of_not_simplyConnectedSpace`,
  `TauCeti.isEmpty_homotopyEquiv_real_of_not_simplyConnectedSpace`: a non-simply-connected space
  is not homotopy equivalent to a simply connected space, or to `ℝ`.
-/

public section

open scoped ContinuousMap

namespace TauCeti

/-- A space with a nontrivial fundamental group at some basepoint is **not simply connected**: a
simply connected space has a subsingleton fundamental group. -/
theorem not_simplyConnectedSpace_of_nontrivial_fundamentalGroup {X : Type*} [TopologicalSpace X]
    (x : X) [Nontrivial (FundamentalGroup X x)] : ¬ SimplyConnectedSpace X :=
  fun _ => false_of_nontrivial_of_subsingleton (FundamentalGroup X x)

/-- A **not simply connected** space is **not contractible**: a contractible space is simply
connected. -/
theorem not_contractibleSpace_of_not_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    (h : ¬ SimplyConnectedSpace X) : ¬ ContractibleSpace X :=
  fun _ => h inferInstance

/-- A **not simply connected** space is not homotopy equivalent (in particular, not
homeomorphic) to any simply connected space, since simple connectivity transfers along homotopy
equivalences. -/
theorem isEmpty_homotopyEquiv_of_not_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    (h : ¬ SimplyConnectedSpace X) (Y : Type*) [TopologicalSpace Y] [SimplyConnectedSpace Y] :
    IsEmpty (X ≃ₕ Y) :=
  ⟨fun e => h e.simplyConnectedSpace⟩

/-- A **not simply connected** space is not homotopy equivalent (in particular, not
homeomorphic) to the real line: `ℝ` is contractible, hence simply connected. -/
theorem isEmpty_homotopyEquiv_real_of_not_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    (h : ¬ SimplyConnectedSpace X) : IsEmpty (X ≃ₕ ℝ) :=
  isEmpty_homotopyEquiv_of_not_simplyConnectedSpace h ℝ

end TauCeti
