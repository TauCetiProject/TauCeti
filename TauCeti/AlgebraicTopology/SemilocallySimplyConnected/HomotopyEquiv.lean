/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On

/-!
# Semilocal simple connectivity is a homotopy invariant

If `X` and `Y` are homotopy equivalent, then `X` is semilocally simply connected if and only if
`Y` is. The forward map `f` of a homotopy equivalence `X ≃ₕ Y` induces an injective map
`π₁(X, x) → π₁(Y, f x)` at every point
(`ContinuousMap.HomotopyEquiv.fundamentalGroup_map_bijective`), so the preimage under `f` of a
neighbourhood of `f x` whose loops are null-homotopic in `Y` is a neighbourhood of `x` whose loops
are null-homotopic in `X` (`TauCeti.SemilocallySimplyConnectedSpace.of_map_injective`).

This lets the standing hypotheses of covering-space theory be transported along homotopy
equivalences, for instance from one model of a classifying space to another. Unlike semilocal
simple connectivity, local path-connectedness is not a homotopy invariant: the comb space is
contractible but not locally path-connected.

## Main results

* `ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace`: a space homotopy equivalent to
  a semilocally simply connected space is semilocally simply connected.
* `ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace_iff`: the iff form.
-/

public section

namespace TauCeti

open scoped ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A space homotopy equivalent to a semilocally simply connected space is semilocally simply
connected.** -/
theorem _root_.ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace
    [SemilocallySimplyConnectedSpace Y] (e : X ≃ₕ Y) : SemilocallySimplyConnectedSpace X :=
  .of_map_injective e.toFun fun x ↦ (e.fundamentalGroup_map_bijective x).injective

/-- **Semilocal simple connectivity is a homotopy invariant.** -/
theorem _root_.ContinuousMap.HomotopyEquiv.semilocallySimplyConnectedSpace_iff (e : X ≃ₕ Y) :
    SemilocallySimplyConnectedSpace X ↔ SemilocallySimplyConnectedSpace Y :=
  ⟨fun _ ↦ e.symm.semilocallySimplyConnectedSpace, fun _ ↦ e.semilocallySimplyConnectedSpace⟩

end TauCeti
