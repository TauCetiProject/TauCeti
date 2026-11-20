/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.FixedPoints.Involution

/-!
# Geometric connectedness of swap fixed-point subgroup schemes

Over a field `k`, the fixed-point closed subgroup scheme of `CommHopfAlgCat.swapAction H` on
`H ⊗[k] H` is isomorphic to `H` and hence geometrically connected whenever `H` is.

## Main declarations

* `TauCeti.CommHopfAlgCat.geometricallyConnected_fixedPoints_swapAction`: geometric connectedness
  of `fixedPoints (fun θ ↦ (swapAction H θ).asIso.hom)` when `H` is geometrically connected.
-/

public section

open CategoryTheory _root_.CommHopfAlgCat

namespace TauCeti.CommHopfAlgCat

universe u v

/-- Over a field `k`, swap fixed points on `H ⊗[k] H` inherit geometric connectedness from `H`. -/
theorem geometricallyConnected_fixedPoints_swapAction {k : Type u} [Field k]
    {H : _root_.CommHopfAlgCat.{v} k} (hH : geometricallyConnectedCommHopfAlgProperty k H) :
    geometricallyConnectedCommHopfAlgProperty k (fixedPoints fun θ ↦ (swapAction H θ).asIso.hom) :=
  (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso (fixedPointsSwapActionIso H).symm hH

end TauCeti.CommHopfAlgCat
