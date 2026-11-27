/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Topology.Circle.BasedMapLift
public import TauCeti.Topology.MappingSpace.Sphere.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The higher iterated loop spaces of the circle are contractible

For `k ≥ 2` the `k`-fold iterated loop space `Ω^[k] S¹` of the circle, based at `1`, is
contractible. It is homeomorphic to the based mapping space `Map_*(S^k, S¹)`
(`TauCeti.BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace`), and for `k ≥ 2` the
sphere `S^k` is compact, simply connected and locally path-connected, so every based map
`S^k → S¹` has a based angle function depending continuously on the map and
`Map_*(S^k, S¹)` is contractible (`Circle.contractibleSpace_basedMap`). In particular all homotopy
groups `π_j(Ω²S¹) ≅ π_{j+2}(S¹)` vanish, and `Ω²S¹` is path-connected.

## Main declarations

* `Circle.contractibleSpace_iteratedLoopSpace`: `Ω^[n + 2] S¹` is contractible.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 1.33 and §4.1.
-/

public section

open Metric TauCeti

namespace Circle

/-- **The higher iterated loop spaces of the circle are contractible**: for every `n`, the
`(n + 2)`-fold loop space `Ω^[n + 2] S¹` of the circle based at `1` is contractible. In
particular `Ω²S¹` is contractible, so `π_j(Ω²S¹) ≅ π_{j+2}(S¹)` vanishes for every `j ≥ 0`. -/
instance contractibleSpace_iteratedLoopSpace (n : ℕ) :
    ContractibleSpace (BasedTopologicalSpace.iteratedLoopSpace ⟨Circle, 1⟩ (n + 2)).carrier :=
  -- the sphere is a manifold, hence locally path-connected
  have : LocallyPathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 2 + 1))) 1) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (n + 2))) _
  (BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace (n + 2) ⟨Circle, 1⟩
    ⟨EuclideanSpace.single 0 1, by simp⟩).symm.contractibleSpace

end Circle
