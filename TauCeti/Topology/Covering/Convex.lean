/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Lifting maps out of convex sets through covering maps

A nonempty convex subset of a real locally convex space is contractible
(`Convex.contractibleSpace`), hence simply connected, and it is locally path-connected
(`Convex.locallyPathConnectedSpace`). By the lifting criterion
(`IsCoveringMap.existsUnique_continuousMap_lifts`), every continuous map out of such a set lifts
uniquely through a covering map once the lift of one point is prescribed
(`IsCoveringMap.existsUnique_continuousMap_lifts_of_convex`). This applies, for instance, to the
closed unit balls carrying the characteristic maps of CW complexes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.3, Proposition 1.33 (the lifting criterion) and Proposition 1.34 (unique lifting).
-/

public section

variable {E X V : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [LocallyConvexSpace ℝ V] {s : Set V}

/-- A continuous map out of a convex subset of a real locally convex space lifts uniquely through
a covering map once the lift of one point is prescribed: the set is contractible and locally
path-connected. -/
theorem IsCoveringMap.existsUnique_continuousMap_lifts_of_convex (hp : IsCoveringMap p)
    (hs : Convex ℝ s) (f : C(s, X)) (x : s) (e : E) (he : p e = f x) :
    ∃! F : C(s, E), F x = e ∧ p ∘ F = f :=
  have := hs.contractibleSpace ⟨x, x.2⟩
  have := hs.locallyPathConnectedSpace
  hp.existsUnique_continuousMap_lifts f x e he
