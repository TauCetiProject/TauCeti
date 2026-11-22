/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap.Loop
public import TauCeti.Topology.MappingSpace.Sphere.Basic

/-!
# Based sphere maps of `n`-connected maps

For `k ≥ 1`, postcomposition with a based map `f : X → Y`, `f x = y`, induces the map
`Map_*(Sᵏ, X) → Map_*(Sᵏ, Y)` of based mapping spaces out of the sphere `Sᵏ ⊆ ℝᵏ⁺¹`
(`TauCeti.BasedMap.mapContinuousMap`). If `f` is `(n + k)`-connected, this map is `n`-connected
(`ContinuousMap.IsNConnected.basedMapMap`).

The based mapping space `Map_*(Sᵏ, X)` is the `k`-fold iterated loop space `Ω^[k] X`, naturally in
`X` (`TauCeti.BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace_map`), and each
loop space lowers connectivity by one (`ContinuousMap.IsNConnected.iteratedLoopSpace`).

For `k = 2` this compares the double loop spaces `Map_*(S², X) = Ω²X` of the fibre and of the total
space of a fibration over a highly connected base: there the fibre inclusion is highly connected,
so its based sphere maps induce isomorphisms on homology in a range.

## Main results

* `ContinuousMap.IsNConnected.basedMapMap`: the map `Map_*(Sᵏ, X) → Map_*(Sᵏ, Y)` induced by an
  `(n + k)`-connected map is `n`-connected.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I and III.
-/

public section

open Metric TauCeti TauCeti.BasedTopologicalSpace

universe u

namespace ContinuousMap.IsNConnected

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y} {f : C(X, Y)}
  {n k : ℕ}

/-- **Based sphere maps of an `(n + k)`-connected map are `n`-connected.** For `k ≥ 1` and a based
map `f : X → Y`, `f x = y`, that is `(n + k)`-connected, postcomposition with `f` is an
`n`-connected map `Map_*(Sᵏ, X) → Map_*(Sᵏ, Y)` of based mapping spaces out of the sphere. -/
theorem basedMapMap [NeZero k] (hf : f.IsNConnected (n + k)) (hx : f x = y)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    (BasedMap.mapContinuousMap (B := sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) (b₀ := s₀) f
      hx).IsNConnected n := by
  -- Read through `Map_*(Sᵏ, -) ≃ₜ Ω^[k] -`, which is natural, the map is `Ω^[k] f`.
  let g : Hom ⟨X, x⟩ ⟨Y, y⟩ := ⟨f, hx⟩
  let eX := basedMapSphereHomeomorphIteratedLoopSpace k ⟨X, x⟩ s₀
  let eY := basedMapSphereHomeomorphIteratedLoopSpace k ⟨Y, y⟩ s₀
  refine (eX.toHomotopyEquiv.isWeakHomotopyEquivalence.isNConnected_iff_of_comp_eq
    eY.toHomotopyEquiv.isWeakHomotopyEquivalence
    (i := BasedMap.mapContinuousMap f hx)
    (j := (g.iteratedLoopSpace k).toContinuousMap)
    (ContinuousMap.ext fun φ ↦ by
      simpa using basedMapSphereHomeomorphIteratedLoopSpace_map k g s₀ φ)).1 ?_
  exact iteratedLoopSpace (f := g) hf

end ContinuousMap.IsNConnected
