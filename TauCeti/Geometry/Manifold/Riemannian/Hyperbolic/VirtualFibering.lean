/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Topology.VirtuallyFibered

/-!
# The virtual fibering conjecture

Thurston asked whether every hyperbolic 3-manifold has a finite cover that is a surface bundle
over the circle (Kirby's problem 3.51). For closed manifolds this was proved by Agol. This file
states it: every compact connected smooth 3-manifold without boundary that admits a hyperbolic
metric (`TauCeti.IsHyperbolic`) is virtually fibered (`TauCeti.IsVirtuallyFibered`).

A closed 3-manifold is modelled here on `EuclideanSpace ℝ (Fin 3)` with the boundaryless model
`𝓡 3`, and is compact and connected. Its topology is that of a metric space, as
`TauCeti.HyperbolicMetric` requires its metric to induce the given distance. The hypothesis
`[ConnectedSpace M]` is stated explicitly for readability; it is in fact implied by
`TauCeti.IsHyperbolic`, since the Riemannian distance between points joined by no `C^1` path is
infinite while the metric-space distance is finite. Orientability is not assumed; Agol's theorem
covers non-orientable manifolds by passing to the orientation double cover.

The conclusion asks for a finite cover homeomorphic to a mapping torus, the topological form of a
fibration over the circle recorded by `TauCeti.FibersOverCircle`. A surface bundle over the circle
is the mapping torus of its monodromy, so Agol's theorem gives this conclusion.

The conjecture is stated, not proved.

## Main definitions

* `TauCeti.VirtualFiberingConjecture`: every closed hyperbolic 3-manifold is virtually fibered.

## Main results

* `TauCeti.VirtualFiberingConjecture.isVirtuallyFibered`: applying the conjecture to a closed
  hyperbolic 3-manifold.
* `TauCeti.virtualFiberingConjecture_iff`: the defining characterization.

## References

* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 3.51, in *Geometric Topology*,
  AMS/IP Stud. Adv. Math. 2.2 (1997).
* I. Agol, *The virtual Haken conjecture* (with an appendix by I. Agol, D. Groves and J. Manning),
  Doc. Math. 18 (2013), 1045–1087.
* I. Agol, *Criteria for virtual fibering*, J. Topol. 1 (2008), 269–284.
-/

public section

open scoped Manifold ContDiff

universe u

namespace TauCeti

/-- The **virtual fibering conjecture** (Thurston's question, Kirby's problem 3.51; a theorem of
Agol): every closed hyperbolic 3-manifold `M`, that is a compact connected smooth 3-manifold
without boundary admitting a complete Riemannian metric of constant curvature `-1`, has a connected
finite-sheeted covering space that fibers over the circle. -/
def VirtualFiberingConjecture : Prop :=
  ∀ (M : Type u) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M],
    IsHyperbolic (I := 𝓡 3) (M := M) → IsVirtuallyFibered M

/-- A proof of the virtual fibering conjecture makes every closed hyperbolic 3-manifold virtually
fibered. -/
theorem VirtualFiberingConjecture.isVirtuallyFibered (h : VirtualFiberingConjecture.{u})
    (M : Type u) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
    (hM : IsHyperbolic (I := 𝓡 3) (M := M)) : IsVirtuallyFibered M :=
  h M hM

/-- The defining characterization of the virtual fibering conjecture. -/
theorem virtualFiberingConjecture_iff :
    VirtualFiberingConjecture.{u} ↔
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M],
        IsHyperbolic (I := 𝓡 3) (M := M) → IsVirtuallyFibered M :=
  Iff.rfl

end TauCeti
