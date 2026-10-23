/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
public import TauCeti.Geometry.Manifold.VirtuallyHaken

/-!
# The virtual Haken conjecture

Waldhausen asked whether every closed irreducible 3-manifold with infinite fundamental group has a
finite cover that is Haken. For closed hyperbolic 3-manifolds this was proved by Agol, building on
work of Kahn–Markovic and Wise; the same work answers the virtual fibering question (Kirby's
problem 3.51), stated in `TauCeti.VirtualFiberingConjecture`. This file states the virtual Haken
conjecture for closed hyperbolic 3-manifolds: every compact connected smooth 3-manifold without
boundary that admits a hyperbolic metric (`TauCeti.IsHyperbolic`) is virtually Haken
(`TauCeti.IsVirtuallyHaken`).

A closed 3-manifold is modelled, as in `TauCeti.VirtualFiberingConjecture`, on
`EuclideanSpace ℝ (Fin 3)` with the boundaryless model `𝓡 3`, and is compact and connected. The
`[MetricSpace M]` hypothesis supplies the ambient metric structure required by this statement, while
a `HyperbolicMetric` witness carries its own Riemannian metric for the completeness field.

The conclusion asks for a finite cover that is a possibly nonorientable closed Haken 3-manifold,
matching `TauCeti.IsPossiblyNonorientableClosedHakenThreeManifold`. Agol's theorem provides an
orientable such cover; the statement here does not record orientability.

The conjecture is stated, not proved.

## Main definitions

* `TauCeti.VirtualHakenConjecture`: every closed hyperbolic 3-manifold is virtually Haken.

## Main results

* `TauCeti.VirtualHakenConjecture.isVirtuallyHaken`: applying the conjecture to a closed
  hyperbolic 3-manifold.
* `TauCeti.virtualHakenConjecture_iff`: the defining characterization.

## References

* F. Waldhausen, *On irreducible 3-manifolds which are sufficiently large*, Ann. of Math. 87
  (1968), 56–88.
* I. Agol, *The virtual Haken conjecture* (with an appendix by I. Agol, D. Groves and J. Manning),
  Doc. Math. 18 (2013), 1045–1087.
* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 3.51, in *Geometric Topology*,
  AMS/IP Stud. Adv. Math. 2.2 (1997).
-/

public section

open scoped Manifold ContDiff

universe u

namespace TauCeti

/-- The **virtual Haken conjecture** for hyperbolic 3-manifolds (Waldhausen's question; a theorem
of Agol): every closed hyperbolic 3-manifold `M`, that is a compact connected smooth 3-manifold
without boundary admitting a complete Riemannian metric of constant curvature `-1`, has a
finite-sheeted covering space that is a closed Haken 3-manifold. -/
def VirtualHakenConjecture : Prop :=
  ∀ (M : Type u) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M],
    IsHyperbolic (I := 𝓡 3) (M := M) → IsVirtuallyHaken M

/-- A proof of the virtual Haken conjecture makes every closed hyperbolic 3-manifold virtually
Haken. -/
theorem VirtualHakenConjecture.isVirtuallyHaken (h : VirtualHakenConjecture.{u})
    (M : Type u) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
    (hM : IsHyperbolic (I := 𝓡 3) (M := M)) : IsVirtuallyHaken M :=
  h M hM

/-- The defining characterization of the virtual Haken conjecture. -/
theorem virtualHakenConjecture_iff :
    VirtualHakenConjecture.{u} ↔
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [ConnectedSpace M],
        IsHyperbolic (I := 𝓡 3) (M := M) → IsVirtuallyHaken M :=
  Iff.rfl

end TauCeti
