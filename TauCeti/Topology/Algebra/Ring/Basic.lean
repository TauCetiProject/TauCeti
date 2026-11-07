/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Pulling back topological (semi)ring structures along inducing homomorphisms

Mathlib provides `Topology.IsInducing.continuousAdd`, `Topology.IsInducing.continuousMul`, and
`Topology.IsInducing.isTopologicalAddGroup` to pull back topological algebraic structures along a
topology-inducing homomorphism, stopping short of `IsTopologicalSemiring` and `IsTopologicalRing`.
This file supplies `Topology.IsInducing.isTopologicalSemiring` and
`Topology.IsInducing.isTopologicalRing` for any `NonUnitalRingHomClass` map into a topological
(semi)ring.

## Main results

* `Topology.IsInducing.isTopologicalSemiring`: pulling back `IsTopologicalSemiring` along a
  topology-inducing non-unital ring homomorphism.
* `Topology.IsInducing.isTopologicalRing`: pulling back `IsTopologicalRing` along a
  topology-inducing non-unital ring homomorphism.
-/

public section

namespace Topology.IsInducing

/-- Pulling back a topological semiring structure along a topology-inducing non-unital ring
homomorphism makes the domain a topological semiring. -/
protected theorem isTopologicalSemiring {R S F : Type*}
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalSemiring S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) (hf : IsInducing f) :
    IsTopologicalSemiring R :=
  { hf.continuousAdd f, hf.continuousMul f with }

/-- Pulling back a topological ring structure along a topology-inducing non-unital ring
homomorphism makes the domain a topological ring. -/
protected theorem isTopologicalRing {R S F : Type*}
    [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) (hf : IsInducing f) :
    IsTopologicalRing R :=
  { hf.isTopologicalAddGroup f, hf.continuousMul f with }

section Examples

example {R S : Type*} [Ring R] [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) : @IsTopologicalRing R (.induced f ‹_›) _ :=
  let _ : TopologicalSpace R := .induced f ‹_›
  IsInducing.isTopologicalRing f ⟨rfl⟩

end Examples

end Topology.IsInducing
