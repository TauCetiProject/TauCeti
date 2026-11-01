/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Basic

/-!
# Separation, countability and local compactness of the point topology

Let `A` be a `k`-algebra and `R` a topological `k`-algebra. The point topology on the `R`-points
`A →ₐ[k] R` is induced from the product topology on `A → R`, and for `A` of finite type also from
`R ^ n` by evaluation at finitely many generators. Point-set properties of `R` therefore pass to the
points:

* if `R` is Hausdorff, so are the points;
* if `R` is totally disconnected, so are the points;
* if `R` is second countable and `A` is of finite type, so are the points;
* if `R` is locally compact and T1 and `A` is of finite type, so are the points (this is
  `TauCeti.PointTopology.locallyCompactSpace_of_finiteType`, made an instance here).

All four are instances, both on `A →ₐ[k] R` and on the convolution type `WithConv (A →ₐ[k] R)`
carrying the group of points of an affine group scheme. Over a nonarchimedean local field `E`, which
is Hausdorff, totally disconnected, locally compact and second countable
(`TauCeti/NumberTheory/LocalField/Topology.lean`), they make the group `G(E)` of points of an affine
group `G = Spec H` over `E` a Hausdorff and totally disconnected topological group, locally compact
and second countable when `H` is of finite type.

## Main declarations

* `TauCeti.PointTopology.instT2Space`, `TauCeti.PointTopology.instT2SpaceWithConv`.
* `TauCeti.PointTopology.instTotallyDisconnectedSpace`,
  `TauCeti.PointTopology.instTotallyDisconnectedSpaceWithConv`.
* `TauCeti.PointTopology.instSecondCountableTopology`,
  `TauCeti.PointTopology.instSecondCountableTopologyWithConv`.
* `TauCeti.PointTopology.instLocallyCompactSpaceWithConv`, with
  `TauCeti.PointTopology.locallyCompactSpace_of_finiteType` made an instance.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2.
-/

public section

open Topology

namespace TauCeti.PointTopology

section Semiring

variable {k A R : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Semiring R] [Algebra k R]
  [TopologicalSpace R]

/-- Points with values in a Hausdorff ring form a Hausdorff space. -/
instance instT2Space [T2Space R] : T2Space (A →ₐ[k] R) :=
  isEmbedding_coeFn.t2Space

/-- The group of points with values in a Hausdorff ring is Hausdorff. -/
instance instT2SpaceWithConv [T2Space R] : T2Space (WithConv (A →ₐ[k] R)) :=
  isHomeomorph_ofConv.isEmbedding.t2Space

/-- Points with values in a totally disconnected ring form a totally disconnected space. -/
instance instTotallyDisconnectedSpace [TotallyDisconnectedSpace R] :
    TotallyDisconnectedSpace (A →ₐ[k] R) :=
  isEmbedding_coeFn.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- The group of points with values in a totally disconnected ring is totally disconnected. -/
instance instTotallyDisconnectedSpaceWithConv [TotallyDisconnectedSpace R] :
    TotallyDisconnectedSpace (WithConv (A →ₐ[k] R)) :=
  isHomeomorph_ofConv.isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

end Semiring

section CommSemiring

variable {k A R : Type*} [CommSemiring k] [CommSemiring A] [Algebra k A] [CommSemiring R]
  [Algebra k R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- Points of a finite type algebra with values in a second countable ring form a second countable
space, since finitely many generators embed them in a finite power of the ring. -/
instance instSecondCountableTopology [SecondCountableTopology R] [Algebra.FiniteType k A] :
    SecondCountableTopology (A →ₐ[k] R) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  exact (isEmbedding_eval_generators (a := ((↑) : s → A))
    (by simpa using hs)).secondCountableTopology

/-- The group of points of a finite type algebra with values in a second countable ring is second
countable. -/
instance instSecondCountableTopologyWithConv [SecondCountableTopology R]
    [Algebra.FiniteType k A] : SecondCountableTopology (WithConv (A →ₐ[k] R)) :=
  isHomeomorph_ofConv.isEmbedding.secondCountableTopology

end CommSemiring

section CommRing

variable {k A R : Type*} [CommRing k] [CommRing A] [Algebra k A] [CommRing R] [Algebra k R]
  [TopologicalSpace R] [IsTopologicalSemiring R] [T1Space R] [LocallyCompactSpace R]
  [Algebra.FiniteType k A]

attribute [instance] locallyCompactSpace_of_finiteType

/-- The group of points of a finite type algebra with values in a locally compact T1 ring is
locally compact. -/
instance instLocallyCompactSpaceWithConv : LocallyCompactSpace (WithConv (A →ₐ[k] R)) :=
  isHomeomorph_ofConv.isClosedEmbedding.locallyCompactSpace

end CommRing

end TauCeti.PointTopology
