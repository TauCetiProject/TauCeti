/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.FinitePaths
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# The path algebra of an acyclic quiver

A finite quiver with finitely many arrows between any two vertices has finitely many paths when it
is acyclic, and the paths are a basis of its path algebra; so the path algebra of such a quiver is
finite-dimensional over a division ring.

Acyclicity is not merely sufficient but **necessary**: an oriented cycle contributes its infinitely
many powers to the path basis, so a path algebra that is a finite module over a nonzero base ring
has no oriented cycle, whatever the quiver. For a finite quiver with finite arrow types the two
conditions therefore agree, and finite-dimensionality of `kQ` *is* acyclicity of `Q`. The loop
quiver is the boundary case, where the path algebra is the polynomial ring and
`TauCeti.not_finiteDimensional_pathAlgebra_oneLoop` records the failure directly.

This is the only place the generic path algebra of
`TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic` meets acyclicity, which is why it is a
module of its own: the path algebra itself needs nothing from the theory of acyclic quivers.

## Main results

* `TauCeti.finiteDimensional_pathAlgebra_of_isAcyclic`: the path algebra of a finite acyclic
  quiver with finite arrow types is finite-dimensional.
* `TauCeti.isAcyclic_of_module_finite_pathAlgebra`: **a path algebra that is a finite module over
  a nonzero base ring comes from an acyclic quiver**, with no finiteness assumed of the quiver.
* `TauCeti.finiteDimensional_pathAlgebra_iff_isAcyclic`: the two together, for a finite quiver
  with finite arrow types over a division ring.

## References

This file implements the finite-dimensionality part of Layer 0 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose statement is that
`kQ` is finite-dimensional exactly when `Q` has finitely many paths, the extensional form of
being finite and acyclic. See Assem--Simson--Skowroński, *Elements of the Representation Theory of
Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v w

/-- The path algebra of a finite acyclic quiver is finite-dimensional. -/
theorem finiteDimensional_pathAlgebra_of_isAcyclic (k : Type w) (Q : Type u) [DivisionRing k]
    [Quiver.{v} Q] [Finite Q] [∀ a b : Q, Finite (a ⟶ b)] (h : Quiver.IsAcyclic Q) :
    FiniteDimensional k (pathAlgebra k Q) :=
  letI := finite_paths_of_isAcyclic h
  module_finite_pathAlgebra k Q

/-- **A finite path algebra comes from an acyclic quiver.**  Over a nonzero base ring the paths are
a basis, so finitely many of them are available; an oriented cycle would already contribute its
infinitely many powers.  Neither the vertices nor the arrows are assumed finite: it is the path
algebra that carries the finiteness. -/
theorem isAcyclic_of_module_finite_pathAlgebra (k : Type w) (Q : Type u) [Semiring k]
    [Nontrivial k] [Quiver.{v} Q] (h : Module.Finite k (pathAlgebra k Q)) :
    Quiver.IsAcyclic Q :=
  isAcyclic_of_finite_paths ((module_finite_pathAlgebra_iff k Q).mp h)

/-- **Finite-dimensionality of the path algebra is acyclicity of the quiver**, for a finite quiver
with finite arrow types over a division ring.  This is the extensional reading of "no oriented
cycle" that the finite-dimensional-algebra theory of a quiver runs on. -/
theorem finiteDimensional_pathAlgebra_iff_isAcyclic (k : Type w) (Q : Type u) [DivisionRing k]
    [Quiver.{v} Q] [Finite Q] [∀ a b : Q, Finite (a ⟶ b)] :
    FiniteDimensional k (pathAlgebra k Q) ↔ Quiver.IsAcyclic Q :=
  ⟨isAcyclic_of_module_finite_pathAlgebra k Q, finiteDimensional_pathAlgebra_of_isAcyclic k Q⟩

end TauCeti
