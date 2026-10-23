/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver.Basic
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.IrreducibleMorphism
public import TauCeti.RepresentationTheory.Quiver.Representation.HomDifferential

/-!
# The quiver of irreducible morphisms of a quiver's representations

This file specializes `TauCeti.IrreducibleMorphismQuiver` to the pointwise finite-dimensional
representations of a quiver `Q`: its vertices are the isomorphism classes of pointwise
finite-dimensional indecomposable representations, and its arrows index a basis of `rad / rad²`
between representatives.

For a quiver with finitely many vertices, these spaces are finite-dimensional even if the quiver
has infinitely many arrows or oriented cycles. Finite representation type is exactly finiteness
of the vertex type, and then the total arrow type is finite too.

The Hom differential identifies representation morphisms with a subspace of the finite product of
vertex-map spaces, which supplies the finite dimensionality of morphism spaces.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. I (2006), IV.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

namespace IrreducibleMorphismQuiver

instance [Finite Q] (a b : IrreducibleMorphismQuiver k (IsFinDim.{u, v, w, t} k Q)) :
    FiniteDimensional k (a.representative ⟶ b.representative) :=
  QuiverRep.finiteDimensional_hom a.representative_property.1 b.representative_property.1

instance [Finite Q] (a : IrreducibleMorphismQuiver k (IsFinDim.{u, v, w, t} k Q)) :
    IsLocalRing (End a.representative) :=
  (QuiverRep.indecomposable_iff_isLocalRing_end a.representative_property.1).mp
    a.representative_property.2

end IrreducibleMorphismQuiver

variable (k Q)

/-- Finite representation type is precisely finiteness of the vertices of the irreducible
morphism quiver. -/
@[simp]
theorem finite_irreducibleMorphismQuiver_iff :
    Finite (IrreducibleMorphismQuiver k (IsFinDim.{u, v, w, t} k Q)) ↔
      IsFiniteRepType.{u, v, w, t} k Q :=
  (Equiv.finite_iff IrreducibleMorphismQuiver.equivSkeleton).trans
    (isFiniteRepType_iff (k := k) (Q := Q)).symm

/-- In finite representation type, the irreducible morphism quiver has finitely many arrows
in total. -/
theorem IsFiniteRepType.finite_irreducibleMorphismQuiver_arrows [Finite Q]
    (h : IsFiniteRepType.{u, v, w, t} k Q) :
    Finite (Σ a b : IrreducibleMorphismQuiver k (IsFinDim.{u, v, w, t} k Q), a ⟶ b) := by
  have : Finite (IrreducibleMorphismQuiver k (IsFinDim.{u, v, w, t} k Q)) :=
    (finite_irreducibleMorphismQuiver_iff k Q).mpr h
  infer_instance

end TauCeti
