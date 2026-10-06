/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic

/-!
# Finite-dimensional preprojective algebras of finite ADE diagrams

The additive preprojective algebra of every orientation of a finite simply-laced Dynkin diagram
is finite-dimensional over every field. The same holds for its signless presentation. For
connected diagrams with at least three vertices, this is the quadratic-dual presentation used
for zigzag algebras.

The signless results retain the caller's neighborhood `Fintype` instances as explicit
parameters, so their conclusions refer to the quotient carrier formed with those enumerations.

The `A`, `D`, and `E` calculations are supplied by the type-specific developments.
The local presentation and finite-Dynkin finiteness theorem are discussed in
Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson problem*,
Section 1. The signless comparison follows Huerfano--Khovanov,
*A category for the adjoint representation*, Section 3, https://arxiv.org/abs/math/0002060.
-/

public section

namespace TauCeti

open DoubledQuiver

/-- Every neighborhood in a graph on a finite vertex type has a finite enumeration. -/
private noncomputable local instance adeNeighborSetFintype {V : Type*} [Finite V]
    (G : SimpleGraph V) (i : V) : Fintype (G.neighborSet i) := Fintype.ofFinite _

variable (k : Type*) [Field k]

/-- The signless preprojective algebra of every finite simply-laced Dynkin diagram is
finite-dimensional over every field. -/
theorem finiteDimensional_signlessPreprojectiveAlgebra_of_isSimplyLaced
    (t : DynkinType)
    [hN : ∀ i, Fintype ((diagramGraph t.cartanMatrix).neighborSet i)]
    (hs : t.IsSimplyLaced) :
    FiniteDimensional k
      (signlessPreprojectiveAlgebra k (DoubledQuiver (diagramGraph t.cartanMatrix))) := by
  -- Retain the caller's quotient type while reusing the finite enumerations of the
  -- type-specific calculations; `Fintype` structures are unique.
  have hN_eq : hN = fun i => adeNeighborSetFintype (diagramGraph t.cartanMatrix) i :=
    Subsingleton.elim _ _
  cases hN_eq
  cases t with
  | A n | D n | E6 | E7 => infer_instance
  | E8 =>
    -- Transport the complete quotient type, including its vertex and star instances.
    have key : ∀ G : SimpleGraph (Fin 8), zigzagE8Graph = G →
        FiniteDimensional k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
      rintro G rfl
      infer_instance
    exact key _ zigzagE8Graph_eq_diagramGraph
  | B n | C n | F4 | G2 => simp at hs

/-- The additive preprojective algebra of every orientation of a finite simply-laced
Dynkin diagram is finite-dimensional over every field, including characteristic two. -/
theorem finiteDimensional_preprojectiveAlgebra_of_isSimplyLaced
    (t : DynkinType) (hs : t.IsSimplyLaced)
    (o : Orientation (diagramGraph t.cartanMatrix)) :
    FiniteDimensional k
      (preprojectiveAlgebra k (OrientedQuiver (diagramGraph t.cartanMatrix) o)) := by
  cases t with
  | A n | D n | E6 | E7 => infer_instance
  | E8 =>
    -- The orientation depends on the graph, so transport both together.
    have key : ∀ G : SimpleGraph (Fin 8), zigzagE8Graph = G →
        ∀ o : Orientation G,
          FiniteDimensional k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
      rintro G rfl o
      infer_instance
    exact key _ zigzagE8Graph_eq_diagramGraph o
  | B n | C n | F4 | G2 => simp at hs

end TauCeti
