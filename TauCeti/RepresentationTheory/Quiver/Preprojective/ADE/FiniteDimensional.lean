/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.InfiniteDimensional

/-!
# Finite-dimensional preprojective algebras of finite ADE diagrams

The additive preprojective algebra of every orientation of a finite simply-laced Dynkin diagram
is finite-dimensional over every field. The same holds for its signless presentation. For
connected diagrams with at least three vertices, this is the quadratic-dual presentation used
for zigzag algebras.

Transporting along graph isomorphisms extends both finiteness theorems to arbitrary graphs
isomorphic to a standard Dynkin diagram. Together with the non-Dynkin growth bound of
`TauCeti.RepresentationTheory.Quiver.Preprojective.InfiniteDimensional`, this yields the
complete finite/infinite-dimensionality dichotomy for connected finite simple graphs: both the
signless preprojective algebra of `DoubledQuiver G` and the preprojective algebra of every
orientation `OrientedQuiver G o` are finite-dimensional over `k` if and only if `G` is isomorphic
to the diagram of a valid Dynkin type (equivalently, a valid simply-laced Dynkin type).

The signless results retain the caller's neighborhood `Fintype` instances as explicit
parameters, so their conclusions refer to the quotient carrier formed with those enumerations.

## Main results

* `TauCeti.finiteDimensional_signlessPreprojectiveAlgebra_of_isSimplyLaced` and
  `TauCeti.finiteDimensional_preprojectiveAlgebra_of_isSimplyLaced`: finiteness for the standard
  simply-laced Dynkin diagrams.
* `TauCeti.finiteDimensional_signlessPreprojectiveAlgebra_of_iso` and
  `TauCeti.finiteDimensional_preprojectiveAlgebra_of_iso`: finiteness for any graph isomorphic to
  a standard Dynkin diagram.
* `TauCeti.finiteDimensional_signlessPreprojectiveAlgebra_iff` and
  `TauCeti.finiteDimensional_preprojectiveAlgebra_orientedQuiver_iff`: **the finite/infinite
  dichotomy for connected finite simple graphs.**

## References

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

/-- **The signless preprojective algebra of any graph isomorphic to a standard Dynkin diagram is
finite-dimensional** over every field. -/
theorem finiteDimensional_signlessPreprojectiveAlgebra_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] {t : DynkinType}
    (e : G ≃g diagramGraph t.cartanMatrix) :
    FiniteDimensional k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) := by
  obtain ⟨s, hs, -, ⟨f⟩⟩ := t.exists_isSimplyLaced_diagramGraph_iso
  have := finiteDimensional_signlessPreprojectiveAlgebra_of_isSimplyLaced k s hs
  exact (signlessPreprojectiveAlgebraEquiv k (e.trans f)).symm.toLinearEquiv.finiteDimensional

/-- **The additive preprojective algebra of every orientation of a graph isomorphic to a standard
Dynkin diagram is finite-dimensional** over every field. -/
theorem finiteDimensional_preprojectiveAlgebra_of_iso {V : Type*} [Finite V]
    {G : SimpleGraph V} {t : DynkinType} (e : G ≃g diagramGraph t.cartanMatrix)
    (o : Orientation G) :
    FiniteDimensional k (preprojectiveAlgebra k (OrientedQuiver G o)) := by
  have := finiteDimensional_signlessPreprojectiveAlgebra_of_iso k e
  have hb : G.IsBipartite :=
    (e.isAcyclic_iff.mpr t.isAcyclic_diagramGraph_cartanMatrix).isBipartite
  exact (hb.signlessPreprojectiveAlgebraEquiv k o).toLinearEquiv.finiteDimensional

/-- **The finite/infinite dichotomy for signless preprojective algebras**: for a connected finite
simple graph `G`, the signless preprojective algebra of `DoubledQuiver G` is finite-dimensional
over `k` if and only if `G` is isomorphic to the diagram of a valid Dynkin type. -/
theorem finiteDimensional_signlessPreprojectiveAlgebra_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} [∀ i, Fintype (G.neighborSet i)] (hG : G.Connected) :
    FiniteDimensional k (signlessPreprojectiveAlgebra k (DoubledQuiver G)) ↔
      ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) :=
  ⟨fun h => by_contra fun hD =>
    not_module_finite_signlessPreprojectiveAlgebra_of_not_exists_dynkinType_iso k hG hD h,
   fun ⟨_, _, ⟨e⟩⟩ => finiteDimensional_signlessPreprojectiveAlgebra_of_iso k e⟩

/-- **The finite/infinite dichotomy for preprojective algebras of oriented graphs**: for a
connected finite simple graph `G` and any orientation `o` of `G`, the preprojective algebra
`Π_k(OrientedQuiver G o)` is finite-dimensional over `k` if and only if `G` is isomorphic to the
diagram of a valid Dynkin type. -/
theorem finiteDimensional_preprojectiveAlgebra_orientedQuiver_iff {V : Type*} [Finite V]
    {G : SimpleGraph V} (hG : G.Connected) (o : Orientation G) :
    FiniteDimensional k (preprojectiveAlgebra k (OrientedQuiver G o)) ↔
      ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) :=
  ⟨fun h => by_contra fun hD =>
    not_module_finite_preprojectiveAlgebra_orientedQuiver_of_not_exists_dynkinType_iso k hG hD o h,
   fun ⟨_, _, ⟨e⟩⟩ => finiteDimensional_preprojectiveAlgebra_of_iso k e o⟩

end TauCeti
