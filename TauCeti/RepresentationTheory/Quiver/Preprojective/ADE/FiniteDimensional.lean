/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeE.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.InducedSubgraph
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Isomorphism

/-!
# Finite-dimensional preprojective algebras of finite ADE diagrams

The additive preprojective algebra of every orientation of a finite simply-laced Dynkin diagram
is finite-dimensional over every field. The same holds for its signless presentation. For
connected diagrams with at least three vertices, this is the quadratic-dual presentation used
for zigzag algebras.

The signless results retain the caller's neighborhood `Fintype` instances as explicit
parameters, so their conclusions refer to the quotient carrier formed with those enumerations.

The `A`, `D`, `E₆`, and `E₈` calculations are supplied by the type-specific developments.
For `E₇`, the Bourbaki-labelled inclusion into `E₈`, recorded in
`TauCeti.DynkinType.cartanMatrix_E7_eq_submatrix_E8`, identifies its algebra with an induced
subgraph quotient. The local presentation and finite-Dynkin finiteness theorem are discussed in
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

private abbrev e7Nodes := Set.range (Fin.castAdd 1 : Fin 7 → Fin 8)

private noncomputable def e7InducedIso :
    diagramGraph DynkinType.E7.cartanMatrix ≃g zigzagE8Graph.induce e7Nodes where
  toEquiv := Equiv.ofInjective (Fin.castAdd 1 : Fin 7 → Fin 8) (Fin.castAdd_injective 7 1)
  map_rel_iff' := fun {i j : Fin 7} => by
    -- Normalize the range equivalence before rewriting the matrix: its coerced function
    -- otherwise retains the `DynkinType.E7.rank` index underneath the `Fin 7` presentation.
    change zigzagE8Graph.Adj (Fin.castAdd 1 i) (Fin.castAdd 1 j) ↔
      (diagramGraph DynkinType.E7.cartanMatrix).Adj i j
    rw [DynkinType.cartanMatrix_E7]
    -- The Cartan-matrix equation also changes the implicit vertex type to `Fin 7`.
    change zigzagE8Graph.Adj (Fin.castAdd 1 i) (Fin.castAdd 1 j) ↔
      (diagramGraph (CartanMatrix.E 7)).Adj i j
    rw [DynkinType.cartanMatrix_E7_eq_submatrix_E8,
      diagramGraph_submatrix (Fin.castAdd_injective 7 1), SimpleGraph.comap_adj,
      zigzagE8Graph_eq_diagramGraph, DynkinType.cartanMatrix_E8]
    rfl

private noncomputable def e7Coloring :
    (diagramGraph DynkinType.E7.cartanMatrix).Coloring Bool :=
  SimpleGraph.Coloring.mk
    (fun i => zigzagE8Coloring (e7InducedIso i).val) (by
      intro i j hij
      apply zigzagE8Coloring.valid
      exact SimpleGraph.induce_adj.mp (e7InducedIso.map_adj_iff.mpr hij))

variable (k : Type*) [Field k]

/-- The signless preprojective algebra of the Bourbaki-labelled `E₇` diagram is
finite-dimensional over every field. -/
instance instFiniteDimensionalSignlessPreprojectiveAlgebraE7
    [∀ i, Fintype ((diagramGraph DynkinType.E7.cartanMatrix).neighborSet i)] :
    FiniteDimensional k
      (signlessPreprojectiveAlgebra k
        (DoubledQuiver (diagramGraph DynkinType.E7.cartanMatrix))) := by
  let := moduleFinite_signlessPreprojectiveAlgebra_induce k zigzagE8Graph e7Nodes
  exact LinearEquiv.finiteDimensional
    (signlessPreprojectiveAlgebraGraphEquiv k e7InducedIso).symm.toLinearEquiv

/-- The additive preprojective algebra of every orientation of `E₇` is finite-dimensional
over every field. -/
instance instFiniteDimensionalPreprojectiveAlgebraE7
    (o : Orientation (diagramGraph DynkinType.E7.cartanMatrix)) :
    FiniteDimensional k
      (preprojectiveAlgebra k (OrientedQuiver (diagramGraph DynkinType.E7.cartanMatrix) o)) := by
  let c := fun i : OrientedQuiver (diagramGraph DynkinType.E7.cartanMatrix) o =>
    e7Coloring ((OrientedQuiver.vertexEquiv _ o).symm i)
  have hc : ∀ ⦃i j⦄ (a : i ⟶ j), c i ≠ c j := fun _ _ a => e7Coloring.valid a.1
  exact ((orientationSignlessPreprojectiveAlgebraEquiv o k).trans
    (symmetrifySignlessPreprojectiveAlgebraEquiv k hc)).toLinearEquiv.finiteDimensional

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
