/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Graph
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram

/-!
# The two-colouring of the Dynkin diagram of a Weyl group

The Coxeter matrix of a base `b` of a finite crystallographic root pairing has entry `2` at a pair
of simple roots exactly when they are orthogonal, that is, when their Cartan entries vanish. Its
Coxeter graph is therefore the Dynkin diagram of `b` with edge multiplicities forgotten
(`RootPairing.graph_coxeterMatrixOfBase`). For a root system this diagram is a forest, because the
Cartan matrix is of finite type, so it admits a two-colouring by `Bool`; for an irreducible
reduced root system it is a tree, so the two-colouring is unique up to exchanging the colours.

Consequently the bipartite Coxeter element `CoxeterSystem.bipartiteCoxeterElement` of the Coxeter
system `TauCeti.weylCoxeterSystem` of the Weyl group is available for every colouring of the
Dynkin diagram, and for an irreducible reduced root system the bipartite Coxeter elements of the
two colourings are mutually inverse and conjugate
(`CoxeterSystem.isConj_bipartiteCoxeterElement` with
`RootPairing.preconnected_graph_coxeterMatrixOfBase`).

## Main results

* `RootPairing.graph_coxeterMatrixOfBase`: the Coxeter graph of a base is its Dynkin diagram.
* `RootPairing.isAcyclic_graph_coxeterMatrixOfBase` and
  `RootPairing.nonempty_coloring_graph_coxeterMatrixOfBase`: for a root system it is a forest, and
  so has a two-colouring.
* `RootPairing.preconnected_graph_coxeterMatrixOfBase`: for an irreducible reduced root pairing it
  is connected.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Ch. VI, §4.
-/

public section

namespace RootPairing

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]
  (b : P.Base)

/-- **The Coxeter graph of a base is its Dynkin diagram**: two distinct simple roots are joined
exactly when both of their Cartan entries are nonzero. -/
theorem graph_coxeterMatrixOfBase :
    (coxeterMatrixOfBase P b).graph = diagramGraph b.cartanMatrix := by
  ext i j
  simp only [CoxeterMatrix.graph_adj, diagramGraph_adj, ne_eq, coxeterMatrixOfBase_eq_two_iff,
    ← cartanMatrix_mul_cartanMatrix_eq_zero_iff_isOrthogonal, mul_eq_zero, not_or]

/-- **The Coxeter graph of a base of a root system is a forest.** -/
theorem isAcyclic_graph_coxeterMatrixOfBase [P.IsRootSystem] :
    (coxeterMatrixOfBase P b).graph.IsAcyclic := by
  rw [graph_coxeterMatrixOfBase]
  exact (isFiniteType_cartanMatrix b).isAcyclic_diagramGraph

/-- **The Dynkin diagram of a root system has a two-colouring**: its simple roots can be coloured
by `Bool` so that simple roots of the same colour are orthogonal. -/
theorem nonempty_coloring_graph_coxeterMatrixOfBase [P.IsRootSystem] :
    Nonempty ((coxeterMatrixOfBase P b).graph.Coloring Bool) :=
  Nonempty.map ((coxeterMatrixOfBase P b).graph.recolorOfEquiv finTwoEquiv)
    (isAcyclic_graph_coxeterMatrixOfBase P b).isBipartite

/-- **The Coxeter graph of a base of an irreducible reduced root pairing is connected**, so its
two-colourings agree up to exchanging the colours. -/
theorem preconnected_graph_coxeterMatrixOfBase [P.IsReduced] [P.IsIrreducible] :
    (coxeterMatrixOfBase P b).graph.Preconnected := by
  rw [graph_coxeterMatrixOfBase]
  exact preconnected_diagramGraph_cartanMatrix b

end RootPairing
