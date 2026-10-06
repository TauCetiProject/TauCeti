/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.BranchComponents
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram

/-!
# The three arms of a branch diagram

A diagram which is a tree of maximum degree three, with a single vertex of degree three, becomes
three paths when that vertex is deleted: the general tree decomposition from
`TauCeti.Combinatorics.SimpleGraph.BranchComponents` applies, because deleting the branch vertex
leaves every other vertex with degree at most two.

For a connected simply-laced finite-type diagram with a branch vertex the hypotheses hold: the
finite-type degree bound supplies degree at most three, and the affine `D` obstruction in
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.UniqueBranch` says that the branch vertex is the
only vertex of degree three. The statement is kept free of the finite-type hypothesis so that it
also applies to diagrams not yet known to be of finite type.

This is the extraction step connecting branch diagrams to the model stars classified in
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Classification`.  The next step attaches each
path to the deleted vertex and reindexes the matrix onto `starCartanMatrix`.

## Main result

* `TauCeti.exists_three_path_components_of_isTree`: deleting the unique branch vertex from a
  diagram which is a tree of maximum degree three leaves three path components.

## References

This is the simply-laced extraction step in Layer 5 of the root-systems roadmap.  See J. E.
Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 11.4, and Bourbaki,
*Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, Section 4.
-/

public section

namespace TauCeti

open SimpleGraph

variable {B : Type*} [Fintype B] [DecidableEq B] {A : Matrix B B Int}

/-- **Deleting the branch vertex of a tree diagram of maximum degree three leaves three paths.**

The branch vertex `c` is assumed to be the only vertex of degree three. The equivalence indexes the
components by `Fin 3`; the component at `i` is a path graph on its own number of vertices.  These
cardinalities are the three arm lengths in the subsequent reindexing onto
`TauCeti.starCartanMatrix`. -/
theorem exists_three_path_components_of_isTree (htree : (diagramGraph A).IsTree)
    (hdeg : ∀ v, (diagramGraph A).degree v ≤ 3) {c : B} (hc : (diagramGraph A).degree c = 3)
    (huniq : ∀ v, (diagramGraph A).degree v = 3 → v = c) :
    ∃ e : Fin 3 ≃ ((diagramGraph A).induce ({c}ᶜ : Set B)).ConnectedComponent,
      ∀ i, Nonempty ((e i).toSimpleGraph ≃g pathGraph (Nat.card (e i))) := by
  refine TauCeti.IsTree.exists_equiv_pathGraph_components htree c hc fun v => ?_
  -- Deleting a vertex only removes edges, so it is enough to bound the degree in the diagram.
  have hle : ((diagramGraph A).induce ({c}ᶜ : Set B)).degree v ≤ (diagramGraph A).degree (v : B) :=
    (SimpleGraph.Copy.induce (diagramGraph A) ({c}ᶜ : Set B)).degree_le v
  refine le_trans hle ?_
  have hvc : (v : B) ≠ c := Set.mem_compl_singleton_iff.mp v.property
  have hv3 := hdeg (v : B)
  by_contra hv2
  exact hvc (huniq _ (by omega))

end TauCeti
