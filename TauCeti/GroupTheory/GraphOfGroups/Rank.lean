/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.PathGroup
public import TauCeti.GroupTheory.FreeGroup.Rank

/-!
# Rank of graph path groups in spanning-tree coordinates

For a spanning tree and an orientation of a Serre graph, the positive non-tree darts
index a free basis of the reduced closed-path group. This group is finitely generated
exactly when there are finitely many such darts, and then its rank is their cardinality.
The graph itself need not be finite: an infinite tree with finitely many extra edges is
included. For the presentation with trivial vertex groups, only reversal closure of the
killed dart set is required; it need not be a tree.

These statements use the minimum number of group generators, not merely the size of a
particular generating family. Loops and parallel edges remain distinct basis indices.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.3–3.1.
* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
-/

public section

namespace TauCeti.SerreGraph.SpanningTree

universe u w

variable {Γ : SerreGraph.{u, w}} (T : Γ.SpanningTree) (v : Γ.V)
  {O : Set Γ.E} (hO : Γ.IsOrientation O)

include hO

/-- The reduced closed-path group is finitely generated exactly when the positive
non-tree dart set is finite, even if the graph has infinitely many vertices or tree darts. -/
theorem fg_pathGroup_iff : Group.FG (PathGroup Γ v) ↔ Finite ↥(O \ T.darts) :=
  (FreeGroupBasis.ofRepr (T.pathGroupEquivFreeGroup v hO)).fg_iff_finite

/-- The rank of the reduced closed-path group is the number of positive non-tree darts. -/
theorem rank_pathGroup [Group.FG (PathGroup Γ v)] :
    Group.rank (PathGroup Γ v) = Nat.card ↥(O \ T.darts) :=
  (FreeGroupBasis.ofRepr (T.pathGroupEquivFreeGroup v hO)).rank_eq_nat_card

end TauCeti.SerreGraph.SpanningTree

namespace TauCeti.GraphOfGroups.π₁Tree

universe u v w x

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ)
  [∀ a, Subsingleton (𝔸.vertexGroup a)] {O T : Set Γ.E}
  (hO : Γ.IsOrientation O) (hT : ∀ e ∈ T, Γ.rev e ∈ T)

include hO hT

/-- With trivial vertex groups, the presentation killing a reversal-closed dart set is
finitely generated exactly when the remaining positive dart set is finite. -/
theorem fg_iff_finite : Group.FG (π₁Tree 𝔸 T) ↔ Finite ↥(O \ T) :=
  (FreeGroupBasis.ofRepr (equivFreeGroup 𝔸 hO hT)).fg_iff_finite

/-- With trivial vertex groups, the rank of the presentation killing a reversal-closed
dart set is the number of remaining positive darts. -/
theorem rank_eq_nat_card [Group.FG (π₁Tree 𝔸 T)] :
    Group.rank (π₁Tree 𝔸 T) = Nat.card ↥(O \ T) :=
  (FreeGroupBasis.ofRepr (equivFreeGroup 𝔸 hO hT)).rank_eq_nat_card

end TauCeti.GraphOfGroups.π₁Tree
