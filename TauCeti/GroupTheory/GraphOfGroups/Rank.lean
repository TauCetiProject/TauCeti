/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.SpanningTree
public import TauCeti.Combinatorics.Graph.Serre.Parallel
public import TauCeti.GroupTheory.Coprod.Finiteness
public import TauCeti.GroupTheory.GraphOfGroups.GraphPresentation
public import TauCeti.GroupTheory.GraphOfGroups.SpanningTree
public import TauCeti.GroupTheory.FreeGroup.Rank

/-!
# Rank of graph path groups in spanning-tree coordinates

For a spanning tree and an orientation of a Serre graph, the positive non-tree darts
index a free basis of the reduced closed-path group. This group is finitely generated
exactly when there are finitely many such darts, and then its rank is their cardinality.
The graph itself need not be finite: an infinite tree with finitely many extra edges is
included. The same holds, with the positive darts outside `T`, for the tree presentation of a
graph of groups with trivial vertex groups and for the presentation of a graph by its darts,
both killing a dart set `T` that need only be closed under reversal, not a tree. These
presentations give the fundamental group of the graph when `T` is the set of darts of a spanning
tree.

These statements use the minimum number of group generators, not merely the size of a
particular generating family. Loops and parallel edges remain distinct basis indices.

For a connected graph with finitely many vertices whose path group is finitely generated, a
spanning tree has one positive dart fewer than there are vertices, which gives the Euler form
of the rank: the rank plus the number of vertices is the number of geometric edges plus one.
In particular the path group of a rose has rank its number of petals, and the fundamental group of
`n` parallel edges, `0 < n`, has rank `n - 1`, both as a reduced path group and in the
presentation relative to any spanning tree.

The fundamental group of a graph of groups with finitely many vertices and geometric edges and
finitely generated vertex groups is finitely generated, relative to any set of darts. For a
graph of groups with trivial vertex groups over a rose, relative to its maximal tree, the
fundamental group is free on the petals (`TauCeti.GraphOfGroups.π₁Tree.roseEquivFreeGroup`), so it
is finitely generated exactly when there are finitely many petals
(`TauCeti.GraphOfGroups.π₁Tree.fg_rose_iff_finite`), and then its rank is their number
(`TauCeti.GraphOfGroups.π₁Tree.rank_rose`).

The same holds for the fundamental group `π₁(𝔸, v)` of closed `𝔸`-paths at the vertex of the
rose. With trivial vertex group it is free on the petals
(`TauCeti.GraphOfGroups.π₁.roseEquivFreeGroup`), so when finitely generated its rank is the number
of petals (`TauCeti.GraphOfGroups.π₁.rank_rose`). With finitely generated vertex group it is
finitely generated exactly when there are finitely many petals
(`TauCeti.GraphOfGroups.π₁.fg_rose_iff_finite`): it maps onto the free group on the petals by
killing the vertex group.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.3–3.1.
* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
* I. Kapovich, A. Myasnikov, *Stallings foldings and subgroups of free groups*, §8, Lemma 8.2.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Proposition 2.4(3).
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

namespace TauCeti.SerreGraph

universe u w

variable {Γ : SerreGraph.{u, w}}

/-- The reduced closed-path group of a connected graph with finitely many geometric edges is
finitely generated. -/
theorem Connected.fg_pathGroup (h : Γ.Connected) [Finite Γ.GeomEdge] (v : Γ.V) :
    Group.FG (PathGroup Γ v) := by
  obtain ⟨T⟩ := Γ.exists_spanningTree h
  obtain ⟨O, hO⟩ := Γ.exists_isOrientation
  have : Finite O := Finite.of_injective _ hO.bijective_toGeomEdge.1
  exact (T.fg_pathGroup_iff v hO).mpr (Finite.Set.subset O Set.sdiff_subset)

/-- For a connected graph with finitely many vertices whose reduced closed-path group is
finitely generated, the rank of that group plus the number of vertices is the number of
positive darts plus one. -/
theorem IsOrientation.rank_pathGroup_add_card {O : Set Γ.E} (hO : Γ.IsOrientation O)
    (h : Γ.Connected) (v : Γ.V) [Finite Γ.V] [Group.FG (PathGroup Γ v)] :
    Group.rank (PathGroup Γ v) + Nat.card Γ.V = Nat.card O + 1 := by
  obtain ⟨T⟩ := Γ.exists_spanningTree h
  have h₁ : Finite ↥(O \ T.darts) := (T.fg_pathGroup_iff v hO).mp inferInstance
  have h₂ : Finite ↥(T.darts ∩ O) := (T.isSpanningForest hO).finite.to_subtype
  have : Finite O := Finite.Set.subset (O \ T.darts ∪ T.darts ∩ O) (by grind)
  rw [T.rank_pathGroup v hO, T.card_diff_add_card hO]

/-- The Euler form of the rank of the reduced closed-path group of a connected graph with
finitely many vertices, when that group is finitely generated (for instance when there are
finitely many geometric edges, see `Connected.fg_pathGroup`): the rank plus the number of
vertices is the number of geometric edges plus one. -/
theorem Connected.rank_pathGroup_add_card (h : Γ.Connected) (v : Γ.V) [Finite Γ.V]
    [Group.FG (PathGroup Γ v)] :
    Group.rank (PathGroup Γ v) + Nat.card Γ.V = Nat.card Γ.GeomEdge + 1 := by
  obtain ⟨O, hO⟩ := Γ.exists_isOrientation
  rw [hO.rank_pathGroup_add_card h v, Nat.card_eq_of_bijective _ hO.bijective_toGeomEdge]

/-- When the reduced closed-path group of a rose is finitely generated, its rank is the number
of petals. -/
theorem rank_pathGroup_rose (α : Type*) (v : (rose α).V) [Group.FG (PathGroup (rose α) v)] :
    Group.rank (PathGroup (rose α) v) = Nat.card α := by
  have h := (rose_connected α).rank_pathGroup_add_card v
  rwa [Nat.card_congr (roseGeomEdgeEquiv α), Nat.card_unique, add_left_inj] at h

/-- The reduced path group of `n` parallel edges, `0 < n`, has rank `n - 1`. -/
theorem rank_pathGroup_parallelGraph_add_one {α : Type*} [Nonempty α] (v : (parallelGraph α).V)
    [Group.FG (PathGroup (parallelGraph α) v)] :
    Group.rank (PathGroup (parallelGraph α) v) + 1 = Nat.card α := by
  have h := (parallelGraph_connected_iff.mpr ‹Nonempty α›).rank_pathGroup_add_card v
  have hV : Nat.card (parallelGraph α).V = 2 := Nat.card_eq_fintype_card.trans rfl
  rw [hV, Nat.card_congr (parallelGraphGeomEdgeEquiv α)] at h
  omega

/-- Relative to any spanning tree, the presentation of the fundamental group of `n` parallel
edges has rank `n - 1`. -/
theorem rank_graphPresentation_parallelGraph_add_one {α : Type*}
    (T : (parallelGraph α).SpanningTree)
    [Group.FG ((parallelGraph α).GraphPresentation T.darts)] :
    Group.rank ((parallelGraph α).GraphPresentation T.darts) + 1 = Nat.card α := by
  have : Nonempty α := parallelGraph_connected_iff.mp ((nonempty_spanningTree_iff _).mp ⟨T⟩)
  have : Group.FG (PathGroup (parallelGraph α) false) :=
    Group.fg_of_surjective (f := (T.pathGroupEquivGraphPresentation false).symm.toMonoidHom)
      (MulEquiv.surjective _)
  rw [← Group.rank_congr (T.pathGroupEquivGraphPresentation false)]
  exact rank_pathGroup_parallelGraph_add_one false

end TauCeti.SerreGraph

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

namespace TauCeti.SerreGraph.GraphPresentation

universe u w

variable {Γ : SerreGraph.{u, w}} {O T : Set Γ.E} (hO : Γ.IsOrientation O)
  (hT : ∀ e ∈ T, Γ.rev e ∈ T)

include hO hT

/-- The presentation of a graph by its darts killing a reversal-closed dart set `T` is finitely
generated exactly when finitely many positive darts lie outside `T`. -/
theorem fg_iff_finite : Group.FG (Γ.GraphPresentation T) ↔ Finite ↥(O \ T) :=
  (FreeGroupBasis.ofRepr (equivFreeGroup hO hT)).fg_iff_finite

/-- The rank of the presentation of a graph by its darts killing a reversal-closed dart set `T`
is the number of positive darts outside `T`. -/
theorem rank_eq_nat_card [Group.FG (Γ.GraphPresentation T)] :
    Group.rank (Γ.GraphPresentation T) = Nat.card ↥(O \ T) :=
  (FreeGroupBasis.ofRepr (equivFreeGroup hO hT)).rank_eq_nat_card

end TauCeti.SerreGraph.GraphPresentation

namespace TauCeti.GraphOfGroups.π₁Tree

universe u v w x

/-- The fundamental group of a graph of groups with finitely many vertices and geometric edges
and finitely generated vertex groups is finitely generated, relative to any set of darts. -/
instance {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (T : Set Γ.E) [Finite Γ.V]
    [Finite Γ.GeomEdge] [∀ a, Group.FG (𝔸.vertexGroup a)] : Group.FG (π₁Tree 𝔸 T) := by
  obtain ⟨O, hO⟩ := Γ.exists_isOrientation
  have : Finite O := Finite.of_injective _ hO.bijective_toGeomEdge.1
  exact Group.fg_of_surjective (ofCoprod_surjective (𝔸 := 𝔸) (T := T) hO.mem_or_rev_mem)

variable {α : Type v} (𝔸 : GraphOfGroups.{0, v, w, x} (SerreGraph.rose α))
  [∀ a, Subsingleton (𝔸.vertexGroup a)] (T : Set (SerreGraph.rose α).E) [IsEmpty T]

/-- The fundamental group of a graph of groups with trivial vertex groups over a rose is
finitely generated exactly when the rose has finitely many petals. -/
theorem fg_rose_iff_finite : Group.FG (π₁Tree 𝔸 T) ↔ Finite α :=
  (FreeGroupBasis.ofRepr (roseEquivFreeGroup 𝔸 T)).fg_iff_finite

/-- The fundamental group of a graph of groups with trivial vertex groups over a rose, when
finitely generated, has rank the number of petals: for the rose with `n` petals it is free of
rank `n`. -/
theorem rank_rose [Group.FG (π₁Tree 𝔸 T)] : Group.rank (π₁Tree 𝔸 T) = Nat.card α :=
  (FreeGroupBasis.ofRepr (roseEquivFreeGroup 𝔸 T)).rank_eq_nat_card

end TauCeti.GraphOfGroups.π₁Tree

namespace TauCeti.GraphOfGroups.π₁

universe v w x

variable {α : Type v} (𝔸 : GraphOfGroups.{0, v, w, x} (SerreGraph.rose α))
  (v₀ : (SerreGraph.rose α).V)

/-- The fundamental group at the vertex of a graph of groups with trivial vertex groups over a
rose, when finitely generated, has rank the number of petals: for the rose with `n` petals it is
free of rank `n`. -/
theorem rank_rose [∀ a, Subsingleton (𝔸.vertexGroup a)] [Group.FG (π₁ 𝔸 v₀)] :
    Group.rank (π₁ 𝔸 v₀) = Nat.card α :=
  (FreeGroupBasis.ofRepr (roseEquivFreeGroup 𝔸 v₀)).rank_eq_nat_card

/-- The homomorphism from the fundamental group at the vertex of a graph of groups over a rose to
the free group on the petals that kills the vertex group and sends the class of the dart `(a, b)`
to `a` or `a⁻¹` according to `b`. -/
private noncomputable def roseToFreeGroup : π₁ 𝔸 v₀ →* FreeGroup α :=
  (π₁Tree.lift (T := (SerreGraph.roseTree α).darts) (fun _ => 1)
      (fun e => cond e.2 (FreeGroup.of e.1) (FreeGroup.of e.1)⁻¹)
      (fun e he => isEmptyElim (⟨e, he⟩ : (SerreGraph.roseTree α).darts))
      (fun e => by obtain ⟨a, b⟩ := e; cases b <;> simp) (fun _ _ => by simp)).comp
    (π₁Equiv 𝔸 v₀ (SerreGraph.roseTree α)).toMonoidHom

private theorem roseToFreeGroup_surjective : Function.Surjective (roseToFreeGroup 𝔸 v₀) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← FreeGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  refine ⟨ofPathGroup 𝔸 v₀ ((SerreGraph.roseTree α).loop v₀ (a, true)), ?_⟩
  rw [roseToFreeGroup, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    π₁Equiv_ofPathGroup_loop 𝔸 v₀ _ (a, true)]
  exact π₁Tree.lift_edge ..

/-- The fundamental group at the vertex of a graph of groups over a rose with finitely generated
vertex group is finitely generated exactly when the rose has finitely many petals. -/
theorem fg_rose_iff_finite [∀ a, Group.FG (𝔸.vertexGroup a)] : Group.FG (π₁ 𝔸 v₀) ↔ Finite α := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have := Group.fg_of_surjective (roseToFreeGroup_surjective 𝔸 v₀)
    exact (FreeGroupBasis.ofRepr (MulEquiv.refl (FreeGroup α))).finite_of_fg
  · exact Group.fg_of_surjective (f := (π₁Equiv 𝔸 v₀ (SerreGraph.roseTree α)).symm.toMonoidHom)
      (MulEquiv.surjective _)

/-- The fundamental group at the vertex of a graph of groups over a rose with finitely many petals
and finitely generated vertex group is finitely generated. -/
instance [∀ a, Group.FG (𝔸.vertexGroup a)] [Finite α] : Group.FG (π₁ 𝔸 v₀) :=
  (fg_rose_iff_finite 𝔸 v₀).2 ‹_›

end TauCeti.GraphOfGroups.π₁
