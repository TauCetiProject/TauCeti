/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Basis
public import TauCeti.Combinatorics.Graph.Stallings.Coset.Comparison
public import TauCeti.Combinatorics.Graph.Stallings.Product

/-!
# The product core and intersections of subgroups of a free group

For folded labelled graphs the based core of the product is a folded based core accepting the
intersection of the two accepted subgroups. It is therefore the canonical graph of that
intersection: for subgroups `H` and `K` of a free group, the core of the product of their
subgroup graphs at the pair of base vertices is isomorphic to the subgroup graph of `H ⊓ K`.
At any other pair of vertices the product accepts an intersection of conjugates of the two
subgroups, the conjugating elements being read along paths from the base vertices.

A spanning tree of the product core consequently gives a free basis of the intersection: the
tree-loop words of its positive non-tree darts generate the intersection freely, and the
rank of the intersection is the number of these darts.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 9, Lemma 9.3, Proposition 9.4, Corollary 9.5 and Proposition 9.8.
-/

public section

namespace TauCeti.StallingsGraph

open SerreGraph

universe u v w x y

variable {α : Type u} {S : StallingsGraph.{u, v, w} α} {T : StallingsGraph.{u, x, y} α}

/-- The based core of a product of folded graphs accepts the intersection of the subgroups
accepted by the factors. -/
theorem core_prod_subgroup (hS : S.IsFolded) (hT : T.IsFolded) :
    (S.prod T).core.subgroup (S.prod T).core.base = S.subgroup S.base ⊓ T.subgroup T.base := by
  rw [core_base, core_subgroup, prod_base, prod_subgroup hS hT]

/-- The based core of a product of folded graphs is the canonical graph of the intersection
of the subgroups accepted by the factors. -/
theorem nonempty_iso_core_prod_subgroupGraph (hS : S.IsFolded) (hT : T.IsFolded) :
    Nonempty (Iso (S.prod T).core (S.subgroup S.base ⊓ T.subgroup T.base).subgroupGraph) := by
  rw [← core_prod_subgroup hS hT]
  exact nonempty_iso_subgroupGraph (hS.prod hT).core (S.prod T).core_isCore

/-- At a pair of vertices reached from the base vertices by paths `p` and `q`, the product of
folded graphs accepts the intersection of the conjugates of the two based subgroups by the
inverses of the labels of `p` and `q`. -/
theorem prod_subgroup_eq_map_conj_inf (hS : S.IsFolded) (hT : T.IsFolded)
    {a : S.graph.V} {b : T.graph.V} (p : S.graph.Path S.base a) (q : T.graph.Path T.base b) :
    (S.prod T).subgroup (a, b) =
      (S.subgroup S.base).map (MulAut.conj (S.read p)⁻¹).toMonoidHom ⊓
        (T.subgroup T.base).map (MulAut.conj (T.read q)⁻¹).toMonoidHom := by
  rw [prod_subgroup hS hT, S.subgroup_conj p, T.subgroup_conj q]

section Basis

variable (R : (S.prod T).core.graph.SpanningTree) {O : Set (S.prod T).core.graph.E}

/-- The tree-loop words of the positive non-tree darts of the product core generate the
intersection of the subgroups accepted by two folded graphs. By
`lift_treeLoopWord_injective` they generate it freely. -/
theorem range_lift_treeLoopWord_core_prod (hS : S.IsFolded) (hT : T.IsFolded)
    (hO : (S.prod T).core.graph.IsOrientation O) :
    (FreeGroup.lift (fun e : ↥(O \ R.darts) =>
      (S.prod T).core.treeLoopWord R (S.prod T).core.base e.1)).range =
        S.subgroup S.base ⊓ T.subgroup T.base := by
  rw [range_lift_treeLoopWord _ R _ hO, core_prod_subgroup hS hT]

/-- The intersection of the subgroups accepted by two folded graphs is finitely generated
exactly when the product core has finitely many positive darts outside a spanning tree. -/
theorem fg_inf_subgroup_iff (hS : S.IsFolded) (hT : T.IsFolded)
    (hO : (S.prod T).core.graph.IsOrientation O) :
    Group.FG ↥(S.subgroup S.base ⊓ T.subgroup T.base) ↔ Finite ↥(O \ R.darts) := by
  rw [← core_prod_subgroup hS hT]
  exact fg_subgroup_iff _ R _ (hS.prod hT).core hO

/-- The rank of the intersection of the subgroups accepted by two folded graphs is the
number of positive darts of the product core outside a spanning tree. -/
theorem rank_inf_subgroup (hS : S.IsFolded) (hT : T.IsFolded)
    (hO : (S.prod T).core.graph.IsOrientation O)
    [Group.FG ↥(S.subgroup S.base ⊓ T.subgroup T.base)] :
    Group.rank ↥(S.subgroup S.base ⊓ T.subgroup T.base) = Nat.card ↥(O \ R.darts) := by
  have h := core_prod_subgroup hS hT
  have : Group.FG ↥((S.prod T).core.subgroup (S.prod T).core.base) := by
    rw [h]
    infer_instance
  rw [← Subgroup.rank_congr h, rank_subgroup _ R _ (hS.prod hT).core hO]

end Basis

end TauCeti.StallingsGraph

namespace Subgroup

open TauCeti StallingsGraph

variable {α : Type*} (H K : Subgroup (FreeGroup α))

/-- The core of the product of two subgroup graphs at the pair of base vertices accepts the
intersection of the subgroups. -/
theorem core_prod_subgroupGraph_subgroup :
    (H.subgroupGraph.prod K.subgroupGraph).core.subgroup
      (H.subgroupGraph.prod K.subgroupGraph).core.base = H ⊓ K := by
  rw [core_prod_subgroup H.subgroupGraph_isFolded K.subgroupGraph_isFolded,
    subgroupGraph_subgroup, subgroupGraph_subgroup]

/-- The core of the product of two subgroup graphs at the pair of base vertices is the
subgroup graph of the intersection. -/
theorem nonempty_iso_core_prod_subgroupGraph :
    Nonempty (Iso (H.subgroupGraph.prod K.subgroupGraph).core (H ⊓ K).subgroupGraph) := by
  simpa only [subgroupGraph_subgroup] using
    StallingsGraph.nonempty_iso_core_prod_subgroupGraph
      H.subgroupGraph_isFolded K.subgroupGraph_isFolded

/-- At every pair of vertices the product of two subgroup graphs accepts the intersection of
a conjugate of the first subgroup with a conjugate of the second. -/
theorem exists_prod_subgroupGraph_subgroup_eq (v : H.subgroupGraph.graph.V)
    (w : K.subgroupGraph.graph.V) :
    ∃ g h : FreeGroup α, (H.subgroupGraph.prod K.subgroupGraph).subgroup (v, w) =
      H.map (MulAut.conj g).toMonoidHom ⊓ K.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨p⟩ := ((SerreGraph.isCore_iff _ _).mp H.subgroupGraph_isCore).1 v
  obtain ⟨q⟩ := ((SerreGraph.isCore_iff _ _).mp K.subgroupGraph_isCore).1 w
  refine ⟨(H.subgroupGraph.read p)⁻¹, (K.subgroupGraph.read q)⁻¹, ?_⟩
  rw [prod_subgroup_eq_map_conj_inf H.subgroupGraph_isFolded K.subgroupGraph_isFolded p q,
    subgroupGraph_subgroup, subgroupGraph_subgroup]

end Subgroup
