/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import TauCeti.Combinatorics.Graph.Serre.Parallel
public import TauCeti.GroupTheory.FreeGroup.Nielsen
public import TauCeti.GroupTheory.GraphOfGroups.ChangeOfTree
import TauCeti.GroupTheory.FreeGroup.Primitive

/-!
# Graphs of groups over graphs of parallel edges and the theta graph

A graph of parallel edges `SerreGraph.parallelGraph α` has the two vertices `false` and `true`,
and each edge `a` on its own is a maximal tree `SerreGraph.parallelTree a`. For a graph of groups
`𝔸` over it, based at the vertex `true`, the change of maximal tree
`π₁(𝔸, parallelTree a) ≃* π₁(𝔸, parallelTree a')` sends the generator of the dart `(b, true)`,
which crosses the edge `b` from `true` to `false`, to the product of the generators of `(b, true)`
and of `(a, false)`; it conjugates the vertex group `A_false` by the generator of `(a, true)`,
while, as for every change of maximal tree, the vertex group `A_true` at the base is fixed.

With trivial vertex groups the fundamental group relative to `parallelTree a` is free on the
edges other than `a`: once each edge `b` is given a direction, the generators of the oriented
darts of the edges `b ≠ a` form a free basis (`TauCeti.GraphOfGroups.parallelBasis`).

The theta graph is the graph of three parallel edges, `parallelGraph (Fin 3)`. Orient the edge
`0` from `false` to `true` and the edges `1` and `2` from `true` to `false`, and enumerate the two
edges other than `a` by `Fin.succAbove a`; this gives a free basis of rank two attached to each
maximal tree (`TauCeti.GraphOfGroups.thetaBasis`). In the coordinates of the bases attached to
the maximal trees `parallelTree 0` and `parallelTree 1`, the change of maximal tree is the
elementary Nielsen automorphism `x₀ ↦ x₀`, `x₁ ↦ x₁ x₀` of the free group of rank two.

## Main definitions

* `TauCeti.GraphOfGroups.parallelBasis`: the free basis of the fundamental group of a graph of
  groups with trivial vertex groups over a graph of parallel edges attached to a maximal tree.
* `TauCeti.GraphOfGroups.thetaBasis`: its rank-two enumeration for the theta graph.

## Main results

* `TauCeti.GraphOfGroups.π₁TreeEquiv_parallelTree_edge_true`: the change of maximal tree on a
  graph of parallel edges, on the generators of the darts.
* `TauCeti.GraphOfGroups.thetaBasis_repr_symm_trans_π₁TreeEquiv_trans_repr`: two maximal trees
  of the theta graph give free bases related by a Nielsen automorphism.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.1, Proposition 20.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Proposition 2.4(3).
* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
-/

public section

namespace TauCeti.GraphOfGroups

open SerreGraph

section changeOfTree

variable {α : Type*} (𝔸 : GraphOfGroups (parallelGraph α))

/-- **Change of maximal tree on a graph of parallel edges.** Based at the vertex `true`, changing
the maximal tree from the edge `a` to the edge `a'` sends the generator of the dart `(b, true)` to
the product of the generators of `(b, true)` and `(a, false)`. -/
theorem π₁TreeEquiv_parallelTree_edge_true (a a' b : α) :
    π₁TreeEquiv 𝔸 true (parallelTree a) (parallelTree a')
        (π₁Tree.edge (parallelTree a).darts (b, true)) =
      π₁Tree.edge (parallelTree a').darts (b, true) *
        π₁Tree.edge (parallelTree a').darts (a, false) := by
  -- `simp` cannot rewrite the end `!true` inside the dependent tree path, so `rw` does it.
  rw [π₁TreeEquiv_edge]
  simp only [parallelGraph_src, parallelGraph_tgt]
  rw [Bool.not_true]
  simp [Quiver.Hom.toPath, reverse_val (parallelGraph α), -parallelGraph_rev]

/-- Based at the vertex `true`, changing the maximal tree from the edge `a` to the edge `a'` sends
the generator of the dart `(b, false)` to the product of the generators of `(a, true)` and
`(b, false)`. -/
theorem π₁TreeEquiv_parallelTree_edge_false (a a' b : α) :
    π₁TreeEquiv 𝔸 true (parallelTree a) (parallelTree a')
        (π₁Tree.edge (parallelTree a).darts (b, false)) =
      π₁Tree.edge (parallelTree a').darts (a, true) *
        π₁Tree.edge (parallelTree a').darts (b, false) := by
  -- As for `(b, true)`, `rw` rewrites the end `!false` inside the dependent tree path.
  rw [π₁TreeEquiv_edge]
  simp only [parallelGraph_src, parallelGraph_tgt]
  rw [Bool.not_false]
  simp [Quiver.Hom.toPath, reverse_val (parallelGraph α)]

/-- Based at the vertex `true`, changing the maximal tree from the edge `a` to the edge `a'`
conjugates the vertex group `A_false` by the generator of the dart `(a, true)`. -/
theorem π₁TreeEquiv_parallelTree_of_false (a a' : α) (g : 𝔸.vertexGroup false) :
    π₁TreeEquiv 𝔸 true (parallelTree a) (parallelTree a')
        (π₁Tree.of (parallelTree a).darts false g) =
      π₁Tree.edge (parallelTree a').darts (a, true) * π₁Tree.of (parallelTree a').darts false g *
        π₁Tree.edge (parallelTree a').darts (a, false) := by
  -- Read backwards, `edge_rev` at `(a, true)` turns `(edge (a, true))⁻¹` into `edge (a, false)`.
  simp [Quiver.Hom.toPath, reverse_val (parallelGraph α), (π₁Tree.edge_rev (𝔸 := 𝔸) (a, true)).symm]

end changeOfTree

section freeBasis

variable {α : Type*} (𝔸 : GraphOfGroups (parallelGraph α)) [∀ v, Subsingleton (𝔸.vertexGroup v)]
  (o : α → Bool)

private def parallelIndexEquiv (a : α) :
    ↥({e : (parallelGraph α).E | e.2 = o e.1} \ (parallelTree a).darts) ≃ {b // b ≠ a} where
  toFun e := ⟨e.val.1, fun h => e.property.2 (mem_parallelTree_darts.2 h)⟩
  invFun b := ⟨(b.val, o b.val), rfl, fun h => b.property (mem_parallelTree_darts.1 h)⟩
  left_inv := by
    rintro ⟨⟨b, x⟩, hx, hb⟩
    obtain rfl : x = o b := hx
    rfl
  right_inv _ := rfl

/-- **The free basis attached to a maximal tree of a graph of parallel edges.** For a graph of
groups with trivial vertex groups over a graph of parallel edges, with each edge `b` directed
along its dart `(b, o b)`, the generators of these darts for the edges `b ≠ a` form a free basis
of the fundamental group `π₁(𝔸, parallelTree a)` relative to the maximal tree `parallelTree a`. -/
noncomputable def parallelBasis (a : α) :
    FreeGroupBasis {b // b ≠ a} (π₁Tree 𝔸 (parallelTree a).darts) :=
  .ofRepr ((π₁Tree.equivFreeGroup 𝔸 (parallelGraph_isOrientation o) (parallelTree a).rev_mem).trans
    (FreeGroup.freeGroupCongr (parallelIndexEquiv o a)))

@[simp] theorem parallelBasis_apply (a : α) (b : {b // b ≠ a}) : parallelBasis 𝔸 o a b =
    π₁Tree.edge (parallelTree a).darts ((b : α), o b) := by
  apply (parallelBasis 𝔸 o a).repr.injective
  rw [FreeGroupBasis.repr_apply_coe]
  simp [parallelBasis, parallelIndexEquiv,
    π₁Tree.equivFreeGroup_edge (parallelGraph_isOrientation o) (parallelTree a).rev_mem
      (e := ((b : α), o b)) ⟨rfl, fun h => b.property (mem_parallelTree_darts.1 h)⟩]

end freeBasis

section theta

variable (𝔸 : GraphOfGroups (parallelGraph (Fin 3))) [∀ v, Subsingleton (𝔸.vertexGroup v)]

/-- **The free basis of a theta graph of groups attached to a maximal tree.** For a graph of groups
with trivial vertex groups over the theta graph `parallelGraph (Fin 3)`, direct the edge `0` from
`false` to `true` and the edges `1` and `2` from `true` to `false`. The generators of the darts of
the two edges `a.succAbove i` other than `a`, for `i : Fin 2`, form a free basis of rank two of the
fundamental group `π₁(𝔸, parallelTree a)`. -/
noncomputable def thetaBasis (a : Fin 3) :
    FreeGroupBasis (Fin 2) (π₁Tree 𝔸 (parallelTree a).darts) :=
  (parallelBasis 𝔸 (fun b => b ≠ 0) a).reindex (finSuccAboveEquiv a).symm

@[simp] theorem thetaBasis_apply (a : Fin 3) (i : Fin 2) : thetaBasis 𝔸 a i =
    π₁Tree.edge (parallelTree a).darts (a.succAbove i, !decide (a.succAbove i = 0)) := by
  simp [thetaBasis, finSuccAboveEquiv_apply]

/-- **The two maximal trees of the theta graph give free bases related by a Nielsen
automorphism.** For a graph of groups with trivial vertex groups over the theta graph, read
`π₁(𝔸, parallelTree 0)` in the coordinates of its basis `thetaBasis 𝔸 0`, change the maximal tree
to `parallelTree 1`, based at the vertex `true`, and read the result in the coordinates of
`thetaBasis 𝔸 1`. The resulting automorphism of the free group of rank two is the elementary
Nielsen automorphism `x₀ ↦ x₀`, `x₁ ↦ x₁ x₀`. -/
theorem thetaBasis_repr_symm_trans_π₁TreeEquiv_trans_repr :
    ((thetaBasis 𝔸 0).repr.symm.trans
        (π₁TreeEquiv 𝔸 true (parallelTree 0) (parallelTree 1))).trans (thetaBasis 𝔸 1).repr =
      TauCeti.FreeGroup.nielsenMul 1 0 (by decide) 1 := by
  -- Evaluate the change of tree on the basis by the formula for parallel edges: the general
  -- `π₁TreeEquiv_edge` leaves tree paths that `simp` cannot evaluate.
  have e₀ : π₁TreeEquiv 𝔸 true (parallelTree 0) (parallelTree 1) (thetaBasis 𝔸 0 0) =
      thetaBasis 𝔸 1 0 := by
    simp [π₁TreeEquiv_parallelTree_edge_true, -π₁TreeEquiv_edge]
  have e₁ : π₁TreeEquiv 𝔸 true (parallelTree 0) (parallelTree 1) (thetaBasis 𝔸 0 1) =
      thetaBasis 𝔸 1 1 * thetaBasis 𝔸 1 0 := by
    simp [π₁TreeEquiv_parallelTree_edge_true, -π₁TreeEquiv_edge]
  refine MulEquiv.toMonoidHom_injective (FreeGroup.ext_hom _ _ (Fin.forall_fin_two.2 ⟨?_, ?_⟩))
  · simp only [MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, FreeGroupBasis.repr_symm_apply_of,
      e₀, FreeGroupBasis.repr_apply_coe]
    exact (TauCeti.FreeGroup.nielsenMul_of_ne _ _ _ _ _ (by decide)).symm
  · simp only [MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, FreeGroupBasis.repr_symm_apply_of,
      e₁, map_mul, FreeGroupBasis.repr_apply_coe, TauCeti.FreeGroup.nielsenMul_of_left, zpow_one]

end theta

end TauCeti.GraphOfGroups
