/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Folded
public import TauCeti.GroupTheory.GraphOfGroups.PathGroup
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# Spanning-tree bases of folded labelled graphs

Reading labels identifies the reduced path group of a folded labelled graph with its
accepted subgroup. A spanning tree and an orientation therefore give a free basis of that
subgroup, indexed by the positive non-tree darts. The basis word for a dart follows the tree
from the chosen vertex to its source, crosses the dart, and returns along the tree.

`StallingsGraph.basisEquiv` gives the explicit isomorphism from the free group on these
darts to the accepted subgroup. Its inverse sends a closed path's reading to the same path
in spanning-tree coordinates. The construction does not require finiteness or the core
condition: any folded graph with a spanning tree has this basis.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  §6, Lemma 6.1 and Corollary 6.8.
* A. Hatcher, *Algebraic Topology*, §1.A, Proposition 1A.2.
-/

public section

namespace TauCeti.StallingsGraph

open SerreGraph

universe u v w

variable {α : Type u} (S : StallingsGraph.{u, v, w} α)

noncomputable section

/-- Read labels on the reduced path group at a vertex. -/
def pathGroupRead (a : S.graph.V) : PathGroup S.graph a →* FreeGroup α :=
  PathGroup.lift (fun e => FreeGroup.mk [S.label e]) (by
    intro e
    simp [S.label_rev, FreeGroup.inv_mk, FreeGroup.invRev])

/-- A closed path may be read before reducing it. -/
@[simp] theorem pathGroupRead_ofPath {a : S.graph.V} (p : S.graph.Path a a) :
    S.pathGroupRead a (PathGroup.ofPath p) = S.read p := by
  rw [pathGroupRead, PathGroup.lift_ofPath, S.read_eq_weight]

/-- Reading a reduced-path group element reads its reduced representative. -/
theorem pathGroupRead_apply {a : S.graph.V} (p : PathGroup S.graph a) :
    S.pathGroupRead a p = S.read p.toPath := by
  rw [pathGroupRead, PathGroup.lift_apply, S.read_eq_weight]

/-- The image of label reading is exactly the accepted subgroup. -/
@[simp] theorem range_pathGroupRead (a : S.graph.V) :
    (S.pathGroupRead a).range = S.subgroup a := by
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    rw [S.pathGroupRead_apply]
    exact S.read_mem_subgroup p.toPath
  · intro hg
    obtain ⟨p, rfl⟩ := S.mem_subgroup_iff.mp hg
    exact ⟨PathGroup.ofPath p, S.pathGroupRead_ofPath p⟩

/-- Foldedness makes label reading injective on the reduced path group. -/
theorem IsFolded.pathGroupRead_injective (hS : S.IsFolded) (a : S.graph.V) :
    Function.Injective (S.pathGroupRead a) := by
  intro p q hpq
  apply PathGroup.ext
  exact hS.path_eq_of_read_eq S p.toPath q.toPath p.isReduced q.isReduced
    (by simpa only [S.pathGroupRead_apply] using hpq)

/-- Reduced closed paths in a folded graph are the elements of its accepted subgroup. -/
def pathGroupEquivSubgroup (hS : S.IsFolded) (a : S.graph.V) :
    PathGroup S.graph a ≃* S.subgroup a :=
  (MonoidHom.ofInjective (hS.pathGroupRead_injective S a)).trans
    (MulEquiv.subgroupCongr (S.range_pathGroupRead a))

@[simp] theorem coe_pathGroupEquivSubgroup_apply (hS : S.IsFolded) {a : S.graph.V}
    (p : PathGroup S.graph a) :
    (S.pathGroupEquivSubgroup hS a p : FreeGroup α) = S.read p.toPath :=
  S.pathGroupRead_apply p

/-- The isomorphism reads any closed path, not just its reduced representative. -/
@[simp] theorem pathGroupEquivSubgroup_ofPath (hS : S.IsFolded) {a : S.graph.V}
    (p : S.graph.Path a a) :
    S.pathGroupEquivSubgroup hS a (PathGroup.ofPath p) =
      ⟨S.read p, S.read_mem_subgroup p⟩ :=
  Subtype.ext (S.pathGroupRead_ofPath p)

variable (T : S.graph.SpanningTree) (a : S.graph.V) {O : Set S.graph.E}

/-- The group word read by the tree loop at `a` through a dart. When the graph is folded,
these words restricted to one dart from each reversal pair outside the tree form a free
basis of the accepted subgroup (see `freeGroupBasis`). -/
def treeLoopWord (e : S.graph.E) : FreeGroup α :=
  S.read (((T.path a (S.graph.src e)).cons (S.graph.dart e)).comp
    (T.path (S.graph.tgt e) a))

/-- A tree-loop word follows the tree to the dart, crosses it, and returns through the tree. -/
theorem treeLoopWord_eq (e : S.graph.E) :
    S.treeLoopWord T a e = S.read (T.path a (S.graph.src e)) *
      FreeGroup.mk [S.label e] * S.read (T.path (S.graph.tgt e) a) := by
  simp [treeLoopWord]

/-- The tree-loop words belong to the accepted subgroup. -/
theorem treeLoopWord_mem_subgroup (e : S.graph.E) :
    S.treeLoopWord T a e ∈ S.subgroup a :=
  S.read_mem_subgroup _

/-- Reading the based tree loop through a dart gives its tree-loop word. -/
@[simp] theorem pathGroupRead_loop (e : S.graph.E) :
    S.pathGroupRead a (T.loop a e) = S.treeLoopWord T a e := by
  rw [SerreGraph.SpanningTree.loop_def, S.pathGroupRead_ofPath]
  rfl

/-- Reversing a dart inverts its tree-loop word. -/
@[simp] theorem treeLoopWord_rev (e : S.graph.E) :
    S.treeLoopWord T a (S.graph.rev e) = (S.treeLoopWord T a e)⁻¹ := by
  simp only [← S.pathGroupRead_loop T a, SerreGraph.SpanningTree.loop_rev, map_inv]

/-- Tree darts contribute the trivial word in the accepted subgroup. -/
@[simp] theorem treeLoopWord_eq_one {e : S.graph.E} (he : e ∈ T.darts) :
    S.treeLoopWord T a e = 1 := by
  rw [← S.pathGroupRead_loop T a, T.loop_eq_one a he, map_one]

/-- The positive non-tree loops freely generate the accepted subgroup of a folded graph. -/
def basisEquiv (hS : S.IsFolded) (hO : S.graph.IsOrientation O) :
    FreeGroup ↥(O \ T.darts) ≃* S.subgroup a :=
  (T.pathGroupEquivFreeGroup a hO).symm.trans
    (S.pathGroupEquivSubgroup hS a)

/-- Each free generator maps to the label of its tree loop. -/
@[simp] theorem basisEquiv_of (hS : S.IsFolded) (hO : S.graph.IsOrientation O)
    (e : ↥(O \ T.darts)) :
    S.basisEquiv T a hS hO (FreeGroup.of e) =
      ⟨S.treeLoopWord T a e.1, S.treeLoopWord_mem_subgroup T a e.1⟩ := by
  apply Subtype.ext
  change S.pathGroupRead a ((T.pathGroupEquivFreeGroup a hO).symm (FreeGroup.of e)) = _
  rw [T.pathGroupEquivFreeGroup_symm_of, S.pathGroupRead_loop]

/-- The inverse basis map reads a closed path in spanning-tree coordinates, recording its
non-tree darts with their orientation signs. -/
@[simp] theorem basisEquiv_symm_read (hS : S.IsFolded) (hO : S.graph.IsOrientation O)
    (p : S.graph.Path a a) :
    (S.basisEquiv T a hS hO).symm ⟨S.read p, S.read_mem_subgroup p⟩ =
      T.pathGroupEquivFreeGroup a hO (PathGroup.ofPath p) := by
  apply (S.basisEquiv T a hS hO).injective
  simp [basisEquiv]

/-- The embedding into the ambient free group is the lift of the tree-loop words. -/
theorem subtype_comp_basisEquiv (hS : S.IsFolded) (hO : S.graph.IsOrientation O) :
    (S.subgroup a).subtype.comp (S.basisEquiv T a hS hO).toMonoidHom =
      FreeGroup.lift (fun e : ↥(O \ T.darts) => S.treeLoopWord T a e.1) := by
  ext e
  simp

/-- The tree-loop words freely generate a subgroup of the ambient free group. -/
theorem lift_treeLoopWord_injective (hS : S.IsFolded) (hO : S.graph.IsOrientation O) :
    Function.Injective (FreeGroup.lift (fun e : ↥(O \ T.darts) => S.treeLoopWord T a e.1)) := by
  rw [← S.subtype_comp_basisEquiv T a hS hO]
  exact Subtype.val_injective.comp (S.basisEquiv T a hS hO).injective

/-- The image of the free group on the tree-loop words is exactly the accepted subgroup. -/
@[simp] theorem range_lift_treeLoopWord (hS : S.IsFolded) (hO : S.graph.IsOrientation O) :
    (FreeGroup.lift (fun e : ↥(O \ T.darts) => S.treeLoopWord T a e.1)).range =
      S.subgroup a := by
  rw [← S.subtype_comp_basisEquiv T a hS hO, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (S.basisEquiv T a hS hO).surjective,
    Subgroup.map_top, Subgroup.range_subtype]

/-- A free group basis of the accepted subgroup, indexed by the positive non-tree darts. -/
def freeGroupBasis (hS : S.IsFolded) (hO : S.graph.IsOrientation O) :
    FreeGroupBasis ↥(O \ T.darts) (S.subgroup a) :=
  .ofRepr (S.basisEquiv T a hS hO).symm

/-- The basis elements are precisely the tree-loop words. -/
@[simp] theorem freeGroupBasis_apply (hS : S.IsFolded) (hO : S.graph.IsOrientation O)
    (e : ↥(O \ T.darts)) :
    S.freeGroupBasis T a hS hO e =
      ⟨S.treeLoopWord T a e.1, S.treeLoopWord_mem_subgroup T a e.1⟩ := by
  exact S.basisEquiv_of T a hS hO e

end
end TauCeti.StallingsGraph
