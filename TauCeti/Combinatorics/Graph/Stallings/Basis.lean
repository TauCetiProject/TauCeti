/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Folded
public import TauCeti.GroupTheory.GraphOfGroups.Rank
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# Spanning-tree bases of folded labelled graphs

Reading labels identifies the reduced path group of a folded labelled graph with its
accepted subgroup. A spanning tree and an orientation therefore give a free basis of that
subgroup, indexed by the positive non-tree darts. The basis word for a dart follows the tree
from the chosen vertex to its source, crosses the dart, and returns along the tree.

`StallingsGraph.basisEquiv` gives the explicit isomorphism from the free group on these
darts to the accepted subgroup. Its inverse reads an accepted element along the graph and
multiplies the signed coordinates of the darts crossed: a positive non-tree dart contributes
its generator, its reverse the inverse generator, and a tree dart nothing. The construction
does not require finiteness or the core condition: any folded graph with a spanning tree has
this basis.

Consequently the accepted subgroup is finitely generated exactly when there are finitely many
positive non-tree darts, its rank is then their number, and it is trivial exactly when there
are none. For a connected graph with finitely many vertices this gives the Euler form of the
rank: the rank plus the number of vertices is the number of positive darts plus one.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  §6, Lemma 6.1 and Corollary 6.8; §8, Lemma 8.2.
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

/-- The reduced closed path representing an accepted element reads that element. -/
@[simp] theorem read_toPath_pathGroupEquivSubgroup_symm (hS : S.IsFolded) {a : S.graph.V}
    (g : S.subgroup a) : S.read ((S.pathGroupEquivSubgroup hS a).symm g).toPath = g := by
  rw [← S.coe_pathGroupEquivSubgroup_apply hS, MulEquiv.apply_symm_apply]

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
  rw [basisEquiv, MulEquiv.trans_apply, S.coe_pathGroupEquivSubgroup_apply,
    ← S.pathGroupRead_apply, T.pathGroupEquivFreeGroup_symm_of, S.pathGroupRead_loop]

/-- The inverse basis map sends the reading of a closed path to the product of the signed
coordinates of its darts: a positive non-tree dart contributes its generator, its reverse the
inverse generator, and tree darts nothing. The path need not be reduced. -/
@[simp] theorem basisEquiv_symm_read (hS : S.IsFolded) (hO : S.graph.IsOrientation O)
    (p : S.graph.Path a a) :
    (S.basisEquiv T a hS hO).symm ⟨S.read p, S.read_mem_subgroup p⟩ =
      p.weight (fun {x y : S.graph.V} (e : x ⟶ y) =>
        GraphOfGroups.π₁Tree.dartWord O T.darts e.1) := by
  rw [← T.pathGroupEquivFreeGroup_ofPath a hO]
  apply (S.basisEquiv T a hS hO).injective
  simp [basisEquiv]

/-- The inverse basis map reads an accepted element along the graph from the chosen vertex,
along its unique reduced closed path, and multiplies the signed coordinates of the darts
crossed. -/
theorem basisEquiv_symm_apply (hS : S.IsFolded) (hO : S.graph.IsOrientation O) (g : S.subgroup a) :
    (S.basisEquiv T a hS hO).symm g =
      ((S.pathGroupEquivSubgroup hS a).symm g).toPath.weight
        (fun {x y : S.graph.V} (e : x ⟶ y) =>
          GraphOfGroups.π₁Tree.dartWord O T.darts e.1) := by
  rw [← T.pathGroupEquivFreeGroup_apply a hO, basisEquiv, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm]

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
@[simp] theorem range_lift_treeLoopWord (hO : S.graph.IsOrientation O) :
    (FreeGroup.lift (fun e : ↥(O \ T.darts) => S.treeLoopWord T a e.1)).range =
      S.subgroup a := by
  have h : FreeGroup.lift (fun e : ↥(O \ T.darts) => S.treeLoopWord T a e.1) =
      (S.pathGroupRead a).comp (T.pathGroupEquivFreeGroup a hO).symm.toMonoidHom := by
    ext e
    simp
  rw [h, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (T.pathGroupEquivFreeGroup a hO).symm.surjective,
    Subgroup.map_top, S.range_pathGroupRead]

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

/-- The accepted subgroup of a folded graph is finitely generated exactly when finitely many
positive darts lie outside a spanning tree. The graph may have infinitely many vertices. -/
theorem fg_subgroup_iff (hS : S.IsFolded) (hO : S.graph.IsOrientation O) :
    Group.FG (S.subgroup a) ↔ Finite ↥(O \ T.darts) :=
  (S.freeGroupBasis T a hS hO).fg_iff_finite

/-- The rank of the accepted subgroup of a folded graph is the number of positive darts
outside a spanning tree. -/
theorem rank_subgroup (hS : S.IsFolded) (hO : S.graph.IsOrientation O) [Group.FG (S.subgroup a)] :
    Group.rank (S.subgroup a) = Nat.card ↥(O \ T.darts) :=
  (S.freeGroupBasis T a hS hO).rank_eq_nat_card

/-- The Euler form of the rank: for a connected folded graph with finitely many vertices
accepting a finitely generated subgroup, the rank of that subgroup plus the number of vertices
is the number of positive darts plus one. -/
theorem rank_subgroup_add_card (hS : S.IsFolded) (hO : S.graph.IsOrientation O)
    (h : S.graph.Connected) [Finite S.graph.V] [Group.FG (S.subgroup a)] :
    Group.rank (S.subgroup a) + Nat.card S.graph.V = Nat.card O + 1 := by
  have : Group.FG (PathGroup S.graph a) := (isMulFG_congr (S.pathGroupEquivSubgroup hS a)).mpr ‹_›
  rw [← Group.rank_congr (S.pathGroupEquivSubgroup hS a), hO.rank_pathGroup_add_card h a]

/-- A folded graph accepts only the identity exactly when its basis is empty: every positive
dart lies in the spanning tree. In particular a graph without darts accepts the trivial
subgroup, of rank zero. -/
theorem subgroup_eq_bot_iff (hS : S.IsFolded) (hO : S.graph.IsOrientation O) :
    S.subgroup a = ⊥ ↔ O ⊆ T.darts := by
  constructor
  · intro h e heO
    by_contra heT
    have hone : S.basisEquiv T a hS hO (FreeGroup.of ⟨e, heO, heT⟩) = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp (h ▸ (S.basisEquiv T a hS hO _).2))
    exact FreeGroup.of_ne_one _ ((S.basisEquiv T a hS hO).map_eq_one_iff.mp hone)
  · intro h
    have : IsEmpty ↥(O \ T.darts) := ⟨fun e => e.2.2 (h e.2.1)⟩
    have := (S.basisEquiv T a hS hO).symm.toEquiv.subsingleton
    exact Subgroup.eq_bot_of_subsingleton _

end
end TauCeti.StallingsGraph
