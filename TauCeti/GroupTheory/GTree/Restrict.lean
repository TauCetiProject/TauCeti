/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.Combinatorics.Graph.Serre.Induce

/-!
# Restricting a tree with a group action

A `G`-tree restricts along a homomorphism `H →* G` to an `H`-tree on the same tree
(`GTree.comap`), and to a nonempty convex `G`-invariant set of vertices, with the darts joining
them (`GTree.subtree`, on the subgraph induced on the set, which is a tree by
`SerreGraph.IsTree.induce`). Together they give the action of a subgroup on an invariant subtree,
the setting of induced splittings.

Stabilizers for the restriction along `f : H →* G` are preimages under `f`, and an element of `H`
is elliptic exactly when its image is. Stabilizers and distances in an invariant subtree are those
of the tree.

## Main declarations

* `TauCeti.GTree.comap`: the restriction of a `G`-tree along a homomorphism `H →* G`.
* `TauCeti.GTree.subtree`: the restriction of a `G`-tree to a nonempty convex invariant set of
  vertices.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.8.
* J.-P. Serre, *Trees*, Chapter I, §5.5.
-/

public section

universe u v w w'

namespace TauCeti

open _root_.MulAction
open scoped Pointwise

namespace GTree

variable {G : Type w} [Group G] {H : Type w'} [Group H] (T : GTree.{u, v} G)

/-- The restriction of a `G`-tree along a homomorphism `H →* G`: the same tree, on which `H`
acts through `G`. -/
@[expose] def comap (f : H →* G) : GTree.{u, v} H where
  toSerreGraph := T.toSerreGraph
  isTree := T.isTree
  action := T.action.comp f
  action_smul_ne_rev h e := T.action_smul_ne_rev (f h) e

@[simp] theorem comap_toSerreGraph (f : H →* G) : (T.comap f).toSerreGraph = T.toSerreGraph :=
  (rfl)

/-! A vertex or dart of `T.comap f` is one of `T`: `comap` keeps the graph of `T`
(`comap_toSerreGraph`), so `(T.comap f).V` and `(T.comap f).E` are `T.V` and `T.E` by definition.
In the statements below, `show` gives a vertex or dart of `T.comap f` the type `T.V` or `T.E`, on
which `G` acts. -/

/-- An element of `H` acts on the restricted tree through its image in `G`. -/
@[simp] theorem comap_smul_vertex (f : H →* G) (h : H) (v : (T.comap f).V) :
    h • v = f h • (show T.V from v) := (rfl)

/-- An element of `H` acts on the darts of the restricted tree through its image in `G`. -/
@[simp] theorem comap_smul_dart (f : H →* G) (h : H) (e : (T.comap f).E) :
    h • e = f h • (show T.E from e) := (rfl)

/-- The stabilizer of a vertex for the restricted action is the preimage of its stabilizer. -/
@[simp] theorem stabilizer_comap_vertex (f : H →* G) (v : (T.comap f).V) :
    stabilizer H v = (stabilizer G (show T.V from v)).comap f := by
  ext h
  rw [Subgroup.mem_comap, mem_stabilizer_iff, mem_stabilizer_iff, comap_smul_vertex]
  -- Both sides say `f h • v = v`, with `v` read in `(T.comap f).V` and in `T.V`.
  exact Iff.rfl

/-- The stabilizer of a dart for the restricted action is the preimage of its stabilizer. -/
@[simp] theorem stabilizer_comap_dart (f : H →* G) (e : (T.comap f).E) :
    stabilizer H e = (stabilizer G (show T.E from e)).comap f := by
  ext h
  rw [Subgroup.mem_comap, mem_stabilizer_iff, mem_stabilizer_iff, comap_smul_dart]
  -- Both sides say `f h • e = e`, with `e` read in `(T.comap f).E` and in `T.E`.
  exact Iff.rfl

/-- An element acts elliptically on the restricted tree exactly when its image does on `T`. -/
@[simp] theorem isElliptic_comap_iff (f : H →* G) (h : H) :
    (T.comap f).IsElliptic h ↔ T.IsElliptic (f h) := by
  simp only [isElliptic_iff, comap_smul_vertex]
  -- Both sides say that `f h` fixes a vertex, ranging over `(T.comap f).V` and over `T.V`.
  exact Iff.rfl

variable (C : Set T.V)

/-- The automorphism of the subgraph induced on an invariant set of vertices given by an element
of the group. -/
def induceAut (hinv : ∀ g : G, ∀ v ∈ C, g • v ∈ C) (g : G) :
    (T.toSerreGraph.induce C).Aut where
  equivV :=
    { toFun v := ⟨g • v.val, hinv g v.val v.property⟩
      invFun v := ⟨g⁻¹ • v.val, hinv g⁻¹ v.val v.property⟩
      left_inv v := Subtype.ext (inv_smul_smul g v.val)
      right_inv v := Subtype.ext (smul_inv_smul g v.val) }
  equivE :=
    { toFun e := ⟨g • e.val, smul_mem_inducedDarts (hinv g) e.property⟩
      invFun e := ⟨g⁻¹ • e.val, smul_mem_inducedDarts (hinv g⁻¹) e.property⟩
      left_inv e := Subtype.ext (inv_smul_smul g e.val)
      right_inv e := Subtype.ext (smul_inv_smul g e.val) }
  map_src e := Subtype.ext (T.src_smul g e.val)
  map_rev e := Subtype.ext (T.rev_smul g e.val).symm

variable {C} in
/-- The automorphism given by `g` moves a vertex `v` of the induced subgraph to `g • v`. -/
@[simp] theorem induceAut_equivV_apply_val (hinv : ∀ g : G, ∀ v ∈ C, g • v ∈ C) (g : G)
    (v : (T.toSerreGraph.induce C).V) :
    ((T.induceAut C hinv g).equivV v).val = g • (Subtype.val v : T.V) := (rfl)

variable {C} in
/-- The automorphism given by `g` moves a dart `e` of the induced subgraph to `g • e`. -/
@[simp] theorem induceAut_equivE_apply_val (hinv : ∀ g : G, ∀ v ∈ C, g • v ∈ C) (g : G)
    (e : (T.toSerreGraph.induce C).E) :
    ((T.induceAut C hinv g).equivE e).val = g • (Subtype.val e : T.E) := (rfl)

/-- The restriction of a `G`-tree to a nonempty convex invariant set of vertices: the subtree
induced on the set, with the restricted action. -/
@[expose] def subtree (hC : T.IsConvex C) (hne : C.Nonempty) (hinv : ∀ g : G, ∀ v ∈ C, g • v ∈ C) :
    GTree.{u, v} G where
  toSerreGraph := T.toSerreGraph.induce C
  isTree := T.isTree.induce hC hne
  action :=
    { toFun := T.induceAut C hinv
      map_one' := SerreGraph.Iso.ext (fun _ => Subtype.ext (by simp))
        fun _ => Subtype.ext (by simp)
      map_mul' g h := SerreGraph.Iso.ext (fun _ => Subtype.ext (by simp [mul_smul]))
        fun _ => Subtype.ext (by simp [mul_smul]) }
  action_smul_ne_rev g e h := T.smul_ne_rev g e.val (by simpa using congrArg Subtype.val h)

variable {C} (hC : T.IsConvex C) (hne : C.Nonempty) (hinv : ∀ g : G, ∀ v ∈ C, g • v ∈ C)

/-- The underlying graph of an invariant subtree is the subgraph induced on its vertices. -/
@[simp] theorem subtree_toSerreGraph :
    (T.subtree C hC hne hinv).toSerreGraph = T.toSerreGraph.induce C := (rfl)

@[simp] theorem subtree_smul_vertex_val (g : G) (v : (T.subtree C hC hne hinv).V) :
    Subtype.val (g • v) = g • (Subtype.val v : T.V) :=
  T.induceAut_equivV_apply_val hinv g v

@[simp] theorem subtree_smul_dart_val (g : G) (e : (T.subtree C hC hne hinv).E) :
    Subtype.val (g • e) = g • (Subtype.val e : T.E) :=
  T.induceAut_equivE_apply_val hinv g e

/-- The stabilizer of a vertex of an invariant subtree is its stabilizer in the tree. -/
@[simp] theorem stabilizer_subtree_vertex (v : (T.subtree C hC hne hinv).V) :
    stabilizer G v = stabilizer G (Subtype.val v : T.V) := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, ← subtree_smul_vertex_val]
  exact Subtype.val_injective.eq_iff.symm

/-- The stabilizer of a dart of an invariant subtree is its stabilizer in the tree. -/
@[simp] theorem stabilizer_subtree_dart (e : (T.subtree C hC hne hinv).E) :
    stabilizer G e = stabilizer G (Subtype.val e : T.E) := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, ← subtree_smul_dart_val]
  exact Subtype.val_injective.eq_iff.symm

/-- The distance in an invariant subtree is the distance in the tree. -/
@[simp] theorem dist_subtree (a b : (T.subtree C hC hne hinv).V) :
    (T.subtree C hC hne hinv).dist a b = T.dist (Subtype.val a) (Subtype.val b) :=
  hC.dist_induce a b

end GTree

end TauCeti
