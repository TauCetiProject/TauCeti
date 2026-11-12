/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.Combinatorics.Graph.Serre.Quotient
public import TauCeti.Combinatorics.Graph.Serre.SpanningTree

/-!
# Liftings of the quotient graph of a group acting on a tree

Let a group `G` act on a tree `T` without inversions, with quotient graph `B = T / G`
(`GTree.quotient`) and projection `q : T → B` (`GTree.quotientMap`). The fibres of `q` are the
`G`-orbits, and `B` is connected.

A lifting (`GTree.Lifting`) consists of a spanning tree of `B`, a lift of every vertex of `B` to
`T`, a lift of every dart of `B` issuing from the lift of its source, and for every dart `y` an
element `twist y` of `G` carrying the lift of the reverse of `y` to the reverse of the lift of
`y`. The elements `twist y` are trivial on the darts of the spanning tree and satisfy
`twist (rev y) = (twist y)⁻¹`. The lift of a dart `y` ends at the translate by `twist y` of the
lift of the target of `y` (`GTree.Lifting.tgt_dart`); in particular the lifts of the darts of the
spanning tree join lifted vertices and are closed under reversal
(`GTree.Lifting.dart_rev_of_mem`), so that they lift the spanning tree. Distinct vertices of `B`
have distinct lifts, and every dart of `T` issuing from a lifted vertex is a translate of a lifted
dart by an element of the stabilizer of that vertex (`GTree.Lifting.exists_smul_dart_eq`).

This is the data of the explicit construction of the quotient graph of groups in
Kapovich–Weidmann–Myasnikov, Remark 2.7: the lifted vertices and tree darts form their lift `T₁`
of a maximal subtree, and the elements `(twist y)⁻¹` are their elements `t_v`. There one dart of
each geometric edge outside the tree is lifted; here both orientations are lifted, the lift of
the second one being the translate by `(twist y)⁻¹` of the reverse of the lift of the first.
Liftings exist for every spanning tree of `B` and every choice of the lift of one vertex
(`GTree.exists_lifting`): the spanning tree is lifted along its tree paths from the prescribed
vertex, and the other darts are lifted with their sources at lifted vertices.

## Main declarations

* `TauCeti.GTree.quotient`, `TauCeti.GTree.quotientMap`: the quotient graph of a `G`-tree and
  the projection onto it.
* `TauCeti.GTree.Lifting`: a lifting of the quotient graph to the tree.
* `TauCeti.GTree.exists_lifting`: liftings exist, with any spanning tree and any base lift.
* `TauCeti.GTree.Lifting.tgt_dart`: the lift of a dart ends at a translate of a lifted vertex.
* `TauCeti.GTree.Lifting.exists_smul_dart_eq`: every dart issuing from a lifted vertex is a
  translate of a lifted dart by an element of the stabilizer of that vertex.

## References

* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, Internat. J. Algebra Comput. 15 (2005), §2, Proposition 2.6 and Remark 2.7.
* J.-P. Serre, *Trees*, Chapter I, §3.1 and §5.4.
-/

public section

universe u v w

namespace TauCeti

open SerreGraph _root_.MulAction

namespace GTree

variable {G : Type w} [Group G] (T : GTree.{u, v} G)

/-- The quotient graph `T / G` of a `G`-tree. -/
abbrev quotient : SerreGraph.{u, v} :=
  T.toSerreGraph.quotient T.action T.smul_ne_rev

/-- The projection of a `G`-tree to its quotient graph. -/
abbrev quotientMap : T.toSerreGraph.Hom T.quotient :=
  T.toSerreGraph.quotientMap T.action T.smul_ne_rev

variable {T}

/-- Two vertices of a `G`-tree have the same image in the quotient graph exactly when they are in
the same orbit. -/
theorem quotientMap_mapV_eq_iff {a b : T.V} :
    T.quotientMap.mapV a = T.quotientMap.mapV b ↔ ∃ g : G, g • a = b :=
  SerreGraph.quotientMap_mapV_eq_iff

/-- Two darts of a `G`-tree have the same image in the quotient graph exactly when they are in
the same orbit. -/
theorem quotientMap_mapE_eq_iff {e f : T.E} :
    T.quotientMap.mapE e = T.quotientMap.mapE f ↔ ∃ g : G, g • e = f :=
  SerreGraph.quotientMap_mapE_eq_iff

/-- A vertex of a `G`-tree and its translates have the same image in the quotient graph. -/
@[simp] theorem quotientMap_mapV_smul (g : G) (a : T.V) :
    T.quotientMap.mapV (g • a) = T.quotientMap.mapV a :=
  SerreGraph.quotientMap_mapV_smul g a

/-- A dart of a `G`-tree and its translates have the same image in the quotient graph. -/
@[simp] theorem quotientMap_mapE_smul (g : G) (e : T.E) :
    T.quotientMap.mapE (g • e) = T.quotientMap.mapE e :=
  SerreGraph.quotientMap_mapE_smul g e

variable (T)

/-- The quotient graph of a `G`-tree is connected. -/
theorem quotient_connected : T.quotient.Connected :=
  SerreGraph.quotient_connected T.isTree.connected

/-- A lifting of the quotient graph `T / G` of a `G`-tree to the tree: a spanning tree of the
quotient, a lift of every vertex, a lift of every dart issuing from the lift of its source, and
for every dart `y` an element `twist y` of `G` mapping the lift of the reverse of `y` to the
reverse of the lift of `y`. The elements `twist y` are trivial on the spanning tree, so that the
lifts of its darts are closed under reversal and join lifted vertices. -/
@[ext] structure Lifting where
  /-- The spanning tree of the quotient graph. -/
  tree : T.quotient.SpanningTree
  /-- The lift of a vertex of the quotient graph. -/
  vertex : T.quotient.V → T.V
  /-- The lift of a dart of the quotient graph. -/
  dart : T.quotient.E → T.E
  /-- The element of the group attached to a dart of the quotient graph. -/
  twist : T.quotient.E → G
  /-- The lift of a vertex lies over it. -/
  quotientMap_vertex : ∀ b, T.quotientMap.mapV (vertex b) = b
  /-- The lift of a dart lies over it. -/
  quotientMap_dart : ∀ y, T.quotientMap.mapE (dart y) = y
  /-- The lift of a dart issues from the lift of its source. -/
  src_dart : ∀ y, T.src (dart y) = vertex (T.quotient.src y)
  /-- The element of a dart maps the lift of its reverse to the reverse of its lift. -/
  twist_smul_dart_rev : ∀ y, twist y • dart (T.quotient.rev y) = T.rev (dart y)
  /-- The element of the reverse dart is the inverse. -/
  twist_rev : ∀ y, twist (T.quotient.rev y) = (twist y)⁻¹
  /-- The elements of the darts of the spanning tree are trivial. -/
  twist_eq_one : ∀ y ∈ tree.darts, twist y = 1

attribute [simp] Lifting.quotientMap_vertex Lifting.quotientMap_dart Lifting.src_dart
  Lifting.twist_rev

/-! ### Existence of liftings -/

variable {T}

/-- A lift of a dart of the quotient graph with a prescribed source in the orbit of its source. -/
private noncomputable def liftDart {a : T.V} {y : T.quotient.E}
    (h : T.quotient.src y = T.quotientMap.mapV a) : T.E :=
  (exists_quotientMap_mapE_eq_of_src_eq h).choose

private theorem src_liftDart {a : T.V} {y : T.quotient.E}
    (h : T.quotient.src y = T.quotientMap.mapV a) : T.src (liftDart h) = a :=
  (exists_quotientMap_mapE_eq_of_src_eq h).choose_spec.1

private theorem quotientMap_liftDart {a : T.V} {y : T.quotient.E}
    (h : T.quotient.src y = T.quotientMap.mapV a) : T.quotientMap.mapE (liftDart h) = y :=
  (exists_quotientMap_mapE_eq_of_src_eq h).choose_spec.2

/-- The end of the lift from `x₀` of a path of the quotient graph issuing from the image of `x₀`,
lifted dart by dart with `liftDart`. The lift of a path extended by a dart is the lift of the
path extended by a lift of that dart. -/
private noncomputable def liftPathEnd (x₀ : T.V) :
    ∀ {b : T.quotient.V}, T.quotient.Path (T.quotientMap.mapV x₀) b →
      {a : T.V // T.quotientMap.mapV a = b}
  | _, .nil => ⟨x₀, rfl⟩
  | _, .cons p f => ⟨T.tgt (liftDart (f.2.1.trans (liftPathEnd x₀ p).2.symm)), by
      rw [← Hom.map_tgt, quotientMap_liftDart, f.2.2]⟩

/-- The lifts of a path and of the path extended by a dart `f` are joined by a lift of `f`. -/
private theorem exists_liftPathEnd_cons (x₀ : T.V) {b c : T.quotient.V}
    (p : T.quotient.Path (T.quotientMap.mapV x₀) b) (f : Quiver.Hom b c) :
    ∃ e : T.E, T.src e = (liftPathEnd x₀ p).1 ∧ T.quotientMap.mapE e = f.1 ∧
      T.tgt e = (liftPathEnd x₀ (p.cons f)).1 :=
  ⟨_, src_liftDart _, quotientMap_liftDart _, rfl⟩

/-- The lift of a spanning tree of the quotient graph: lifts of the vertices, with a prescribed
lift of one vertex, such that the two ends of every tree dart are joined by a lift of that dart.
The lifts are the ends of the lifts of the tree paths from the base vertex. -/
private theorem exists_lift_spanningTree (S : T.quotient.SpanningTree) (x₀ : T.V) :
    ∃ s : T.quotient.V → T.V, (∀ b, T.quotientMap.mapV (s b) = b) ∧
      s (T.quotientMap.mapV x₀) = x₀ ∧ ∀ y ∈ S.darts, ∃ e : T.E,
        T.src e = s (T.quotient.src y) ∧ T.tgt e = s (T.quotient.tgt y) ∧
          T.quotientMap.mapE e = y := by
  refine ⟨fun b => (liftPathEnd x₀ (S.path _ b)).1, fun b => (liftPathEnd x₀ _).2,
    by simp [liftPathEnd], fun y hy => ?_⟩
  rcases S.path_eq_cons_or_path_eq_cons_reverse (T.quotientMap.mapV x₀) (T.quotient.dart y)
    (by rwa [dart_val]) with h | h
  · obtain ⟨e, he₁, he₂, he₃⟩ := exists_liftPathEnd_cons x₀ _ (T.quotient.dart y)
    rw [← h] at he₃
    exact ⟨e, he₁, he₃, by rwa [dart_val] at he₂⟩
  · -- The tree path to the source of `y` passes through its target.
    obtain ⟨e, he₁, he₂, he₃⟩ :=
      exists_liftPathEnd_cons x₀ _ (Quiver.reverse (T.quotient.dart y))
    rw [← h] at he₃
    exact ⟨T.rev e, by rwa [src_rev], by rwa [tgt_rev], by simp [he₂]⟩

open scoped Classical in
/-- A lifting built from lifts `e y` of all darts `y` issuing from the lifts of their sources and
ending at the translates by elements `g y` of the lifts of their targets, with `g` trivial on the
spanning tree: the lift of the chosen dart `GeomEdge.out` of each geometric edge is kept, and the
lift of the other dart is the translate of the reverse of the kept one. -/
private noncomputable def Lifting.ofLifts (S : T.quotient.SpanningTree) (s : T.quotient.V → T.V)
    (e : T.quotient.E → T.E) (g : T.quotient.E → G) (hs : ∀ b, T.quotientMap.mapV (s b) = b)
    (he₁ : ∀ y, T.src (e y) = s (T.quotient.src y)) (he₂ : ∀ y, T.quotientMap.mapE (e y) = y)
    (he₃ : ∀ y, T.tgt (e y) = g y • s (T.quotient.tgt y)) (hg : ∀ y ∈ S.darts, g y = 1) :
    T.Lifting where
  tree := S
  vertex := s
  dart y := if GeomEdge.out T.quotient (T.quotient.toGeomEdge y) = y then e y
    else (g (T.quotient.rev y))⁻¹ • T.rev (e (T.quotient.rev y))
  twist y := if GeomEdge.out T.quotient (T.quotient.toGeomEdge y) = y then g y
    else (g (T.quotient.rev y))⁻¹
  quotientMap_vertex := hs
  quotientMap_dart y := by split_ifs <;> simp [he₂]
  src_dart y := by split_ifs <;> simp [he₁, he₃]
  twist_smul_dart_rev y := by
    rcases GeomEdge.out_toGeomEdge_eq_or_eq_rev T.quotient y with h | h <;>
      simp [h, T.quotient.rev_ne y, (T.quotient.rev_ne y).symm]
  twist_rev y := by
    rcases GeomEdge.out_toGeomEdge_eq_or_eq_rev T.quotient y with h | h <;>
      simp [h, T.quotient.rev_ne y, (T.quotient.rev_ne y).symm]
  twist_eq_one y hy := by split_ifs <;> simp [hg y hy, hg _ (S.rev_mem y hy)]

variable (T)

/-- For every spanning tree of the quotient graph and every vertex `x₀` of the tree there is a
lifting with that spanning tree in which the image of `x₀` lifts to `x₀`. -/
theorem exists_lifting (S : T.quotient.SpanningTree) (x₀ : T.V) :
    ∃ D : T.Lifting, D.tree = S ∧ D.vertex (T.quotientMap.mapV x₀) = x₀ := by
  obtain ⟨s, hs, hs₀, hsS⟩ := exists_lift_spanningTree S x₀
  -- Every dart has a lift issuing from the lift of its source and ending at a translate of the
  -- lift of its target, by the trivial element for the darts of the spanning tree.
  have key (y : T.quotient.E) : ∃ c : T.E × G, T.src c.1 = s (T.quotient.src y) ∧
      T.quotientMap.mapE c.1 = y ∧ T.tgt c.1 = c.2 • s (T.quotient.tgt y) ∧
        (y ∈ S.darts → c.2 = 1) := by
    by_cases hy : y ∈ S.darts
    · obtain ⟨e, he₁, he₂, he₃⟩ := hsS y hy
      exact ⟨(e, 1), he₁, he₃, by rw [he₂, one_smul], fun _ => rfl⟩
    · obtain ⟨e, he₁, he₂⟩ := exists_quotientMap_mapE_eq_of_src_eq (hs (T.quotient.src y)).symm
      obtain ⟨g, hg⟩ : ∃ g : G, g • s (T.quotient.tgt y) = T.tgt e :=
        quotientMap_mapV_eq_iff.mp (by rw [hs, ← Hom.map_tgt, he₂])
      exact ⟨(e, g), he₁, he₂, hg.symm, fun h => absurd h hy⟩
  choose c hc₁ hc₂ hc₃ hc₄ using key
  exact ⟨Lifting.ofLifts S s (fun y => (c y).1) (fun y => (c y).2) hs hc₁ hc₂ hc₃ hc₄, rfl, hs₀⟩

/-- Every `G`-tree has a lifting of its quotient graph. -/
theorem nonempty_lifting : Nonempty T.Lifting :=
  (T.quotient.exists_spanningTree T.quotient_connected).map fun S =>
    (T.exists_lifting S (Classical.arbitrary T.V)).choose

namespace Lifting

variable {T} (D : T.Lifting)

/-- The lift of a dart ends at the translate by its element of the lift of its target. -/
@[simp] theorem tgt_dart (y : T.quotient.E) :
    T.tgt (D.dart y) = D.twist y • D.vertex (T.quotient.tgt y) := by
  simpa using (congrArg T.src (D.twist_smul_dart_rev y)).symm

/-- The lifts of the darts of the spanning tree are closed under reversal. -/
theorem dart_rev_of_mem {y : T.quotient.E} (hy : y ∈ D.tree.darts) :
    D.dart (T.quotient.rev y) = T.rev (D.dart y) := by
  simpa [D.twist_eq_one y hy] using D.twist_smul_dart_rev y

/-- Distinct vertices of the quotient graph have distinct lifts. -/
theorem vertex_injective : Function.Injective D.vertex :=
  Function.LeftInverse.injective D.quotientMap_vertex

/-- Every dart issuing from a lifted vertex is a translate, by an element of the stabilizer of
that vertex, of the lift of its image. -/
theorem exists_smul_dart_eq {b : T.quotient.V} {e : T.E} (he : T.src e = D.vertex b) :
    ∃ g ∈ stabilizer G (D.vertex b), g • D.dart (T.quotientMap.mapE e) = e := by
  obtain ⟨g, hg⟩ := quotientMap_mapE_eq_iff.mp (D.quotientMap_dart (T.quotientMap.mapE e))
  refine ⟨g, mem_stabilizer_iff.mpr ?_, hg⟩
  simpa [he] using congrArg T.src hg

end Lifting

end GTree

end TauCeti
