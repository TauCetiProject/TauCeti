/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Line
public import TauCeti.GroupTheory.GTree.Refinement

/-!
# Equivariant graph morphisms of trees and parallel edges

An equivariant *graph morphism* between two `G`-trees (`GTree.Hom`) sends vertices to vertices
and darts to darts, compatibly with sources, reversal and the action: it sends every edge onto an
edge. It is determined by its map of vertices, which is a geodesic morphism of `G`-trees and is
surjective when the target is minimal.

Let `φ : S → T` be such a morphism. A vertex `x` of `S` is *unfolded* (`GTree.Hom.IsUnfoldedAt`)
when exactly two darts start at `x` and `φ` sends them to distinct darts: `S` looks at `x` like
a subdivision point of an edge on which `φ` is injective. Two edges of `S` are *parallel* when
one is reached from the other through unfolded vertices, and `GTree.Hom.ParallelClass` is the set
of classes of darts under parallelism, reversal and the action of `G`. A tree with finitely many
orbits of darts has finitely many parallel classes, and when every vertex is unfolded, as for the
identity of the line, there is at most one.

Parallel classes are meant for trees dual to invariant patterns of tracks in a two-complex,
where the two darts at an unfolded vertex play the role of the two boundary tracks of an
untwisted band in the sense of Dunwoody, so that each parallel class becomes a union of orbits of
classes of parallel tracks. Dunwoody bounds the number of the latter, and Guirardel and Levitt use
this bound to show that a sequence of refinements of trees is eventually dominated by one tree.

## Main definitions

* `TauCeti.GTree.Hom`: equivariant graph morphisms of `G`-trees.
* `TauCeti.GTree.Hom.IsUnfoldedAt`: exactly two darts start at the vertex, with distinct images.
* `TauCeti.GTree.Hom.ParallelClass`: orbits of classes of parallel edges.

## Main statements

* `TauCeti.GTree.Hom.isGeodesicMorphism`: the vertex map identifies the ends of no dart.
* `TauCeti.GTree.Hom.mapV_surjective_of_isMinimal`: surjectivity onto a minimal tree.
* `TauCeti.GTree.Hom.finite_parallelClass`,
  `TauCeti.GTree.Hom.subsingleton_parallelClass_of_forall_isUnfoldedAt`: counting classes.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.4 and
  the proof of Proposition 2.24.
* M. J. Dunwoody, *The accessibility of finitely presented groups*, Invent. Math. 81 (1985),
  §2 (bands and parallel tracks).
-/

public section

universe u v u' v' w

namespace TauCeti

open SerreGraph _root_.MulAction

namespace GTree

variable {G : Type w} [Group G] {S : GTree.{u, v} G} {T : GTree.{u', v'} G}

variable (S T) in
/-- An equivariant graph morphism of `G`-trees: a morphism of the underlying Serre graphs whose
map of vertices commutes with the actions. It sends every edge onto an edge, and its map of darts
commutes with the actions as well (`GTree.Hom.map_smul_dart`). -/
structure Hom extends SerreGraph.Hom S.toSerreGraph T.toSerreGraph where
  /-- The map of vertices is equivariant. -/
  map_smul_vertex : ∀ (g : G) (x : S.V), mapV (g • x) = g • mapV x

namespace Hom

attribute [simp] map_smul_vertex

/-- An equivariant graph morphism of `G`-trees is determined by its map of vertices. -/
@[ext] theorem ext {φ ψ : S.Hom T} (h : ∀ x, φ.mapV x = ψ.mapV x) : φ = ψ := by
  -- A dart of the tree `T` is determined by its ends.
  have hE (e : S.E) : φ.mapE e = ψ.mapE e :=
    T.isAcyclic.eq_of_src_eq_of_tgt_eq (by simp [h]) (by simp [h])
  obtain ⟨φ, _⟩ := φ
  obtain ⟨ψ, _⟩ := ψ
  obtain rfl : φ = ψ := SerreGraph.Hom.ext _ (funext h) (funext hE)
  rfl

variable (T) in
/-- The identity of a `G`-tree, as an equivariant graph morphism. -/
protected def id : T.Hom T where
  toHom := SerreGraph.Hom.id T.toSerreGraph
  map_smul_vertex _ _ := by simp

variable (T) in
/-- The underlying morphism of Serre graphs of the identity is the identity. -/
@[simp] theorem id_toHom : (Hom.id T).toHom = SerreGraph.Hom.id T.toSerreGraph := by
  rfl

variable (φ : S.Hom T)

/-- The map of darts of an equivariant graph morphism is equivariant. -/
@[simp] theorem map_smul_dart (g : G) (e : S.E) : φ.mapE (g • e) = g • φ.mapE e :=
  T.isAcyclic.eq_of_src_eq_of_tgt_eq (by simp) (by simp)

/-- The equivariant map of vertices of an equivariant graph morphism. -/
def toMulActionHom : S.V →[G] T.V where
  toFun := φ.mapV
  map_smul' := φ.map_smul_vertex

/-- The equivariant map of vertices is the vertex map. -/
@[simp] theorem toMulActionHom_apply (x : S.V) : φ.toMulActionHom x = φ.mapV x := (rfl)

/-- The map of vertices of an equivariant graph morphism identifies the ends of no dart. -/
theorem isGeodesicMorphism : IsGeodesicMorphism φ.toMulActionHom :=
  isGeodesicMorphism_iff.mpr fun e h => T.isAcyclic.src_ne_tgt (φ.mapE e) (by simpa using h)

/-- An equivariant graph morphism to a minimal `G`-tree is surjective on vertices: its image is
an invariant subtree. -/
theorem mapV_surjective_of_isMinimal (hT : T.IsMinimal) : Function.Surjective φ.mapV := by
  refine Set.range_eq_univ.mp (isMinimal_iff.mp hT _ (Set.range_nonempty _)
    (isConvex_iff.mpr ?_) ?_)
  · -- A reduced path between two image vertices only crosses darts of the image of a path.
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ p hp e he
    obtain ⟨q⟩ := S.nonempty_path a b
    -- The ends are written as those of the image path, the form `Hom.darts_mapPath` rewrites.
    have he' := (T.isAcyclic.darts_sublist (a := φ.toPrefunctor.obj a)
      (b := φ.toPrefunctor.obj b) hp (φ.toPrefunctor.mapPath q)).subset he
    rw [Hom.darts_mapPath] at he'
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp he'
    exact ⟨S.src d, (φ.map_src d).symm⟩
  · rintro g _ ⟨x, rfl⟩
    exact ⟨g • x, φ.map_smul_vertex g x⟩

/-- The vertex `x` is *unfolded* by `φ` when exactly two darts start at `x` and `φ` sends them
to distinct darts. -/
def IsUnfoldedAt (x : S.V) : Prop :=
  ∃ e₁ e₂ : S.E, φ.mapE e₁ ≠ φ.mapE e₂ ∧ ∀ e : S.E, S.src e = x ↔ e = e₁ ∨ e = e₂

/-- Unfold the definition of an unfolded vertex. -/
theorem isUnfoldedAt_iff {x : S.V} : φ.IsUnfoldedAt x ↔
    ∃ e₁ e₂ : S.E, φ.mapE e₁ ≠ φ.mapE e₂ ∧ ∀ e : S.E, S.src e = x ↔ e = e₁ ∨ e = e₂ := Iff.rfl

/-- Unfolded vertices are permuted by the action. -/
theorem isUnfoldedAt_smul_iff (g : G) {x : S.V} : φ.IsUnfoldedAt (g • x) ↔ φ.IsUnfoldedAt x := by
  suffices h : ∀ (g : G) (x : S.V), φ.IsUnfoldedAt x → φ.IsUnfoldedAt (g • x) from
    ⟨fun hx => by simpa using h g⁻¹ _ hx, h g x⟩
  rintro g x ⟨e₁, e₂, hne, he⟩
  exact ⟨g • e₁, g • e₂, by simpa using hne, fun e => by
    simpa [inv_smul_eq_iff] using he (g⁻¹ • e)⟩

/-- An unfolded vertex is the source of no two distinct darts with the same image. -/
theorem IsUnfoldedAt.ne_of_src_eq {x : S.V} (h : φ.IsUnfoldedAt x) {e e' : S.E} (he : S.src e = x)
    (he' : S.src e' = x) (hne : e ≠ e') : φ.mapE e ≠ φ.mapE e' := by
  obtain ⟨e₁, e₂, h₁₂, h⟩ := h
  grind

/-- The relation generating parallelism of darts up to the action: a dart is related to its
translates, to its reverse, and to the other dart starting at its source when the source is
unfolded. -/
def ParallelStep (e e' : S.E) : Prop :=
  (∃ g : G, e' = g • e) ∨ e' = S.rev e ∨ (S.src e = S.src e' ∧ φ.IsUnfoldedAt (S.src e))

/-- Unfold the relation generating parallelism. -/
theorem parallelStep_iff {e e' : S.E} : φ.ParallelStep e e' ↔
    (∃ g : G, e' = g • e) ∨ e' = S.rev e ∨ (S.src e = S.src e' ∧ φ.IsUnfoldedAt (S.src e)) :=
  Iff.rfl

/-- The orbits of classes of parallel edges of `S` with respect to `φ`: the quotient of the darts
by the action, reversal, and passage through unfolded vertices. -/
def ParallelClass : Type v :=
  Quot φ.ParallelStep

/-- The parallel class of a dart. -/
def parallelClass (e : S.E) : φ.ParallelClass :=
  Quot.mk _ e

/-- Two darts have the same parallel class exactly when a chain of translations, reversals and
passages through unfolded vertices joins them. -/
theorem parallelClass_eq_parallelClass_iff {e e' : S.E} :
    φ.parallelClass e = φ.parallelClass e' ↔ Relation.EqvGen φ.ParallelStep e e' :=
  Quot.eq

/-- Every parallel class is the class of a dart. -/
theorem parallelClass_surjective : Function.Surjective φ.parallelClass :=
  Quot.mk_surjective

/-- A dart and its translates have the same parallel class. -/
@[simp] theorem parallelClass_smul (g : G) (e : S.E) :
    φ.parallelClass (g • e) = φ.parallelClass e :=
  (Quot.sound (.inl ⟨g, rfl⟩)).symm

/-- A dart and its reverse have the same parallel class. -/
@[simp] theorem parallelClass_rev (e : S.E) : φ.parallelClass (S.rev e) = φ.parallelClass e :=
  (Quot.sound (.inr (.inl rfl))).symm

/-- The two darts starting at an unfolded vertex have the same parallel class. -/
theorem parallelClass_eq_of_isUnfoldedAt {e e' : S.E} (h : S.src e = S.src e')
    (hx : φ.IsUnfoldedAt (S.src e)) : φ.parallelClass e = φ.parallelClass e' :=
  Quot.sound (.inr (.inr ⟨h, hx⟩))

/-- A tree with finitely many orbits of darts has finitely many parallel classes. -/
theorem finite_parallelClass [Finite (orbitRel.Quotient G S.E)] : Finite φ.ParallelClass := by
  refine Finite.of_surjective (Quotient.lift (s := orbitRel G S.E) φ.parallelClass ?_) fun c => ?_
  · rintro _ e ⟨g, rfl⟩
    exact φ.parallelClass_smul g e
  · obtain ⟨e, rfl⟩ := φ.parallelClass_surjective c
    exact ⟨Quotient.mk _ e, rfl⟩

/-- If every vertex is unfolded, there is at most one parallel class. -/
theorem subsingleton_parallelClass_of_forall_isUnfoldedAt (h : ∀ x : S.V, φ.IsUnfoldedAt x) :
    Subsingleton φ.ParallelClass := by
  -- Darts at the two ends of a path are parallel: darts with a common source are, and a dart is
  -- parallel to its reverse.
  have key {a b : S.V} (p : S.Path a b) {e e' : S.E} (he : S.src e = a) (he' : S.src e' = b) :
      φ.parallelClass e = φ.parallelClass e' := by
    induction p generalizing e' with
    | nil => exact φ.parallelClass_eq_of_isUnfoldedAt (he.trans he'.symm) (h _)
    | cons _ d ih =>
      rw [ih d.property.1, ← φ.parallelClass_rev d.val]
      exact φ.parallelClass_eq_of_isUnfoldedAt (by rw [src_rev, d.property.2, he']) (h _)
  refine ⟨fun c c' => ?_⟩
  obtain ⟨e, rfl⟩ := φ.parallelClass_surjective c
  obtain ⟨e', rfl⟩ := φ.parallelClass_surjective c'
  obtain ⟨p⟩ := S.nonempty_path (S.src e) (S.src e')
  exact key p rfl rfl

/-- The identity of the line is unfolded at every vertex: exactly two darts start at each
vertex, one in each direction. So the identity of the line has at most one parallel class, by
`GTree.Hom.subsingleton_parallelClass_of_forall_isUnfoldedAt`. -/
theorem isUnfoldedAt_id_line (x : line.V) : (Hom.id line).IsUnfoldedAt x := by
  -- The darts from `x` are `(x, true)`, to `x + 1`, and `(x - 1, false)`, back to `x - 1`.
  refine ⟨(lineVertexEquiv x, true), (lineVertexEquiv x - 1, false), ?_,
    fun e => ⟨fun he => ?_, ?_⟩⟩
  · rw [id_toHom, SerreGraph.Hom.id_mapE]
    exact fun h => Bool.noConfusion (congrArg Prod.snd h)
  · have h := (lineVertexEquiv_line_src e).symm.trans (congrArg lineVertexEquiv he)
    rcases e with ⟨n, _ | _⟩
    · exact .inr (Prod.ext (by simp at h ⊢; lia) rfl)
    · exact .inl (Prod.ext (by simpa using h) rfl)
  · rintro (rfl | rfl) <;>
      exact lineVertexEquiv.injective ((lineVertexEquiv_line_src _).trans (by simp))

end Hom

end GTree

end TauCeti
