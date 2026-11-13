/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Folded
public import TauCeti.Combinatorics.Graph.Stallings.Isomorphism

/-!
# Forgetting the base vertex of a labelled graph

Conjugating a subgroup of a free group moves the base vertex of a labelled graph accepting it.
This file provides the two operations needed to compare labelled graphs up to such moves:

* `StallingsGraph.withBase`: the same labelled graph with another base vertex;
* `StallingsGraph.UnbasedIso`: isomorphisms of labelled graphs that need not preserve the base
  vertex. Such an isomorphism identifies the subgroup accepted at each vertex with the subgroup
  accepted at its image (`StallingsGraph.UnbasedIso.subgroup_eq`).

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*, Section 7.
-/

public section

namespace TauCeti.StallingsGraph

variable {α : Type*} {R S T : StallingsGraph α}

/-- The same labelled graph based at the vertex `v`. The underlying graph computes to the
original one, so that paths of the two graphs are the same. -/
@[expose] def withBase (S : StallingsGraph α) (v : S.graph.V) : StallingsGraph α where
  graph := S.graph
  base := v
  label := S.label
  label_rev := S.label_rev

@[simp] theorem withBase_graph (S : StallingsGraph α) (v : S.graph.V) :
    (S.withBase v).graph = S.graph := rfl

@[simp] theorem withBase_base (S : StallingsGraph α) (v : S.graph.V) :
    (S.withBase v).base = v := rfl

@[simp] theorem withBase_label (S : StallingsGraph α) (v : S.graph.V) (e : S.graph.E) :
    (S.withBase v).label e = S.label e := rfl

@[simp] theorem withBase_base_self (S : StallingsGraph α) : S.withBase S.base = S := rfl

/-- Moving the base vertex twice is moving it once, to the second vertex. -/
@[simp] theorem withBase_withBase (S : StallingsGraph α) (v w : S.graph.V) :
    (S.withBase v).withBase w = S.withBase w := rfl

instance (S : StallingsGraph α) (v : S.graph.V) [Finite S.graph.V] :
    Finite (S.withBase v).graph.V :=
  inferInstanceAs (Finite S.graph.V)

instance (S : StallingsGraph α) (v : S.graph.V) [Finite S.graph.E] :
    Finite (S.withBase v).graph.E :=
  inferInstanceAs (Finite S.graph.E)

@[simp] theorem word_withBase (S : StallingsGraph α) (v : S.graph.V) {a b : S.graph.V}
    (p : S.graph.Path a b) : (S.withBase v).word p = S.word p := by
  -- As for `read_withBase` below, the word lemmas of `S.withBase v` are applied explicitly.
  induction p with
  | nil => exact ((S.withBase v).word_nil a).trans (S.word_nil a).symm
  | cons p e ih =>
    exact ((S.withBase v).word_cons p e).trans
      ((congrArg (· ++ _) ih).trans (S.word_cons p e).symm)

@[simp] theorem read_withBase (S : StallingsGraph α) (v : S.graph.V) {a b : S.graph.V}
    (p : S.graph.Path a b) : (S.withBase v).read p = S.read p := by
  -- The path is stated in the quiver of `S.graph`, so `simp` does not rewrite with the reading
  -- lemmas of `S.withBase v`; they are applied explicitly.
  induction p with
  | nil => exact ((S.withBase v).read_nil a).trans (S.read_nil a).symm
  | cons p e ih =>
    exact ((S.withBase v).read_cons p e).trans
      ((congrArg (· * _) ih).trans (S.read_cons p e).symm)

/-- Moving the base vertex does not change the subgroup accepted at a given vertex. -/
@[simp] theorem subgroup_withBase (S : StallingsGraph α) (v a : S.graph.V) :
    (S.withBase v).subgroup a = S.subgroup a := by
  ext g
  exact (S.withBase v).mem_subgroup_iff.trans
    ((exists_congr fun p => Eq.congr_left (S.read_withBase v p)).trans S.mem_subgroup_iff.symm)

/-- Foldedness does not depend on the base vertex. -/
@[simp] theorem isFolded_withBase (S : StallingsGraph α) (v : S.graph.V) :
    (S.withBase v).IsFolded ↔ S.IsFolded :=
  (S.withBase v).isFolded_def.trans S.isFolded_def.symm

/-- An isomorphism of labelled Serre graphs, not required to preserve the base vertex. -/
structure UnbasedIso (S T : StallingsGraph α) where
  /-- The equivalence of vertices. -/
  vertexEquiv : S.graph.V ≃ T.graph.V
  /-- The equivalence of darts. -/
  dartEquiv : S.graph.E ≃ T.graph.E
  /-- Initial vertices are preserved. -/
  map_src : ∀ e, vertexEquiv (S.graph.src e) = T.graph.src (dartEquiv e)
  /-- Reversal is preserved. -/
  map_rev : ∀ e, dartEquiv (S.graph.rev e) = T.graph.rev (dartEquiv e)
  /-- Labels are preserved. -/
  map_label : ∀ e, T.label (dartEquiv e) = S.label e

attribute [simp] UnbasedIso.map_src UnbasedIso.map_rev UnbasedIso.map_label

/-- A based isomorphism, with the preservation of the base vertex forgotten. -/
def Iso.toUnbasedIso (f : Iso S T) : UnbasedIso S T where
  vertexEquiv := f.vertexEquiv
  dartEquiv := f.dartEquiv
  map_src := f.map_src
  map_rev := f.map_rev
  map_label := f.map_label

@[simp] theorem Iso.toUnbasedIso_vertexEquiv (f : Iso S T) :
    f.toUnbasedIso.vertexEquiv = f.vertexEquiv := (rfl)

@[simp] theorem Iso.toUnbasedIso_dartEquiv (f : Iso S T) :
    f.toUnbasedIso.dartEquiv = f.dartEquiv := (rfl)

namespace UnbasedIso

/-- Unbased isomorphisms are determined by their vertex and dart equivalences. -/
@[ext] theorem ext {f g : UnbasedIso S T} (hV : f.vertexEquiv = g.vertexEquiv)
    (hE : f.dartEquiv = g.dartEquiv) : f = g := by
  cases f
  cases g
  cases hV
  cases hE
  rfl

@[simp] theorem map_tgt (f : UnbasedIso S T) (e : S.graph.E) :
    f.vertexEquiv (S.graph.tgt e) = T.graph.tgt (f.dartEquiv e) := by
  rw [S.graph.tgt_def, T.graph.tgt_def, f.map_src, f.map_rev]

/-- An unbased isomorphism is a based isomorphism once the base vertices are moved to a vertex
and its image. -/
def toIso (f : UnbasedIso S T) (v : S.graph.V) :
    Iso (S.withBase v) (T.withBase (f.vertexEquiv v)) where
  vertexEquiv := f.vertexEquiv
  dartEquiv := f.dartEquiv
  map_src := f.map_src
  map_rev := f.map_rev
  map_base := rfl
  map_label := f.map_label

@[simp] theorem toIso_vertexEquiv (f : UnbasedIso S T) (v : S.graph.V) :
    (f.toIso v).vertexEquiv = f.vertexEquiv := (rfl)

@[simp] theorem toIso_dartEquiv (f : UnbasedIso S T) (v : S.graph.V) :
    (f.toIso v).dartEquiv = f.dartEquiv := (rfl)

/-- The underlying morphism of Serre graphs. -/
def toGraphHom (f : UnbasedIso S T) : S.graph.Hom T.graph where
  mapV := f.vertexEquiv
  mapE := f.dartEquiv
  map_src := fun e => (f.map_src e).symm
  map_rev := f.map_rev

@[simp] theorem toGraphHom_mapV (f : UnbasedIso S T) (v : S.graph.V) :
    f.toGraphHom.mapV v = f.vertexEquiv v := (rfl)

@[simp] theorem toGraphHom_mapE (f : UnbasedIso S T) (e : S.graph.E) :
    f.toGraphHom.mapE e = f.dartEquiv e := (rfl)

/-- The vertex map of an unbased isomorphism is injective. -/
theorem toGraphHom_mapV_injective (f : UnbasedIso S T) : Function.Injective f.toGraphHom.mapV :=
  f.vertexEquiv.injective

/-- The dart map of an unbased isomorphism is injective. -/
theorem toGraphHom_mapE_injective (f : UnbasedIso S T) : Function.Injective f.toGraphHom.mapE :=
  f.dartEquiv.injective

/-- The identity unbased isomorphism. -/
def refl (S : StallingsGraph α) : UnbasedIso S S where
  vertexEquiv := Equiv.refl _
  dartEquiv := Equiv.refl _
  map_src := fun _ => rfl
  map_rev := fun _ => rfl
  map_label := fun _ => rfl

/-- The inverse unbased isomorphism. -/
def symm (f : UnbasedIso S T) : UnbasedIso T S where
  vertexEquiv := f.vertexEquiv.symm
  dartEquiv := f.dartEquiv.symm
  map_src := fun e => by simp [Equiv.symm_apply_eq]
  map_rev := fun e => by simp [Equiv.symm_apply_eq]
  map_label := fun e => by rw [← f.map_label]; simp

/-- Composition, first the left unbased isomorphism and then the right one. -/
def trans (f : UnbasedIso R S) (g : UnbasedIso S T) : UnbasedIso R T where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  dartEquiv := f.dartEquiv.trans g.dartEquiv
  map_src := fun e => (congrArg g.vertexEquiv (f.map_src e)).trans (g.map_src _)
  map_rev := fun e => (congrArg g.dartEquiv (f.map_rev e)).trans (g.map_rev _)
  map_label := fun e => (g.map_label _).trans (f.map_label e)

@[simp] theorem refl_vertexEquiv (S : StallingsGraph α) :
    (refl S).vertexEquiv = Equiv.refl _ := (rfl)

@[simp] theorem refl_dartEquiv (S : StallingsGraph α) :
    (refl S).dartEquiv = Equiv.refl _ := (rfl)

@[simp] theorem symm_vertexEquiv (f : UnbasedIso S T) :
    f.symm.vertexEquiv = f.vertexEquiv.symm := (rfl)

@[simp] theorem symm_dartEquiv (f : UnbasedIso S T) :
    f.symm.dartEquiv = f.dartEquiv.symm := (rfl)

@[simp] theorem trans_vertexEquiv (f : UnbasedIso R S) (g : UnbasedIso S T) :
    (f.trans g).vertexEquiv = f.vertexEquiv.trans g.vertexEquiv := (rfl)

@[simp] theorem trans_dartEquiv (f : UnbasedIso R S) (g : UnbasedIso S T) :
    (f.trans g).dartEquiv = f.dartEquiv.trans g.dartEquiv := (rfl)

@[simp] theorem refl_symm (S : StallingsGraph α) : (refl S).symm = refl S := by
  ext <;> rfl

@[simp] theorem symm_symm (f : UnbasedIso S T) : f.symm.symm = f := by
  ext <;> rfl

@[simp] theorem symm_trans (f : UnbasedIso R S) (g : UnbasedIso S T) :
    (f.trans g).symm = g.symm.trans f.symm := by
  ext <;> rfl

@[simp] theorem self_trans_symm (f : UnbasedIso S T) : f.trans f.symm = refl S := by
  ext <;> simp

@[simp] theorem symm_trans_self (f : UnbasedIso S T) : f.symm.trans f = refl T := by
  ext <;> simp

@[simp] theorem refl_trans (f : UnbasedIso S T) : (refl S).trans f = f := by
  ext <;> rfl

@[simp] theorem trans_refl (f : UnbasedIso S T) : f.trans (refl T) = f := by
  ext <;> rfl

/-- Composition of unbased isomorphisms is associative. -/
theorem trans_assoc {U : StallingsGraph α} (f : UnbasedIso R S) (g : UnbasedIso S T)
    (h : UnbasedIso T U) : (f.trans g).trans h = f.trans (g.trans h) := by
  ext <;> rfl

/-- Changing the base vertices of the two graphs does not affect an unbased isomorphism. -/
def withBase (f : UnbasedIso S T) (v : S.graph.V) (w : T.graph.V) :
    UnbasedIso (S.withBase v) (T.withBase w) where
  vertexEquiv := f.vertexEquiv
  dartEquiv := f.dartEquiv
  map_src := f.map_src
  map_rev := f.map_rev
  map_label := f.map_label

@[simp] theorem withBase_vertexEquiv (f : UnbasedIso S T) (v : S.graph.V) (w : T.graph.V) :
    (f.withBase v w).vertexEquiv = f.vertexEquiv := (rfl)

@[simp] theorem withBase_dartEquiv (f : UnbasedIso S T) (v : S.graph.V) (w : T.graph.V) :
    (f.withBase v w).dartEquiv = f.dartEquiv := (rfl)

/-- Forgetting the base vertex of the based isomorphism given by an unbased isomorphism returns
the unbased isomorphism, with the base vertices moved. -/
@[simp] theorem toIso_toUnbasedIso (f : UnbasedIso S T) (v : S.graph.V) :
    (f.toIso v).toUnbasedIso = f.withBase v (f.vertexEquiv v) := by
  ext <;> rfl

@[simp] theorem word_mapPath (f : UnbasedIso S T) {a b : S.graph.V} (p : S.graph.Path a b) :
    T.word (f.toGraphHom.toPrefunctor.mapPath p) = S.word p := by
  induction p with
  | nil => simp
  | cons p e ih => simp only [Prefunctor.mapPath_cons, word_cons, ih,
      SerreGraph.Hom.toPrefunctor_map_val, toGraphHom_mapE, map_label]

@[simp] theorem read_mapPath (f : UnbasedIso S T) {a b : S.graph.V} (p : S.graph.Path a b) :
    T.read (f.toGraphHom.toPrefunctor.mapPath p) = S.read p := by
  rw [read_eq_mk_word, read_eq_mk_word, word_mapPath]

private theorem isFolded_of_isFolded (f : UnbasedIso S T) (hT : T.IsFolded) : S.IsFolded :=
  S.isFolded_def.mpr fun e e' hs hl => f.dartEquiv.injective <|
    T.isFolded_def.mp hT _ _ (by rw [← f.map_src, ← f.map_src, hs]) (by simp [hl])

/-- Isomorphic labelled graphs are folded together. -/
theorem isFolded_iff (f : UnbasedIso S T) : S.IsFolded ↔ T.IsFolded :=
  ⟨f.symm.isFolded_of_isFolded, f.isFolded_of_isFolded⟩

/-- An unbased isomorphism identifies the subgroup accepted at a vertex with the subgroup
accepted at its image. -/
theorem subgroup_eq (f : UnbasedIso S T) (v : S.graph.V) :
    S.subgroup v = T.subgroup (f.vertexEquiv v) := by
  simpa using (f.toIso v).subgroup_eq

end UnbasedIso

@[simp] theorem Iso.toUnbasedIso_refl (S : StallingsGraph α) :
    (Iso.refl S).toUnbasedIso = UnbasedIso.refl S := by
  ext <;> simp

@[simp] theorem Iso.toUnbasedIso_symm (f : Iso S T) :
    f.symm.toUnbasedIso = f.toUnbasedIso.symm := by
  ext <;> simp

@[simp] theorem Iso.toUnbasedIso_trans (f : Iso R S) (g : Iso S T) :
    (f.trans g).toUnbasedIso = f.toUnbasedIso.trans g.toUnbasedIso := by
  ext <;> simp

end TauCeti.StallingsGraph
