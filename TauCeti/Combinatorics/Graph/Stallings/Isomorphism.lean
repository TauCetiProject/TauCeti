/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Morphism

/-!
# Isomorphisms of based labelled graphs

An isomorphism bijects vertices and darts, preserving incidence, reversal, the base vertex
and labels. These are the comparisons in the uniqueness statement for subgroup graphs;
in particular, distinct parallel darts and the two directions of a loop are retained.
-/

public section

namespace TauCeti.StallingsGraph

variable {α : Type*} {R S T : StallingsGraph α}

/-- An isomorphism of based labelled Serre graphs. -/
structure Iso (S T : StallingsGraph α) where
  /-- The equivalence of vertices. -/
  vertexEquiv : S.graph.V ≃ T.graph.V
  /-- The equivalence of darts. -/
  dartEquiv : S.graph.E ≃ T.graph.E
  /-- Initial vertices are preserved. -/
  map_src : ∀ e, vertexEquiv (S.graph.src e) = T.graph.src (dartEquiv e)
  /-- Reversal is preserved. -/
  map_rev : ∀ e, dartEquiv (S.graph.rev e) = T.graph.rev (dartEquiv e)
  /-- The base vertex is preserved. -/
  map_base : vertexEquiv S.base = T.base
  /-- Labels are preserved. -/
  map_label : ∀ e, T.label (dartEquiv e) = S.label e

attribute [simp] Iso.map_src Iso.map_rev Iso.map_base Iso.map_label

namespace Iso

/-- Isomorphisms are determined by their vertex and dart equivalences. -/
@[ext] theorem ext {f g : Iso S T} (hV : f.vertexEquiv = g.vertexEquiv)
    (hE : f.dartEquiv = g.dartEquiv) : f = g := by
  cases f
  cases g
  cases hV
  cases hE
  rfl

/-- The underlying based label-preserving morphism. -/
def toHom (f : Iso S T) : S.Hom T where
  graphHom := {
    mapV := f.vertexEquiv
    mapE := f.dartEquiv
    map_src := fun e => (f.map_src e).symm
    map_rev := f.map_rev }
  map_base := f.map_base
  map_label := f.map_label

@[simp] theorem map_tgt (f : Iso S T) (e : S.graph.E) :
    f.vertexEquiv (S.graph.tgt e) = T.graph.tgt (f.dartEquiv e) :=
  (f.toHom.graphHom.map_tgt S.graph e).symm

@[simp] theorem toHom_mapV (f : Iso S T) (v : S.graph.V) :
    f.toHom.graphHom.mapV v = f.vertexEquiv v := (rfl)

@[simp] theorem toHom_mapE (f : Iso S T) (e : S.graph.E) :
    f.toHom.graphHom.mapE e = f.dartEquiv e := (rfl)

/-- The underlying morphism determines an isomorphism. -/
theorem toHom_injective : Function.Injective (toHom (S := S) (T := T)) := by
  intro f g h
  apply ext
  · exact Equiv.ext fun v => congrArg (fun k : S.Hom T => k.graphHom.mapV v) h
  · exact Equiv.ext fun e => congrArg (fun k : S.Hom T => k.graphHom.mapE e) h

/-- The identity isomorphism. -/
def refl (S : StallingsGraph α) : Iso S S where
  vertexEquiv := Equiv.refl _
  dartEquiv := Equiv.refl _
  map_src := fun _ => rfl
  map_rev := fun _ => rfl
  map_base := rfl
  map_label := fun _ => rfl

/-- The inverse isomorphism. -/
def symm (f : Iso S T) : Iso T S where
  vertexEquiv := f.vertexEquiv.symm
  dartEquiv := f.dartEquiv.symm
  map_src := fun e => by
    apply f.vertexEquiv.injective
    simp only [Equiv.apply_symm_apply]
    rw [f.map_src, Equiv.apply_symm_apply]
  map_rev := fun e => by
    apply f.dartEquiv.injective
    simp only [Equiv.apply_symm_apply]
    rw [f.map_rev, Equiv.apply_symm_apply]
  map_base := f.vertexEquiv.symm_apply_eq.mpr f.map_base.symm
  map_label := fun e => by rw [← f.map_label]; simp

/-- Composition, first the left isomorphism and then the right one. -/
def trans (f : Iso R S) (g : Iso S T) : Iso R T where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  dartEquiv := f.dartEquiv.trans g.dartEquiv
  map_src := fun e => (congrArg g.vertexEquiv (f.map_src e)).trans (g.map_src _)
  map_rev := fun e => (congrArg g.dartEquiv (f.map_rev e)).trans (g.map_rev _)
  map_base := (congrArg g.vertexEquiv f.map_base).trans g.map_base
  map_label := fun e => (g.map_label _).trans (f.map_label e)

@[simp] theorem refl_vertexEquiv (S : StallingsGraph α) :
    (refl S).vertexEquiv = Equiv.refl _ := (rfl)

@[simp] theorem refl_dartEquiv (S : StallingsGraph α) :
    (refl S).dartEquiv = Equiv.refl _ := (rfl)

@[simp] theorem refl_toHom (S : StallingsGraph α) : (refl S).toHom = Hom.id S := by
  apply Hom.ext
  rw [Hom.id_graphHom]
  apply SerreGraph.Hom.ext <;> simp [toHom, refl]

@[simp] theorem symm_vertexEquiv (f : Iso S T) :
    f.symm.vertexEquiv = f.vertexEquiv.symm := (rfl)

@[simp] theorem symm_dartEquiv (f : Iso S T) :
    f.symm.dartEquiv = f.dartEquiv.symm := (rfl)

@[simp] theorem trans_vertexEquiv (f : Iso R S) (g : Iso S T) :
    (f.trans g).vertexEquiv = f.vertexEquiv.trans g.vertexEquiv := (rfl)

@[simp] theorem trans_dartEquiv (f : Iso R S) (g : Iso S T) :
    (f.trans g).dartEquiv = f.dartEquiv.trans g.dartEquiv := (rfl)

@[simp] theorem trans_toHom (f : Iso R S) (g : Iso S T) :
    (f.trans g).toHom = g.toHom.comp f.toHom := by
  apply Hom.ext
  rw [Hom.comp_graphHom]
  apply SerreGraph.Hom.ext <;> funext x <;> simp [toHom, trans]

@[simp] theorem refl_symm (S : StallingsGraph α) : (refl S).symm = refl S := by
  ext <;> rfl

@[simp] theorem symm_trans (f : Iso R S) (g : Iso S T) :
    (f.trans g).symm = g.symm.trans f.symm := by
  ext <;> rfl

@[simp] theorem symm_symm (f : Iso S T) : f.symm.symm = f := by
  apply ext <;> rfl

@[simp] theorem self_trans_symm (f : Iso S T) : f.trans f.symm = refl S := by
  ext <;> simp

@[simp] theorem symm_trans_self (f : Iso S T) : f.symm.trans f = refl T := by
  ext <;> simp

@[simp] theorem toHom_comp_symm_toHom (f : Iso S T) :
    f.toHom.comp f.symm.toHom = Hom.id T := by
  simpa only [trans_toHom, refl_toHom] using congrArg toHom f.symm_trans_self

@[simp] theorem symm_toHom_comp_toHom (f : Iso S T) :
    f.symm.toHom.comp f.toHom = Hom.id S := by
  simpa only [trans_toHom, refl_toHom] using congrArg toHom f.self_trans_symm

@[simp] theorem refl_trans (f : Iso S T) : (refl S).trans f = f := by
  ext <;> simp

@[simp] theorem trans_refl (f : Iso S T) : f.trans (refl T) = f := by
  ext <;> simp

/-- Composition of labelled isomorphisms is associative. -/
theorem trans_assoc {U : StallingsGraph α} (f : Iso R S) (g : Iso S T) (h : Iso T U) :
    (f.trans g).trans h = f.trans (g.trans h) := by
  ext <;> rfl

/-- Isomorphic based labelled graphs accept the same subgroup. -/
theorem subgroup_eq (f : Iso S T) : S.subgroup S.base = T.subgroup T.base :=
  le_antisymm f.toHom.subgroup_le f.symm.toHom.subgroup_le

/-- Between a graph reachable from its base and a folded graph there is at most one
based labelled isomorphism. -/
theorem eq_of_isFolded_of_reachable (hT : T.IsFolded)
    (hS : ∀ v : S.graph.V, Nonempty (S.graph.Path S.base v)) (f g : Iso S T) : f = g :=
  toHom_injective (Hom.eq_of_isFolded_of_reachable hT hS f.toHom g.toHom)

end Iso

/-- A morphism bijective on vertices and darts is an isomorphism. -/
noncomputable def Hom.toIso (f : S.Hom T)
    (hV : Function.Bijective f.graphHom.mapV) (hE : Function.Bijective f.graphHom.mapE) :
    Iso S T where
  vertexEquiv := Equiv.ofBijective _ hV
  dartEquiv := Equiv.ofBijective _ hE
  map_src := fun e => (f.graphHom.map_src e).symm
  map_rev := f.graphHom.map_rev
  map_base := f.map_base
  map_label := f.map_label

@[simp] theorem Hom.toIso_vertexEquiv_apply (f : S.Hom T)
    (hV : Function.Bijective f.graphHom.mapV) (hE : Function.Bijective f.graphHom.mapE)
    (v : S.graph.V) : (f.toIso hV hE).vertexEquiv v = f.graphHom.mapV v := (rfl)

@[simp] theorem Hom.toIso_dartEquiv_apply (f : S.Hom T)
    (hV : Function.Bijective f.graphHom.mapV) (hE : Function.Bijective f.graphHom.mapE)
    (e : S.graph.E) : (f.toIso hV hE).dartEquiv e = f.graphHom.mapE e := (rfl)

@[simp] theorem Hom.toIso_toHom (f : S.Hom T)
    (hV : Function.Bijective f.graphHom.mapV) (hE : Function.Bijective f.graphHom.mapE) :
    (f.toIso hV hE).toHom = f := (rfl)

end TauCeti.StallingsGraph
