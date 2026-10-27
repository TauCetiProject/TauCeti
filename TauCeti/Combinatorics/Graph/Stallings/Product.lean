/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Folded

/-!
# Products of labelled graphs

The product of two based labelled Serre graphs pairs darts carrying the same signed letter.
Its closed paths project to closed paths in both factors, so its accepted subgroup lies in
their intersection. Foldedness is preserved by the product.

The construction is the fibre product over the labelled rose used in Stallings' subgroup
intersection method.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*, Section 9.
-/

public section

namespace TauCeti
namespace StallingsGraph

universe u v w x y z t

variable {α : Type u}

/-- The based fibre product of labelled graphs: vertices are pairs and darts are pairs
with identical signed labels. -/
@[expose] def prod (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) : StallingsGraph α where
  graph := {
    V := S.graph.V × T.graph.V
    E := {e : S.graph.E × T.graph.E // S.label e.1 = T.label e.2}
    src := fun e => (S.graph.src e.1.1, T.graph.src e.1.2)
    rev := fun e => ⟨(S.graph.rev e.1.1, T.graph.rev e.1.2), by
      simpa only [S.label_rev, T.label_rev] using congrArg
        (fun l : α × Bool => (l.1, !l.2)) e.2⟩
    rev_rev := by
      intro e
      apply Subtype.ext
      simp
    rev_ne := by
      intro e h
      have hfst : S.graph.rev e.1.1 = e.1.1 :=
        congrArg (fun p : S.graph.E × T.graph.E => p.1) (congrArg Subtype.val h)
      exact S.graph.rev_ne e.1.1 hfst }
  base := (S.base, T.base)
  label := fun e => S.label e.1.1
  label_rev := by
    intro e
    exact S.label_rev e.1.1

@[simp] theorem prod_base (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) : (S.prod T).base = (S.base, T.base) := rfl

@[simp] theorem prod_label (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (e : (S.prod T).graph.E) :
    (S.prod T).label e = S.label e.1.1 := rfl

@[simp] theorem prod_src (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (e : (S.prod T).graph.E) :
    (S.prod T).graph.src e = (S.graph.src e.1.1, T.graph.src e.1.2) := rfl

@[simp] theorem prod_rev (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (e : (S.prod T).graph.E) :
    ((S.prod T).graph.rev e).1 = (S.graph.rev e.1.1, T.graph.rev e.1.2) := rfl

@[simp] theorem prod_tgt (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (e : (S.prod T).graph.E) :
    (S.prod T).graph.tgt e = (S.graph.tgt e.1.1, T.graph.tgt e.1.2) := by
  simp only [SerreGraph.tgt_def, prod_src, prod_rev]
  rfl

/-- The first projection preserves the base point and labels. -/
@[expose] def prodFst (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) : (S.prod T).Hom S where
  graphHom := {
    mapV := Prod.fst
    mapE := fun e => e.1.1
    map_src := by intro e; rfl
    map_rev := by intro e; rfl }
  map_base := rfl
  map_label := by intro e; rfl

/-- The second projection preserves the base point and labels. -/
@[expose] def prodSnd (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) : (S.prod T).Hom T where
  graphHom := {
    mapV := Prod.snd
    mapE := fun e => e.1.2
    map_src := by intro e; rfl
    map_rev := by intro e; rfl }
  map_base := rfl
  map_label := by intro e; exact e.2.symm

@[simp] theorem prodFst_mapV (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (p : (S.prod T).graph.V) :
    (S.prodFst T).graphHom.mapV p = p.1 := rfl

@[simp] theorem prodSnd_mapV (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (p : (S.prod T).graph.V) :
    (S.prodSnd T).graphHom.mapV p = p.2 := rfl

@[simp] theorem prodFst_mapE (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (e : (S.prod T).graph.E) :
    (S.prodFst T).graphHom.mapE e = e.1.1 := rfl

@[simp] theorem prodSnd_mapE (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (e : (S.prod T).graph.E) :
    (S.prodSnd T).graphHom.mapE e = e.1.2 := rfl

/-- Pair two morphisms with a common source into the labelled fibre product. -/
def prodLift {R : StallingsGraph.{u, z, t} α} {S : StallingsGraph.{u, v, w} α}
    {T : StallingsGraph.{u, x, y} α} (f : R.Hom S) (g : R.Hom T) : R.Hom (S.prod T) where
  graphHom := {
    mapV := fun a => (f.graphHom.mapV a, g.graphHom.mapV a)
    mapE := fun e => ⟨(f.graphHom.mapE e, g.graphHom.mapE e),
      (f.map_label e).trans (g.map_label e).symm⟩
    map_src := by
      intro e
      exact Prod.ext (f.graphHom.map_src e) (g.graphHom.map_src e)
    map_rev := by
      intro e
      apply Subtype.ext
      exact Prod.ext (f.graphHom.map_rev e) (g.graphHom.map_rev e) }
  map_base := Prod.ext f.map_base g.map_base
  map_label := by intro e; exact f.map_label e

@[simp] theorem prodLift_mapV {R : StallingsGraph.{u, z, t} α}
    {S : StallingsGraph.{u, v, w} α} {T : StallingsGraph.{u, x, y} α}
    (f : R.Hom S) (g : R.Hom T) (a : R.graph.V) :
    (prodLift f g).graphHom.mapV a = (f.graphHom.mapV a, g.graphHom.mapV a) := (rfl)

@[simp] theorem prodLift_mapE {R : StallingsGraph.{u, z, t} α}
    {S : StallingsGraph.{u, v, w} α} {T : StallingsGraph.{u, x, y} α}
    (f : R.Hom S) (g : R.Hom T) (e : R.graph.E) :
    ((prodLift f g).graphHom.mapE e).1 =
      (f.graphHom.mapE e, g.graphHom.mapE e) := (rfl)

@[simp] theorem prodFst_comp_prodLift {R : StallingsGraph.{u, z, t} α}
    {S : StallingsGraph.{u, v, w} α} {T : StallingsGraph.{u, x, y} α}
    (f : R.Hom S) (g : R.Hom T) : Hom.comp (S.prodFst T) (prodLift f g) = f := by
  apply Hom.ext
  rw [Hom.comp_graphHom]
  apply SerreGraph.Hom.ext
  · funext a
    simp only [SerreGraph.Hom.comp_mapV, Function.comp_apply, prodLift_mapV]
    rfl
  · funext e
    simp only [SerreGraph.Hom.comp_mapE, Function.comp_apply, prodFst_mapE]
    rw [prodLift_mapE]

@[simp] theorem prodSnd_comp_prodLift {R : StallingsGraph.{u, z, t} α}
    {S : StallingsGraph.{u, v, w} α} {T : StallingsGraph.{u, x, y} α}
    (f : R.Hom S) (g : R.Hom T) : Hom.comp (S.prodSnd T) (prodLift f g) = g := by
  apply Hom.ext
  rw [Hom.comp_graphHom]
  apply SerreGraph.Hom.ext
  · funext a
    simp only [SerreGraph.Hom.comp_mapV, Function.comp_apply, prodLift_mapV]
    rfl
  · funext e
    simp only [SerreGraph.Hom.comp_mapE, Function.comp_apply, prodSnd_mapE]
    rw [prodLift_mapE]

/-- A map into the product is determined by its two projections. -/
theorem prodLift_unique {R : StallingsGraph.{u, z, t} α}
    {S : StallingsGraph.{u, v, w} α} {T : StallingsGraph.{u, x, y} α}
    (h : R.Hom (S.prod T)) :
    prodLift (Hom.comp (S.prodFst T) h) (Hom.comp (S.prodSnd T) h) = h := by
  apply Hom.ext
  apply SerreGraph.Hom.ext
  · funext a
    simp only [prodLift_mapV, Hom.comp_graphHom, SerreGraph.Hom.comp_mapV,
      Function.comp_apply, prodFst_mapV, prodSnd_mapV]
    exact Prod.mk.eta
  · funext e
    apply Subtype.ext
    simp only [prodLift_mapE, Hom.comp_graphHom, SerreGraph.Hom.comp_mapE,
      Function.comp_apply, prodFst_mapE, prodSnd_mapE]

/-- Every word read at a vertex pair is read at each coordinate. -/
theorem prod_subgroup_le (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α) (a : S.graph.V) (b : T.graph.V) :
    (S.prod T).subgroup (a, b) ≤ S.subgroup a ⊓ T.subgroup b := by
  exact le_inf ((S.prodFst T).subgroup_le_subgroup_mapV (a, b))
    ((S.prodSnd T).subgroup_le_subgroup_mapV (a, b))

/-- Paths with the same sequence of signed labels pair to a path in the product. -/
theorem exists_prod_path_of_word_eq (S : StallingsGraph.{u, v, w} α)
    (T : StallingsGraph.{u, x, y} α)
    {a b : S.graph.V} {c d : T.graph.V}
    (p : S.graph.Path a b) (q : T.graph.Path c d)
    (h : S.word p = T.word q) :
    ∃ r : (S.prod T).graph.Path (a, c) (b, d),
      (S.prodFst T).graphHom.toPrefunctor.mapPath r = p ∧
      (S.prodSnd T).graphHom.toPrefunctor.mapPath r = q := by
  induction p generalizing c d q with
  | nil =>
    cases q with
    | nil => exact ⟨.nil, rfl, rfl⟩
    | cons q f => simp at h
  | cons p e ih =>
    cases q with
    | nil => simp at h
    | cons q f =>
      simp only [word_cons] at h
      obtain ⟨hpq, hef⟩ := List.append_inj' h (by simp)
      simp only [List.singleton_inj] at hef
      obtain ⟨r, hrS, hrT⟩ := ih q hpq
      let k : (S.prod T).graph.E := ⟨(e.1, f.1), hef⟩
      refine ⟨r.cons ⟨k, ?_, ?_⟩, ?_, ?_⟩
      · exact Prod.ext e.2.1 f.2.1
      · rw [prod_tgt]
        exact Prod.ext e.2.2 f.2.2
      · -- `erw` crosses the definitional equality between the product's vertex pairs
        -- and the vertex type of its graph, which `rw` cannot unfold here.
        erw [Prefunctor.mapPath_cons]
        rw [hrS]
        rfl
      · erw [Prefunctor.mapPath_cons]
        rw [hrT]
        rfl

/-- A product of folded labelled graphs is folded. -/
theorem IsFolded.prod {S : StallingsGraph.{u, v, w} α}
    {T : StallingsGraph.{u, x, y} α} (hS : S.IsFolded) (hT : T.IsFolded) :
    (S.prod T).IsFolded := by
  simp only [isFolded_def] at hS hT ⊢
  intro e f hsrc hlabel
  apply Subtype.ext
  apply Prod.ext
  · apply hS e.1.1 f.1.1 (congrArg Prod.fst hsrc) hlabel
  · exact hT e.1.2 f.1.2 (congrArg Prod.snd hsrc) (e.2.symm.trans (hlabel.trans f.2))

/-- A morphism into the second factor makes the product accept exactly the first subgroup. -/
theorem prod_subgroup_of_hom {S : StallingsGraph.{u, v, w} α}
    {T : StallingsGraph.{u, x, y} α} (f : S.Hom T) :
    (S.prod T).subgroup (S.prod T).base = S.subgroup S.base := by
  apply le_antisymm
  · exact (S.prodFst T).subgroup_le
  · exact (prodLift (Hom.id S) f).subgroup_le

/-- A morphism into the first factor makes the product accept exactly the second subgroup. -/
theorem prod_subgroup_of_hom_right {S : StallingsGraph.{u, v, w} α}
    {T : StallingsGraph.{u, x, y} α} (f : T.Hom S) :
    (S.prod T).subgroup (S.prod T).base = T.subgroup T.base := by
  apply le_antisymm
  · exact (S.prodSnd T).subgroup_le
  · exact (prodLift f (Hom.id T)).subgroup_le

/-- The rose imposes no additional restriction on accepted words. -/
theorem prod_rose_subgroup (S : StallingsGraph.{u, v, w} α) :
    (S.prod (rose α)).subgroup (S.prod (rose α)).base = S.subgroup S.base := by
  exact prod_subgroup_of_hom S.toRose

/-- A rose in the first factor imposes no additional restriction on accepted words. -/
theorem rose_prod_subgroup (S : StallingsGraph.{u, v, w} α) :
    ((rose α).prod S).subgroup ((rose α).prod S).base = S.subgroup S.base := by
  exact prod_subgroup_of_hom_right S.toRose

end StallingsGraph
end TauCeti
