/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.AddEdge
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Stallings folds of Serre graphs

Let `e₁` and `e₂` be two darts of a Serre graph `Γ` issuing from the same vertex and lying on
distinct geometric edges, that is with `e₁` different from `e₂` and from the reverse of `e₂`. The
Stallings fold identifies `e₂` with `e₁`, the reverse of `e₂` with the reverse of `e₁`, and the
terminal vertex of `e₂` with the terminal vertex of `e₁`. Two constructions cover the two possible
shapes.

* When the two darts have the same terminal vertex, the fold is the graph `Γ.deleteEdge e₂`
  without the geometric edge of `e₂`. It has the vertices of `Γ` and one geometric edge fewer
  (`SerreGraph.card_deleteEdge_geomEdge_add_one`).
* When the terminal vertices are distinct, the fold `SerreGraph.fold` has the darts of
  `Γ.deleteEdge e₂` and the vertices of `Γ` other than `t(e₂)`, every dart at `t(e₂)` being
  attached to `t(e₁)`. Here `e₁` and `e₂` automatically lie on distinct geometric edges. The fold
  has one vertex and one geometric edge fewer.

In both cases the folding map `Γ → Γ'` sends `e₂` to `e₁`, the reverse of `e₂` to the reverse of
`e₁`, and is the identity on the other darts; it is surjective on vertices, so a fold of a
connected graph is connected. A morphism from `Γ` identifying `e₁` with `e₂` factors uniquely
through the folding map.

When `e₂` is a loop and `e₁` is its reverse, there is no folding map, since deleting the geometric
edge of `e₂` deletes `e₁` too. Deleting that geometric edge still keeps a connected graph
connected.

The folded graph is built by deletion rather than as a quotient (compare the fold of a labelled
graph, `TauCeti.StallingsGraph.foldAt`): its darts are those of `Γ` other than `e₂^{±1}`, its
vertices are those of `Γ` (other than `t(e₂)` for `SerreGraph.fold`), and the folding map
restricts to the identity on them.

## Main definitions

* `TauCeti.SerreGraph.foldE`: the dart map of a fold.
* `TauCeti.SerreGraph.deleteEdgeHom`: the folding map onto `Γ.deleteEdge e₂` for parallel darts on
  distinct geometric edges.
* `TauCeti.SerreGraph.foldV`: the vertex map of a fold of two darts with distinct terminal
  vertices.
* `TauCeti.SerreGraph.fold`: the fold of two darts with distinct terminal vertices.
* `TauCeti.SerreGraph.foldGeomEdgeEquiv`: the geometric edges of the fold are those of `Γ` other
  than the edge of `e₂`.
* `TauCeti.SerreGraph.foldHom`: the folding map onto `Γ.fold e₁ e₂ h`.
* `TauCeti.SerreGraph.foldLift`: the morphism out of the fold induced by a morphism out of `Γ`
  identifying `e₁` with `e₂`.

## Main results

* `TauCeti.SerreGraph.comp_restrictInclusion_comp_deleteEdgeHom`,
  `TauCeti.SerreGraph.deleteEdgeHom_ext`, `TauCeti.SerreGraph.foldLift_comp_foldHom`,
  `TauCeti.SerreGraph.foldHom_ext`: the universal property of the folding maps.
* `TauCeti.SerreGraph.Connected.deleteEdge_of_ne_of_src_eq_of_tgt_eq`,
  `TauCeti.SerreGraph.Connected.fold`: folding two darts with the same initial vertex keeps a
  connected graph connected. The first also covers a loop `e₂` with `e₁` its reverse.
* `TauCeti.SerreGraph.card_fold_V_add_one`, `TauCeti.SerreGraph.card_fold_geomEdge_add_one`: a fold
  of two darts with distinct terminal vertices removes one vertex and one geometric edge.

## References

* J. R. Stallings, *Topology of finite graphs*, Invent. Math. 71 (1983), §3.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §4.2.
-/

public section

universe u v w x

namespace TauCeti

namespace SerreGraph

variable (Γ : SerreGraph.{u, v})

/-! ### Folding two parallel darts -/

variable {Γ} in
open scoped Classical in
/-- The dart map of a fold of two darts `e₁` and `e₂` on distinct geometric edges: it sends `e₂` to
`e₁`, the reverse of `e₂` to the reverse of `e₁`, and every other dart to itself. Its values are
the darts of `Γ.deleteEdge e₂`. -/
noncomputable def foldE {e₁ e₂ : Γ.E} (h : Γ.toGeomEdge e₁ ≠ Γ.toGeomEdge e₂) (f : Γ.E) :
    (Γ.deleteEdge e₂).E :=
  if hf : Γ.toGeomEdge f = Γ.toGeomEdge e₂ then
    if f = e₂ then ⟨e₁, h⟩ else (Γ.deleteEdge e₂).rev ⟨e₁, h⟩
  else ⟨f, hf⟩

section foldE

variable {Γ} {e₁ e₂ : Γ.E} (h : Γ.toGeomEdge e₁ ≠ Γ.toGeomEdge e₂)

/-- The dart map of a fold fixes every dart off the geometric edge of `e₂`. -/
@[simp] theorem foldE_of_ne {f : Γ.E} (hf : Γ.toGeomEdge f ≠ Γ.toGeomEdge e₂) :
    foldE h f = ⟨f, hf⟩ := by
  simp [foldE, hf]

-- Not `@[simp]`: `simp [h]` proves the evaluations at `e₁` and `t(e₁)` by the `_of_ne` lemmas.
/-- The dart map of a fold fixes `e₁`. -/
theorem foldE_left : foldE h e₁ = ⟨e₁, h⟩ :=
  foldE_of_ne h h

/-- The dart map of a fold sends `e₂` to `e₁`. -/
@[simp] theorem foldE_right : foldE h e₂ = ⟨e₁, h⟩ := by
  simp [foldE]

/-- The dart map of a fold fixes every dart of `Γ.deleteEdge e₂`. -/
@[simp] theorem foldE_val (f : (Γ.deleteEdge e₂).E) : foldE h f.val = f :=
  foldE_of_ne h f.property

/-- The dart map of a fold commutes with reversal; in particular it sends the reverse of `e₂` to
the reverse of `e₁`. -/
@[simp] theorem foldE_rev (f : Γ.E) : foldE h (Γ.rev f) = (Γ.deleteEdge e₂).rev (foldE h f) := by
  by_cases hf : Γ.toGeomEdge f = Γ.toGeomEdge e₂
  · obtain rfl | rfl := Γ.toGeomEdge_eq_toGeomEdge_iff.1 hf.symm <;>
      simp [foldE, Γ.rev_ne]
  · simp [hf]

/-- The dart map of a fold is surjective: every dart of `Γ.deleteEdge e₂` is its own image. -/
theorem foldE_surjective : Function.Surjective (foldE h) :=
  fun f => ⟨f.val, foldE_val h f⟩

/-- The darts sent to `g` by the dart map of a fold: `g` itself, together with `e₂` if `g` is
`e₁`, and with the reverse of `e₂` if `g` is the reverse of `e₁`. -/
theorem foldE_eq_iff {f : Γ.E} {g : (Γ.deleteEdge e₂).E} :
    foldE h f = g ↔ f = g.val ∨ f = e₂ ∧ g.val = e₁ ∨ f = Γ.rev e₂ ∧ g.val = Γ.rev e₁ := by
  obtain ⟨g, hg⟩ := g
  have hg₁ : g ≠ e₂ := by rintro rfl; exact hg rfl
  have hg₂ : g ≠ Γ.rev e₂ := by rintro rfl; exact hg (Γ.toGeomEdge_rev e₂)
  by_cases hf : Γ.toGeomEdge f = Γ.toGeomEdge e₂
  · obtain rfl | rfl := Γ.toGeomEdge_eq_toGeomEdge_iff.1 hf.symm <;> simp [Subtype.ext_iff] <;>
      grind [Γ.rev_ne]
  · grind [foldE_of_ne, toGeomEdge_rev]

end foldE

variable {Γ} in
/-- A function on darts taking the same value at `e₁` and at `e₂`, and at their reverses, takes the
same value at a dart and at its image under the dart map of the fold. -/
theorem apply_foldE_val {β : Sort*} (k : Γ.E → β) {e₁ e₂ : Γ.E}
    (h : Γ.toGeomEdge e₁ ≠ Γ.toGeomEdge e₂) (hk : k e₁ = k e₂)
    (hk_rev : k (Γ.rev e₁) = k (Γ.rev e₂)) (f : Γ.E) : k (foldE h f).val = k f := by
  by_cases hf : Γ.toGeomEdge f = Γ.toGeomEdge e₂
  · obtain rfl | rfl := Γ.toGeomEdge_eq_toGeomEdge_iff.1 hf.symm <;> simp_all
  · simp [hf]

variable {Γ} in
/-- A morphism identifying `e₁` with `e₂` takes the same value at a dart and at its image under the
dart map of the fold. -/
theorem Hom.mapE_foldE_val {Δ : SerreGraph.{w, x}} (g : Γ.Hom Δ) {e₁ e₂ : Γ.E}
    (h : Γ.toGeomEdge e₁ ≠ Γ.toGeomEdge e₂) (hg : g.mapE e₁ = g.mapE e₂) (f : Γ.E) :
    g.mapE (foldE h f).val = g.mapE f :=
  apply_foldE_val g.mapE h hg (by simp [hg]) f

variable {Γ} in
/-- The folding map of two parallel darts `e₁` and `e₂` on distinct geometric edges: it sends `e₂`
to `e₁`, the reverse of `e₂` to the reverse of `e₁`, and is the identity on the vertices and on the
other darts. -/
noncomputable def deleteEdgeHom {e₁ e₂ : Γ.E} (h : Γ.toGeomEdge e₁ ≠ Γ.toGeomEdge e₂)
    (hsrc : Γ.src e₁ = Γ.src e₂) (htgt : Γ.tgt e₁ = Γ.tgt e₂) : Γ.Hom (Γ.deleteEdge e₂) where
  mapV := id
  mapE := foldE h
  map_src f := by
    by_cases hf : Γ.toGeomEdge f = Γ.toGeomEdge e₂
    · obtain rfl | rfl := Γ.toGeomEdge_eq_toGeomEdge_iff.1 hf.symm <;> simp_all
    · simp [hf]
  map_rev := foldE_rev h

section deleteEdgeHom

variable {Γ} {e₁ e₂ : Γ.E} (h : Γ.toGeomEdge e₁ ≠ Γ.toGeomEdge e₂) (hsrc : Γ.src e₁ = Γ.src e₂)
  (htgt : Γ.tgt e₁ = Γ.tgt e₂)

/-- The folding map of two parallel darts is the identity on vertices. -/
@[simp] theorem deleteEdgeHom_mapV (a : Γ.V) : (deleteEdgeHom h hsrc htgt).mapV a = a :=
  (rfl)

/-- The dart map of the folding map of two parallel darts is the dart map `foldE` of the fold. -/
theorem deleteEdgeHom_mapE (f : Γ.E) : (deleteEdgeHom h hsrc htgt).mapE f = foldE h f :=
  (rfl)

/-- The folding map of two parallel darts fixes every dart off the geometric edge of `e₂`. -/
@[simp] theorem deleteEdgeHom_mapE_of_ne {f : Γ.E} (hf : Γ.toGeomEdge f ≠ Γ.toGeomEdge e₂) :
    (deleteEdgeHom h hsrc htgt).mapE f = ⟨f, hf⟩ :=
  foldE_of_ne h hf

/-- The folding map of two parallel darts fixes `e₁`. -/
theorem deleteEdgeHom_mapE_left : (deleteEdgeHom h hsrc htgt).mapE e₁ = ⟨e₁, h⟩ :=
  foldE_left h

/-- The folding map of two parallel darts sends `e₂` to `e₁`. -/
@[simp] theorem deleteEdgeHom_mapE_right : (deleteEdgeHom h hsrc htgt).mapE e₂ = ⟨e₁, h⟩ :=
  foldE_right h

/-- The folding map of two parallel darts fixes every dart of `Γ.deleteEdge e₂`. -/
@[simp] theorem deleteEdgeHom_mapE_val (f : (Γ.deleteEdge e₂).E) :
    (deleteEdgeHom h hsrc htgt).mapE f.val = f :=
  foldE_val h f

/-- The folding map of two parallel darts preserves the source of a dart, seen in `Γ`. -/
@[simp] theorem src_deleteEdgeHom_mapE_val (f : Γ.E) :
    Γ.src ((deleteEdgeHom h hsrc htgt).mapE f).val = Γ.src f :=
  (deleteEdgeHom h hsrc htgt).map_src f

/-- The folding map of two parallel darts preserves the target of a dart, seen in `Γ`. -/
@[simp] theorem tgt_deleteEdgeHom_mapE_val (f : Γ.E) :
    Γ.tgt ((deleteEdgeHom h hsrc htgt).mapE f).val = Γ.tgt f :=
  Hom.map_tgt _ (deleteEdgeHom h hsrc htgt) f

/-- The folding map of two parallel darts identifies `e₁` with `e₂`. -/
theorem deleteEdgeHom_mapE_left_eq_right :
    (deleteEdgeHom h hsrc htgt).mapE e₁ = (deleteEdgeHom h hsrc htgt).mapE e₂ :=
  (deleteEdgeHom_mapE_left h hsrc htgt).trans (deleteEdgeHom_mapE_right h hsrc htgt).symm

/-- The folding map of two parallel darts is surjective on darts. -/
theorem deleteEdgeHom_mapE_surjective : Function.Surjective (deleteEdgeHom h hsrc htgt).mapE :=
  foldE_surjective h

/-- The darts sent to `g` by the folding map of two parallel darts. -/
theorem deleteEdgeHom_mapE_eq_iff {f : Γ.E} {g : (Γ.deleteEdge e₂).E} :
    (deleteEdgeHom h hsrc htgt).mapE f = g ↔
      f = g.val ∨ f = e₂ ∧ g.val = e₁ ∨ f = Γ.rev e₂ ∧ g.val = Γ.rev e₁ :=
  foldE_eq_iff h

/-- The folding map of two parallel darts is a retraction of the inclusion of `Γ.deleteEdge e₂`
into `Γ`. -/
@[simp] theorem deleteEdgeHom_comp_restrictInclusion :
    (deleteEdgeHom h hsrc htgt).comp (Γ.restrictInclusion _ _) = Hom.id _ :=
  Hom.ext _ (by ext; simp) (by ext; simp)

/-- A morphism from `Γ` identifying `e₁` with `e₂` factors through the folding map of two parallel
darts, by its restriction to `Γ.deleteEdge e₂`. -/
theorem comp_restrictInclusion_comp_deleteEdgeHom {Δ : SerreGraph.{w, x}} (g : Γ.Hom Δ)
    (hg : g.mapE e₁ = g.mapE e₂) :
    (g.comp (Γ.restrictInclusion _ _)).comp (deleteEdgeHom h hsrc htgt) = g :=
  Hom.ext _ (by ext; simp) (by ext; simp [deleteEdgeHom_mapE, g.mapE_foldE_val h hg])

/-- Two morphisms out of `Γ.deleteEdge e₂` agreeing after the folding map of two parallel darts are
equal. -/
theorem deleteEdgeHom_ext {Δ : SerreGraph.{w, x}} {g₁ g₂ : (Γ.deleteEdge e₂).Hom Δ}
    (hg : g₁.comp (deleteEdgeHom h hsrc htgt) = g₂.comp (deleteEdgeHom h hsrc htgt)) :
    g₁ = g₂ :=
  (Hom.cancel_right Function.surjective_id (deleteEdgeHom_mapE_surjective h hsrc htgt)).1 hg

end deleteEdgeHom

variable {Γ} in
/-- Deleting the geometric edge of one of two distinct parallel darts of a connected graph leaves a
connected graph. -/
theorem Connected.deleteEdge_of_ne_of_src_eq_of_tgt_eq (hΓ : Γ.Connected) {e₁ e₂ : Γ.E}
    (h : e₁ ≠ e₂) (hsrc : Γ.src e₁ = Γ.src e₂) (htgt : Γ.tgt e₁ = Γ.tgt e₂) :
    (Γ.deleteEdge e₂).Connected := by
  by_cases h₂ : Γ.toGeomEdge e₁ = Γ.toGeomEdge e₂
  · -- Here `e₁` is the reverse of `e₂`, so `e₂` is a loop, and dropping its darts from a path of
    -- `Γ` gives a path of the deletion.
    have hloop : Γ.src e₂ = Γ.tgt e₂ := by
      obtain rfl | rfl := Γ.toGeomEdge_eq_toGeomEdge_iff.1 h₂.symm <;> simp_all
    obtain ⟨hV, hpre⟩ := (connected_iff Γ).1 hΓ
    refine (connected_iff _).2 ⟨hV, (preconnected_iff _).2 fun a b => ?_⟩
    obtain ⟨p⟩ := (preconnected_iff Γ).1 hpre a b
    induction p with
    | nil => exact ⟨.nil⟩
    | cons _ f ih =>
      obtain ⟨q⟩ := ih
      by_cases hf : Γ.toGeomEdge f.val = Γ.toGeomEdge e₂
      · have hf' : Γ.src f.val = Γ.tgt f.val := by
          rcases Γ.toGeomEdge_eq_toGeomEdge_iff.1 hf.symm with hf | hf <;> simp [hf, hloop]
        obtain rfl := f.property.1.symm.trans (hf'.trans f.property.2)
        exact ⟨q⟩
      · exact ⟨q.cons ⟨⟨f.val, hf⟩, f.property⟩⟩
  · exact (deleteEdgeHom h₂ hsrc htgt).connected_of_surjective Function.surjective_id hΓ

/-! ### Folding two darts with distinct terminal vertices -/

open scoped Classical in
/-- The vertex map of the fold of `e₁` and `e₂`: the terminal vertex of `e₂` is sent to the terminal
vertex of `e₁`, and every other vertex to itself. -/
noncomputable def foldV (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) (a : Γ.V) :
    {a : Γ.V // a ≠ Γ.tgt e₂} :=
  if ha : a = Γ.tgt e₂ then ⟨Γ.tgt e₁, h⟩ else ⟨a, ha⟩

section foldV

variable (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂)

/-- The vertex map of a fold fixes every vertex other than `t(e₂)`. -/
@[simp] theorem foldV_of_ne {a : Γ.V} (ha : a ≠ Γ.tgt e₂) : Γ.foldV e₁ e₂ h a = ⟨a, ha⟩ := by
  simp [foldV, ha]

/-- The vertex map of a fold fixes `t(e₁)`. -/
theorem foldV_tgt_left : Γ.foldV e₁ e₂ h (Γ.tgt e₁) = ⟨Γ.tgt e₁, h⟩ :=
  Γ.foldV_of_ne e₁ e₂ h h

/-- The vertex map of a fold sends `t(e₂)` to `t(e₁)`. -/
@[simp] theorem foldV_tgt_right : Γ.foldV e₁ e₂ h (Γ.tgt e₂) = ⟨Γ.tgt e₁, h⟩ := by
  simp [foldV]

/-- The vertex map of a fold fixes every vertex of the fold. -/
@[simp] theorem foldV_val (a : {a : Γ.V // a ≠ Γ.tgt e₂}) : Γ.foldV e₁ e₂ h a.val = a :=
  Γ.foldV_of_ne e₁ e₂ h a.property

/-- The vertex map of a fold is surjective: every vertex other than `t(e₂)` is its own image. -/
theorem foldV_surjective : Function.Surjective (Γ.foldV e₁ e₂ h) :=
  fun a => ⟨a.val, Γ.foldV_val e₁ e₂ h a⟩

/-- The vertices sent to `b` by the vertex map of a fold: `b` itself, together with `t(e₂)` if `b`
is `t(e₁)`. -/
theorem foldV_eq_iff {a : Γ.V} {b : {a : Γ.V // a ≠ Γ.tgt e₂}} :
    Γ.foldV e₁ e₂ h a = b ↔ a = b.val ∨ a = Γ.tgt e₂ ∧ b.val = Γ.tgt e₁ := by
  obtain ⟨b, hb⟩ := b
  by_cases ha : a = Γ.tgt e₂
  · subst ha
    simp [Subtype.ext_iff, eq_comm, hb]
  · simp [ha, Subtype.ext_iff]

end foldV

variable {Γ} in
/-- A function on vertices taking the same value at `t(e₁)` and at `t(e₂)` takes the same value at a
vertex and at its image under the vertex map of the fold. -/
theorem apply_foldV_val {β : Sort*} (k : Γ.V → β) {e₁ e₂ : Γ.E} (h : Γ.tgt e₁ ≠ Γ.tgt e₂)
    (hk : k (Γ.tgt e₁) = k (Γ.tgt e₂)) (a : Γ.V) : k (Γ.foldV e₁ e₂ h a).val = k a := by
  by_cases ha : a = Γ.tgt e₂
  · subst ha
    simpa using hk
  · simp [ha]

-- Unfolding at instance transparency lets `simp` accept a vertex `⟨a, ha⟩` or a dart `⟨f, hf⟩` of
-- the fold, while `SerreGraph.toQuiver` still applies to its vertices.
/-- The fold of two darts `e₁`, `e₂` with distinct terminal vertices: the graph obtained from
`Γ.deleteEdge e₂` by deleting the vertex `t(e₂)`, every dart of `Γ` at `t(e₂)` being attached to
`t(e₁)`. -/
@[expose, instance_reducible] noncomputable def fold (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) :
    SerreGraph.{u, v} where
  V := {a : Γ.V // a ≠ Γ.tgt e₂}
  E := (Γ.deleteEdge e₂).E
  src f := Γ.foldV e₁ e₂ h (Γ.src f.val)
  rev := (Γ.deleteEdge e₂).rev
  rev_rev := (Γ.deleteEdge e₂).rev_rev
  rev_ne := (Γ.deleteEdge e₂).rev_ne

section fold

variable (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂)

-- `low`: on the image of a dart under a morphism, `Hom.map_src` and `Hom.map_tgt` come first.
/-- The source of a dart of the fold is the image of its source in `Γ`. -/
@[simp low] theorem fold_src (f : (Γ.fold e₁ e₂ h).E) :
    (Γ.fold e₁ e₂ h).src f = Γ.foldV e₁ e₂ h (Γ.src f.val) :=
  rfl

/-- Reversal in the fold is reversal in `Γ`. -/
@[simp] theorem fold_rev_val (f : (Γ.fold e₁ e₂ h).E) : ((Γ.fold e₁ e₂ h).rev f).val = Γ.rev f.val
    :=
  rfl

/-- The target of a dart of the fold is the image of its target in `Γ`. -/
@[simp low] theorem fold_tgt (f : (Γ.fold e₁ e₂ h).E) :
    (Γ.fold e₁ e₂ h).tgt f = Γ.foldV e₁ e₂ h (Γ.tgt f.val) :=
  rfl

/-- A fold of a graph with finitely many vertices has finitely many vertices. -/
instance [Finite Γ.V] : Finite (Γ.fold e₁ e₂ h).V :=
  inferInstanceAs (Finite {a : Γ.V // a ≠ Γ.tgt e₂})

/-- A fold of a graph with finitely many darts has finitely many darts. -/
instance [Finite Γ.E] : Finite (Γ.fold e₁ e₂ h).E :=
  inferInstanceAs (Finite (Γ.deleteEdge e₂).E)

/-- A fold has a vertex, the terminal vertex of `e₁`. -/
instance : Nonempty (Γ.fold e₁ e₂ h).V :=
  ⟨Γ.foldV e₁ e₂ h (Γ.tgt e₁)⟩

/-- Equality of vertices of a fold is decidable when it is in `Γ`. -/
instance [DecidableEq Γ.V] : DecidableEq (Γ.fold e₁ e₂ h).V :=
  inferInstanceAs (DecidableEq {a : Γ.V // a ≠ Γ.tgt e₂})

/-- Equality of darts of a fold is decidable when it is in `Γ`. -/
instance [DecidableEq Γ.E] : DecidableEq (Γ.fold e₁ e₂ h).E :=
  inferInstanceAs (DecidableEq (Γ.deleteEdge e₂).E)

/-- The geometric edges of the fold are those of `Γ` other than the edge of `e₂`. -/
noncomputable def foldGeomEdgeEquiv :
    (Γ.fold e₁ e₂ h).GeomEdge ≃ {q : Γ.GeomEdge // q ≠ Γ.toGeomEdge e₂} :=
  (GeomEdge.congr (Γ.fold e₁ e₂ h) (Δ := Γ.deleteEdge e₂) (.refl _) fun _ => rfl).trans
    (Γ.deleteEdgeGeomEdgeEquiv e₂)

@[simp] theorem coe_foldGeomEdgeEquiv_toGeomEdge (f : (Γ.fold e₁ e₂ h).E) :
    (Γ.foldGeomEdgeEquiv e₁ e₂ h ((Γ.fold e₁ e₂ h).toGeomEdge f) : Γ.GeomEdge) =
      Γ.toGeomEdge f.val := by
  rw [foldGeomEdgeEquiv, Equiv.trans_apply]
  exact (congrArg (fun q => (Γ.deleteEdgeGeomEdgeEquiv e₂ q : Γ.GeomEdge))
    (GeomEdge.congr_toGeomEdge _ _ _ f)).trans (Γ.coe_deleteEdgeGeomEdgeEquiv_toGeomEdge e₂ f)

/-- A fold of a graph with finitely many geometric edges has finitely many geometric edges. -/
instance [Finite Γ.GeomEdge] : Finite (Γ.fold e₁ e₂ h).GeomEdge :=
  .of_equiv _ (Γ.foldGeomEdgeEquiv e₁ e₂ h).symm

end fold

variable {Γ} in
/-- The folding map of two darts `e₁`, `e₂` with the same initial vertex and distinct terminal
vertices: it sends `e₂` to `e₁`, the reverse of `e₂` to the reverse of `e₁`, the vertex `t(e₂)` to
`t(e₁)`, and is the identity elsewhere. -/
noncomputable def foldHom {e₁ e₂ : Γ.E} (h : Γ.tgt e₁ ≠ Γ.tgt e₂) (hsrc : Γ.src e₁ = Γ.src e₂) :
    Γ.Hom (Γ.fold e₁ e₂ h) where
  mapV := Γ.foldV e₁ e₂ h
  mapE := foldE (Γ.toGeomEdge_ne_toGeomEdge_of_src_eq_of_tgt_ne hsrc h)
  map_src f := by
    by_cases hf : Γ.toGeomEdge f = Γ.toGeomEdge e₂
    · obtain rfl | rfl := Γ.toGeomEdge_eq_toGeomEdge_iff.1 hf.symm <;> simp_all
    · simp [hf]
  map_rev := foldE_rev _

section foldHom

variable {Γ} {e₁ e₂ : Γ.E} (h : Γ.tgt e₁ ≠ Γ.tgt e₂) (hsrc : Γ.src e₁ = Γ.src e₂)

/-- The vertex map of the folding map is the vertex map `foldV` of the fold. -/
@[simp] theorem foldHom_mapV (a : Γ.V) : (foldHom h hsrc).mapV a = Γ.foldV e₁ e₂ h a :=
  (rfl)

/-- The dart map of the folding map is the dart map `foldE` of the fold. -/
theorem foldHom_mapE (f : Γ.E) : (foldHom h hsrc).mapE f =
    foldE (Γ.toGeomEdge_ne_toGeomEdge_of_src_eq_of_tgt_ne hsrc h) f :=
  (rfl)

/-- The folding map fixes every dart off the geometric edge of `e₂`. -/
@[simp] theorem foldHom_mapE_of_ne {f : Γ.E} (hf : Γ.toGeomEdge f ≠ Γ.toGeomEdge e₂) :
    (foldHom h hsrc).mapE f = ⟨f, hf⟩ :=
  foldE_of_ne _ hf

/-- The folding map fixes `e₁`. -/
@[simp] theorem foldHom_mapE_left :
    (foldHom h hsrc).mapE e₁ = ⟨e₁, Γ.toGeomEdge_ne_toGeomEdge_of_src_eq_of_tgt_ne hsrc h⟩ :=
  foldE_left _

/-- The folding map sends `e₂` to `e₁`. -/
@[simp] theorem foldHom_mapE_right :
    (foldHom h hsrc).mapE e₂ = ⟨e₁, Γ.toGeomEdge_ne_toGeomEdge_of_src_eq_of_tgt_ne hsrc h⟩ :=
  foldE_right _

/-- The folding map fixes every dart of `Γ.deleteEdge e₂`. -/
@[simp] theorem foldHom_mapE_val (f : (Γ.fold e₁ e₂ h).E) : (foldHom h hsrc).mapE f.val = f :=
  foldE_val _ f

/-- The folding map identifies `e₁` with `e₂`. -/
theorem foldHom_mapE_left_eq_right : (foldHom h hsrc).mapE e₁ = (foldHom h hsrc).mapE e₂ :=
  (foldHom_mapE_left h hsrc).trans (foldHom_mapE_right h hsrc).symm

/-- The folding map identifies `t(e₁)` with `t(e₂)`. -/
theorem foldHom_mapV_tgt_left_eq_right :
    (foldHom h hsrc).mapV (Γ.tgt e₁) = (foldHom h hsrc).mapV (Γ.tgt e₂) :=
  (Γ.foldV_tgt_left e₁ e₂ h).trans (Γ.foldV_tgt_right e₁ e₂ h).symm

/-- The folding map is surjective on vertices. -/
theorem foldHom_mapV_surjective : Function.Surjective (foldHom h hsrc).mapV :=
  Γ.foldV_surjective e₁ e₂ h

/-- The folding map is surjective on darts. -/
theorem foldHom_mapE_surjective : Function.Surjective (foldHom h hsrc).mapE :=
  foldE_surjective _

/-- The darts sent to `g` by the folding map. -/
theorem foldHom_mapE_eq_iff {f : Γ.E} {g : (Γ.fold e₁ e₂ h).E} :
    (foldHom h hsrc).mapE f = g ↔ f = g.val ∨ f = e₂ ∧ g.val = e₁ ∨ f = Γ.rev e₂ ∧ g.val = Γ.rev e₁
        :=
  foldE_eq_iff _

end foldHom

variable {Γ} in
/-- The morphism out of the fold induced by a morphism `g` from `Γ` identifying `e₁` with `e₂`: it
sends a vertex or a dart of the fold to the image under `g` of the same vertex or dart of `Γ`. -/
def foldLift {e₁ e₂ : Γ.E} (h : Γ.tgt e₁ ≠ Γ.tgt e₂) {Δ : SerreGraph.{w, x}} (g : Γ.Hom Δ)
    (hg : g.mapE e₁ = g.mapE e₂) : (Γ.fold e₁ e₂ h).Hom Δ where
  mapV a := g.mapV a.val
  mapE f := g.mapE f.val
  map_src f :=
    (g.map_src f.val).trans (apply_foldV_val g.mapV h (g.mapV_tgt_eq_of_mapE_eq hg) _).symm
  map_rev f := g.map_rev f.val

section foldLift

variable {Γ} {e₁ e₂ : Γ.E} (h : Γ.tgt e₁ ≠ Γ.tgt e₂) {Δ : SerreGraph.{w, x}} (g : Γ.Hom Δ)
  (hg : g.mapE e₁ = g.mapE e₂)

/-- The induced morphism sends a vertex of the fold to the image of the same vertex of `Γ`. -/
@[simp] theorem foldLift_mapV (a : (Γ.fold e₁ e₂ h).V) : (foldLift h g hg).mapV a = g.mapV a.val :=
  (rfl)

-- This must be tried before `foldLift_mapV`, which would leave the image under `g` of an unknown
-- vertex of the fold.
/-- The induced morphism sends the image of a vertex under the vertex map of the fold to the image
of that vertex. -/
@[simp high] theorem foldLift_mapV_foldV (a : Γ.V) :
    (foldLift h g hg).mapV (Γ.foldV e₁ e₂ h a) = g.mapV a :=
  apply_foldV_val g.mapV h (g.mapV_tgt_eq_of_mapE_eq hg) a

/-- The induced morphism sends a dart of the fold to the image of the same dart of `Γ`. -/
@[simp] theorem foldLift_mapE (f : (Γ.fold e₁ e₂ h).E) : (foldLift h g hg).mapE f = g.mapE f.val :=
  (rfl)

-- This must be tried before `foldLift_mapE`, which would leave the image under `g` of an unknown
-- dart of the fold.
/-- The induced morphism sends the image of a dart under the folding map to the image of that
dart. -/
@[simp high] theorem foldLift_mapE_foldHom (hsrc : Γ.src e₁ = Γ.src e₂) (f : Γ.E) :
    (foldLift h g hg).mapE ((foldHom h hsrc).mapE f) = g.mapE f :=
  g.mapE_foldE_val _ hg f

/-- A morphism from `Γ` identifying `e₁` with `e₂` factors through the folding map. -/
@[simp] theorem foldLift_comp_foldHom (hsrc : Γ.src e₁ = Γ.src e₂) :
    (foldLift h g hg).comp (foldHom h hsrc) = g :=
  Hom.ext _ (funext fun a => by simp) (funext fun f => by simp)

end foldLift

/-- Two morphisms out of the fold agreeing after the folding map are equal. -/
theorem foldHom_ext {Γ : SerreGraph.{u, v}} {e₁ e₂ : Γ.E} {h : Γ.tgt e₁ ≠ Γ.tgt e₂}
    (hsrc : Γ.src e₁ = Γ.src e₂) {Δ : SerreGraph.{w, x}} {g₁ g₂ : (Γ.fold e₁ e₂ h).Hom Δ}
    (hg : g₁.comp (foldHom h hsrc) = g₂.comp (foldHom h hsrc)) : g₁ = g₂ :=
  (Hom.cancel_right (foldHom_mapV_surjective h hsrc) (foldHom_mapE_surjective h hsrc)).1 hg

/-- The morphism induced on the fold is the unique morphism whose composite with the folding map is
`g`. -/
theorem foldLift_unique {Γ : SerreGraph.{u, v}} {e₁ e₂ : Γ.E} {h : Γ.tgt e₁ ≠ Γ.tgt e₂}
    (hsrc : Γ.src e₁ = Γ.src e₂) {Δ : SerreGraph.{w, x}} {g : Γ.Hom Δ} (hg : g.mapE e₁ = g.mapE e₂)
    {k : (Γ.fold e₁ e₂ h).Hom Δ} (hk : k.comp (foldHom h hsrc) = g) : k = foldLift h g hg :=
  foldHom_ext hsrc (hk.trans (foldLift_comp_foldHom h g hg hsrc).symm)

variable {Γ} in
/-- A fold of a connected graph is connected. -/
theorem Connected.fold (hΓ : Γ.Connected) {e₁ e₂ : Γ.E} (h : Γ.tgt e₁ ≠ Γ.tgt e₂)
    (hsrc : Γ.src e₁ = Γ.src e₂) : (Γ.fold e₁ e₂ h).Connected :=
  (foldHom h hsrc).connected_of_surjective (foldHom_mapV_surjective h hsrc) hΓ

/-- A fold of two darts with distinct terminal vertices lowers the number of vertices by one. -/
theorem card_fold_V_add_one [Finite Γ.V] (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) :
    Nat.card (Γ.fold e₁ e₂ h).V + 1 = Nat.card Γ.V := by
  classical
  exact (Finite.card_option (α := {a : Γ.V // a ≠ Γ.tgt e₂})).symm.trans
    (Nat.card_congr (Equiv.optionSubtypeNe _))

/-- A fold of two darts with distinct terminal vertices lowers the number of geometric edges by
one. -/
theorem card_fold_geomEdge_add_one [Finite Γ.GeomEdge] (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) :
    Nat.card (Γ.fold e₁ e₂ h).GeomEdge + 1 = Nat.card Γ.GeomEdge := by
  classical
  rw [Nat.card_congr (Γ.foldGeomEdgeEquiv e₁ e₂ h), ← Finite.card_option,
    Nat.card_congr (Equiv.optionSubtypeNe _)]

end SerreGraph

end TauCeti
