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
connected graph is connected.

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
* `TauCeti.SerreGraph.foldHom`: the folding map onto `Γ.fold e₁ e₂ h`.

## Main results

* `TauCeti.SerreGraph.Connected.deleteEdge`, `TauCeti.SerreGraph.Connected.fold`: folding two
  darts with the same initial vertex keeps a connected graph connected. The first also covers a
  loop `e₂` with `e₁` its reverse.
* `TauCeti.SerreGraph.card_V_fold`, `TauCeti.SerreGraph.card_geomEdge_fold`: a fold of two darts
  with distinct terminal vertices removes one vertex and one geometric edge.

## References

* J. R. Stallings, *Topology of finite graphs*, Invent. Math. 71 (1983), §3.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §4.2.
-/

public section

universe u v

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

/-- The dart map of a fold sends `e₂` to `e₁`. -/
@[simp] theorem foldE_self : (foldE h e₂).1 = e₁ := by
  simp [foldE]

/-- The dart map of a fold sends the reverse of `e₂` to the reverse of `e₁`. -/
@[simp] theorem foldE_rev : (foldE h (Γ.rev e₂)).1 = Γ.rev e₁ := by
  simp [foldE, Γ.rev_ne e₂]

/-- The dart map of a fold fixes every dart off the geometric edge of `e₂`, as a dart of `Γ`. -/
@[simp] theorem foldE_of_ne {f : Γ.E} (hf : Γ.toGeomEdge f ≠ Γ.toGeomEdge e₂) :
    (foldE h f).1 = f := by
  simp [foldE, hf]

/-- The dart map of a fold fixes every dart of `Γ.deleteEdge e₂`. -/
@[simp] theorem foldE_val (f : (Γ.deleteEdge e₂).E) : foldE h f.1 = f :=
  Subtype.ext (foldE_of_ne h f.2)

/-- The dart map of a fold commutes with reversal. -/
theorem foldE_rev_apply (f : Γ.E) : (foldE h (Γ.rev f)).1 = Γ.rev (foldE h f).1 := by
  by_cases hf : Γ.toGeomEdge f = Γ.toGeomEdge e₂
  · obtain rfl | rfl := Γ.toGeomEdge_eq_toGeomEdge_iff.1 hf.symm <;> simp
  · simp [hf]

end foldE

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
  map_rev f := Subtype.ext (foldE_rev_apply h f)

section deleteEdgeHom

variable {Γ} {e₁ e₂ : Γ.E} (h : Γ.toGeomEdge e₁ ≠ Γ.toGeomEdge e₂) (hsrc : Γ.src e₁ = Γ.src e₂)
  (htgt : Γ.tgt e₁ = Γ.tgt e₂)

/-- The folding map of two parallel darts is the identity on vertices. -/
@[simp] theorem deleteEdgeHom_mapV (a : Γ.V) : (deleteEdgeHom h hsrc htgt).mapV a = a :=
  (rfl)

/-- The dart map of the folding map of two parallel darts is the dart map `foldE` of the fold. -/
theorem deleteEdgeHom_mapE (f : Γ.E) : (deleteEdgeHom h hsrc htgt).mapE f = foldE h f :=
  (rfl)

-- With `Hom.map_rev`, `simp` also computes the image of the reverse of `e₂`.
/-- The folding map of two parallel darts sends `e₂` to `e₁`. -/
@[simp] theorem deleteEdgeHom_mapE_self : ((deleteEdgeHom h hsrc htgt).mapE e₂).1 = e₁ :=
  foldE_self h

/-- The folding map of two parallel darts fixes every dart of `Γ.deleteEdge e₂`. -/
@[simp] theorem deleteEdgeHom_mapE_val (f : (Γ.deleteEdge e₂).E) :
    (deleteEdgeHom h hsrc htgt).mapE f.1 = f :=
  foldE_val h f

end deleteEdgeHom

variable {Γ} in
/-- Deleting the geometric edge of one of two distinct parallel darts of a connected graph leaves a
connected graph. -/
theorem Connected.deleteEdge (hΓ : Γ.Connected) {e₁ e₂ : Γ.E} (h : e₁ ≠ e₂)
    (hsrc : Γ.src e₁ = Γ.src e₂) (htgt : Γ.tgt e₁ = Γ.tgt e₂) : (Γ.deleteEdge e₂).Connected := by
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
      by_cases hf : Γ.toGeomEdge f.1 = Γ.toGeomEdge e₂
      · have hf' : Γ.src f.1 = Γ.tgt f.1 := by
          rcases Γ.toGeomEdge_eq_toGeomEdge_iff.1 hf.symm with hf | hf <;> simp [hf, hloop]
        obtain rfl := f.2.1.symm.trans (hf'.trans f.2.2)
        exact ⟨q⟩
      · exact ⟨q.cons ⟨⟨f.1, hf⟩, f.2⟩⟩
  · exact (deleteEdgeHom h₂ hsrc htgt).connected_of_surjective Function.surjective_id hΓ

/-! ### Folding two darts with distinct terminal vertices -/

open scoped Classical in
/-- The vertex map of the fold of `e₁` and `e₂`: the terminal vertex of `e₂` is sent to the terminal
vertex of `e₁`, and every other vertex to itself. -/
noncomputable def foldV (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) (a : Γ.V) :
    {a : Γ.V // a ≠ Γ.tgt e₂} :=
  if ha : a = Γ.tgt e₂ then ⟨Γ.tgt e₁, h⟩ else ⟨a, ha⟩

/-- The vertex map of a fold sends `t(e₂)` to `t(e₁)`. -/
@[simp] theorem foldV_tgt (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) :
    Γ.foldV e₁ e₂ h (Γ.tgt e₂) = ⟨Γ.tgt e₁, h⟩ := by
  simp [foldV]

/-- The vertex map of a fold fixes every vertex other than `t(e₂)`. -/
@[simp] theorem foldV_of_ne (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) {a : Γ.V} (ha : a ≠ Γ.tgt e₂) :
    Γ.foldV e₁ e₂ h a = ⟨a, ha⟩ := by
  simp [foldV, ha]

/-- The vertex map of a fold is surjective: every vertex other than `t(e₂)` is its own image. -/
theorem foldV_surjective (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) :
    Function.Surjective (Γ.foldV e₁ e₂ h) :=
  fun a => ⟨a.1, Γ.foldV_of_ne e₁ e₂ h a.2⟩

/-- The fold of two darts `e₁`, `e₂` with distinct terminal vertices: the graph obtained from
`Γ.deleteEdge e₂` by deleting the vertex `t(e₂)`, every dart of `Γ` at `t(e₂)` being attached to
`t(e₁)`. -/
@[expose] noncomputable def fold (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) : SerreGraph.{u, v} where
  V := {a : Γ.V // a ≠ Γ.tgt e₂}
  E := (Γ.deleteEdge e₂).E
  src f := Γ.foldV e₁ e₂ h (Γ.src f.1)
  rev := (Γ.deleteEdge e₂).rev
  rev_rev := (Γ.deleteEdge e₂).rev_rev
  rev_ne := (Γ.deleteEdge e₂).rev_ne

/-- The source of a dart of the fold is the image of its source in `Γ`. -/
@[simp] theorem fold_src (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) (f : (Γ.fold e₁ e₂ h).E) :
    (Γ.fold e₁ e₂ h).src f = Γ.foldV e₁ e₂ h (Γ.src f.1) :=
  rfl

/-- Reversal in the fold is reversal in `Γ`. -/
@[simp] theorem fold_rev_val (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) (f : (Γ.fold e₁ e₂ h).E) :
    ((Γ.fold e₁ e₂ h).rev f).1 = Γ.rev f.1 :=
  rfl

/-- The target of a dart of the fold is the image of its target in `Γ`. -/
@[simp] theorem fold_tgt (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) (f : (Γ.fold e₁ e₂ h).E) :
    (Γ.fold e₁ e₂ h).tgt f = Γ.foldV e₁ e₂ h (Γ.tgt f.1) :=
  rfl

variable {Γ} in
/-- The folding map of two darts `e₁`, `e₂` with the same initial vertex and distinct terminal
vertices: it sends `e₂` to `e₁`, the reverse of `e₂` to the reverse of `e₁`, the vertex `t(e₂)` to
`t(e₁)`, and is the identity elsewhere. -/
noncomputable def foldHom {e₁ e₂ : Γ.E} (h : Γ.tgt e₁ ≠ Γ.tgt e₂) (hsrc : Γ.src e₁ = Γ.src e₂) :
    Γ.Hom (Γ.fold e₁ e₂ h) where
  mapV := Γ.foldV e₁ e₂ h
  mapE := foldE (Γ.toGeomEdge_ne_toGeomEdge_of_src_eq_of_tgt_ne hsrc h)
  map_src f := by
    -- `fold_src` does not rewrite here: `foldE _ f` is typed as a dart of `Γ.deleteEdge e₂` rather
    -- than as a dart of the fold, so the source in the fold is unfolded by hand.
    change Γ.foldV e₁ e₂ h (Γ.src (foldE _ f).1) = Γ.foldV e₁ e₂ h (Γ.src f)
    by_cases hf : Γ.toGeomEdge f = Γ.toGeomEdge e₂
    · obtain rfl | rfl := Γ.toGeomEdge_eq_toGeomEdge_iff.1 hf.symm <;> simp_all
    · simp [hf]
  map_rev f := Subtype.ext (foldE_rev_apply _ f)

section foldHom

variable {Γ} {e₁ e₂ : Γ.E} (h : Γ.tgt e₁ ≠ Γ.tgt e₂) (hsrc : Γ.src e₁ = Γ.src e₂)

/-- The vertex map of the folding map is the vertex map `foldV` of the fold. -/
@[simp] theorem foldHom_mapV (a : Γ.V) : (foldHom h hsrc).mapV a = Γ.foldV e₁ e₂ h a :=
  (rfl)

/-- The dart map of the folding map is the dart map `foldE` of the fold. -/
theorem foldHom_mapE (f : Γ.E) : (foldHom h hsrc).mapE f =
    foldE (Γ.toGeomEdge_ne_toGeomEdge_of_src_eq_of_tgt_ne hsrc h) f :=
  (rfl)

-- With `Hom.map_rev`, `simp` also computes the image of the reverse of `e₂`.
/-- The folding map sends `e₂` to `e₁`. -/
@[simp] theorem foldHom_mapE_self : ((foldHom h hsrc).mapE e₂).1 = e₁ :=
  foldE_self _

/-- The folding map fixes every dart of `Γ.deleteEdge e₂`. -/
@[simp] theorem foldHom_mapE_val (f : (Γ.fold e₁ e₂ h).E) : (foldHom h hsrc).mapE f.1 = f :=
  foldE_val _ f

end foldHom

variable {Γ} in
/-- A fold of a connected graph is connected. -/
theorem Connected.fold (hΓ : Γ.Connected) {e₁ e₂ : Γ.E} (h : Γ.tgt e₁ ≠ Γ.tgt e₂)
    (hsrc : Γ.src e₁ = Γ.src e₂) : (Γ.fold e₁ e₂ h).Connected :=
  (foldHom h hsrc).connected_of_surjective (Γ.foldV_surjective e₁ e₂ h) hΓ

/-- A fold of two darts with distinct terminal vertices lowers the number of vertices by one. -/
theorem card_V_fold [Finite Γ.V] (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) :
    Nat.card (Γ.fold e₁ e₂ h).V + 1 = Nat.card Γ.V := by
  classical
  exact (Finite.card_option (α := {a : Γ.V // a ≠ Γ.tgt e₂})).symm.trans
    (Nat.card_congr (Equiv.optionSubtypeNe _))

/-- A fold of two darts with distinct terminal vertices lowers the number of geometric edges by
one: it has the geometric edges of `Γ.deleteEdge e₂`. -/
theorem card_geomEdge_fold [Finite Γ.GeomEdge] (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) :
    Nat.card (Γ.fold e₁ e₂ h).GeomEdge + 1 = Nat.card Γ.GeomEdge := by
  rw [← Γ.card_deleteEdge_geomEdge_add_one e₂]
  exact congrArg (· + 1) (Nat.card_congr (GeomEdge.congr _ (.refl _) fun _ => rfl))

end SerreGraph

end TauCeti
