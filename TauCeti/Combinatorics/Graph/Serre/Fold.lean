/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Stallings folds of Serre graphs

Let `e₁` and `e₂` be two darts of a Serre graph `Γ` issuing from the same vertex, with `e₁`
different from `e₂` and from the reverse of `e₂`. The Stallings fold identifies `e₂` with `e₁`, the
reverse of `e₂` with the reverse of `e₁`, and the terminal vertex of `e₂` with the terminal vertex
of `e₁`. Two constructions cover the two possible shapes.

* When the two darts have the same terminal vertex, the fold deletes the geometric edge of `e₂`:
  `SerreGraph.deleteEdge`. It has the vertices of `Γ` and one geometric edge fewer.
* When the terminal vertices are distinct, the fold deletes the geometric edge of `e₂` and the
  vertex `t(e₂)`, every dart at `t(e₂)` being attached to `t(e₁)`: `SerreGraph.fold`. Here `e₁` is
  automatically not the reverse of `e₂`. The fold has one vertex and one geometric edge fewer.

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

* `TauCeti.SerreGraph.deleteEdge`: the graph without the geometric edge of a dart.
* `TauCeti.SerreGraph.foldE`: the dart map of a fold.
* `TauCeti.SerreGraph.deleteEdgeHom`: the folding map onto `Γ.deleteEdge e₂` for parallel darts
  `e₁ ≠ e₂` with `e₁` not the reverse of `e₂`.
* `TauCeti.SerreGraph.foldV`: the vertex map of a fold of two darts with distinct terminal
  vertices.
* `TauCeti.SerreGraph.fold`: the fold of two darts with distinct terminal vertices.
* `TauCeti.SerreGraph.foldHom`: the folding map onto `Γ.fold e₁ e₂ h`.

## Main results

* `TauCeti.SerreGraph.Connected.deleteEdge`, `TauCeti.SerreGraph.Connected.fold`: folding two
  darts with the same initial vertex keeps a connected graph connected. The first also covers a
  loop `e₂` with `e₁` its reverse.
* `TauCeti.SerreGraph.card_geomEdge_deleteEdge`, `TauCeti.SerreGraph.card_geomEdge_fold`: a fold
  removes one geometric edge.
* `TauCeti.SerreGraph.card_V_fold`: a fold of darts with distinct terminal vertices removes one
  vertex.

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

/- A Serre graph whose darts are, through an injective map commuting with reversal, the darts of
`Γ` other than `e` and its reverse has one geometric edge fewer than `Γ`. -/
private theorem card_geomEdge_add_one {Δ : SerreGraph.{w, x}} [Finite Γ.GeomEdge] (e : Γ.E)
    (ι : Δ.E → Γ.E) (hι : Function.Injective ι) (hrev : ∀ f, ι (Δ.rev f) = Γ.rev (ι f))
    (hrange : ∀ f, f ∈ Set.range ι ↔ f ≠ e ∧ f ≠ Γ.rev e) :
    Nat.card Δ.GeomEdge + 1 = Nat.card Γ.GeomEdge := by
  classical
  have hne (f : Δ.E) : Γ.toGeomEdge (ι f) ≠ Γ.toGeomEdge e := fun h => by
    have := (hrange (ι f)).1 ⟨f, rfl⟩
    rcases Γ.toGeomEdge_eq_toGeomEdge_iff.1 h with rfl | rfl <;> simp_all
  let j : Δ.GeomEdge → {y : Γ.GeomEdge // y ≠ Γ.toGeomEdge e} :=
    GeomEdge.lift Δ (fun f => ⟨Γ.toGeomEdge (ι f), hne f⟩) fun f => Subtype.ext (by simp [hrev])
  have hj : Function.Bijective j := by
    refine ⟨fun a b hab => ?_, fun ⟨y, hy⟩ => ?_⟩
    · obtain ⟨f, rfl⟩ := Δ.toGeomEdge_surjective a
      obtain ⟨g, rfl⟩ := Δ.toGeomEdge_surjective b
      simp only [j, GeomEdge.lift_toGeomEdge, Subtype.mk.injEq] at hab
      rcases Γ.toGeomEdge_eq_toGeomEdge_iff.1 hab with h | h
      · rw [hι h]
      · rw [← hrev] at h
        rw [hι h, toGeomEdge_rev]
    · obtain ⟨g, rfl⟩ := Γ.toGeomEdge_surjective y
      obtain ⟨f, rfl⟩ := (hrange g).2
        ⟨fun h => hy (by rw [h]), fun h => hy (by rw [h, toGeomEdge_rev])⟩
      exact ⟨Δ.toGeomEdge f, by simp [j]⟩
  rw [Nat.card_congr (Equiv.ofBijective j hj), ← Finite.card_option,
    Nat.card_congr (Equiv.optionSubtypeNe _)]

/-! ### Deleting a geometric edge -/

/-- The graph obtained from `Γ` by deleting the dart `e` and its reverse. It has the vertices of
`Γ`. -/
abbrev deleteEdge (e : Γ.E) : SerreGraph.{u, v} :=
  Γ.restrict {f | f ≠ e ∧ f ≠ Γ.rev e} fun f hf =>
    ⟨fun h => hf.2 ((Γ.rev_rev f).symm.trans (congrArg Γ.rev h)), fun h => hf.1 (Γ.rev_injective h)⟩

variable {Γ} in
open scoped Classical in
/-- The dart map of a fold: it sends `e₂` to `e₁`, the reverse of `e₂` to the reverse of `e₁`, and
every other dart to itself. Its values are darts other than `e₂` and its reverse. -/
noncomputable def foldE {e₁ e₂ : Γ.E} (h₁ : e₁ ≠ e₂) (h₂ : e₁ ≠ Γ.rev e₂) (f : Γ.E) :
    {f : Γ.E // f ≠ e₂ ∧ f ≠ Γ.rev e₂} :=
  if hf : f = e₂ then ⟨e₁, h₁, h₂⟩
  else if hf' : f = Γ.rev e₂ then
    ⟨Γ.rev e₁, fun h => h₂ ((Γ.rev_rev e₁).symm.trans (congrArg Γ.rev h)),
      fun h => h₁ (Γ.rev_injective h)⟩
  else ⟨f, hf, hf'⟩

variable {Γ} in
/-- The dart map of a fold sends `e₂` to `e₁`. -/
@[simp] theorem foldE_self {e₁ e₂ : Γ.E} (h₁ : e₁ ≠ e₂) (h₂ : e₁ ≠ Γ.rev e₂) :
    (foldE h₁ h₂ e₂).1 = e₁ := by
  simp [foldE]

variable {Γ} in
/-- The dart map of a fold sends the reverse of `e₂` to the reverse of `e₁`. -/
@[simp] theorem foldE_rev {e₁ e₂ : Γ.E} (h₁ : e₁ ≠ e₂) (h₂ : e₁ ≠ Γ.rev e₂) :
    (foldE h₁ h₂ (Γ.rev e₂)).1 = Γ.rev e₁ := by
  simp [foldE, Γ.rev_ne e₂]

variable {Γ} in
/-- The dart map of a fold fixes every dart other than `e₂` and its reverse, as a dart of `Γ`. -/
@[simp] theorem foldE_of_ne {e₁ e₂ : Γ.E} (h₁ : e₁ ≠ e₂) (h₂ : e₁ ≠ Γ.rev e₂) {f : Γ.E}
    (hf : f ≠ e₂) (hf' : f ≠ Γ.rev e₂) : (foldE h₁ h₂ f).1 = f := by
  simp [foldE, hf, hf']

variable {Γ} in
/-- The dart map of a fold fixes every dart other than `e₂` and its reverse. -/
@[simp] theorem foldE_val {e₁ e₂ : Γ.E} (h₁ : e₁ ≠ e₂) (h₂ : e₁ ≠ Γ.rev e₂)
    (f : {f : Γ.E // f ≠ e₂ ∧ f ≠ Γ.rev e₂}) : foldE h₁ h₂ f.1 = f :=
  Subtype.ext (foldE_of_ne h₁ h₂ f.2.1 f.2.2)

variable {Γ} in
/-- The dart map of a fold commutes with reversal. -/
theorem foldE_rev_apply {e₁ e₂ : Γ.E} (h₁ : e₁ ≠ e₂) (h₂ : e₁ ≠ Γ.rev e₂) (f : Γ.E) :
    (foldE h₁ h₂ (Γ.rev f)).1 = Γ.rev (foldE h₁ h₂ f).1 := by
  by_cases hf : f = e₂
  · simp [hf]
  by_cases hf' : f = Γ.rev e₂
  · simp [hf']
  rw [foldE_of_ne h₁ h₂ hf hf', foldE_of_ne h₁ h₂ (by grind [rev_rev]) (by grind [rev_injective])]

variable {Γ} in
/-- The folding map of two parallel darts `e₁ ≠ e₂`, where `e₁` is not the reverse of `e₂`: it sends
`e₂` to `e₁`, the reverse of `e₂` to the reverse of `e₁`, and is the identity on the vertices and on
the other darts. -/
noncomputable def deleteEdgeHom {e₁ e₂ : Γ.E} (h₁ : e₁ ≠ e₂) (h₂ : e₁ ≠ Γ.rev e₂)
    (hsrc : Γ.src e₁ = Γ.src e₂) (htgt : Γ.tgt e₁ = Γ.tgt e₂) : Γ.Hom (Γ.deleteEdge e₂) where
  mapV := id
  mapE := foldE h₁ h₂
  map_src f := by
    by_cases hf : f = e₂ <;> by_cases hf' : f = Γ.rev e₂ <;> simp_all [Γ.rev_ne]
  map_rev f := Subtype.ext (foldE_rev_apply h₁ h₂ f)

section deleteEdgeHom

variable {Γ} {e₁ e₂ : Γ.E} (h₁ : e₁ ≠ e₂) (h₂ : e₁ ≠ Γ.rev e₂) (hsrc : Γ.src e₁ = Γ.src e₂)
  (htgt : Γ.tgt e₁ = Γ.tgt e₂)

/-- The folding map of two parallel darts is the identity on vertices. -/
@[simp] theorem deleteEdgeHom_mapV (a : Γ.V) : (deleteEdgeHom h₁ h₂ hsrc htgt).mapV a = a :=
  (rfl)

/-- The dart map of the folding map of two parallel darts is the dart map `foldE` of the fold. -/
theorem deleteEdgeHom_mapE (f : Γ.E) : (deleteEdgeHom h₁ h₂ hsrc htgt).mapE f = foldE h₁ h₂ f :=
  (rfl)

-- With `Hom.map_rev`, `simp` also computes the image of the reverse of `e₂`.
/-- The folding map of two parallel darts sends `e₂` to `e₁`. -/
@[simp] theorem deleteEdgeHom_mapE_self : ((deleteEdgeHom h₁ h₂ hsrc htgt).mapE e₂).1 = e₁ :=
  foldE_self h₁ h₂

/-- The folding map of two parallel darts fixes every dart other than `e₂` and its reverse. -/
@[simp] theorem deleteEdgeHom_mapE_val (f : (Γ.deleteEdge e₂).E) :
    (deleteEdgeHom h₁ h₂ hsrc htgt).mapE f.1 = f :=
  foldE_val h₁ h₂ f

end deleteEdgeHom

variable {Γ} in
/-- Deleting one of two distinct parallel darts of a connected graph, with its reverse, leaves a
connected graph. -/
theorem Connected.deleteEdge (hΓ : Γ.Connected) {e₁ e₂ : Γ.E} (h : e₁ ≠ e₂)
    (hsrc : Γ.src e₁ = Γ.src e₂) (htgt : Γ.tgt e₁ = Γ.tgt e₂) : (Γ.deleteEdge e₂).Connected := by
  by_cases h₂ : e₁ = Γ.rev e₂
  · -- Here `e₂` is a loop, and dropping its darts from a path of `Γ` gives a path of the deletion.
    have hloop : Γ.src e₂ = Γ.tgt e₂ := by simp_all
    obtain ⟨hV, hpre⟩ := (connected_iff Γ).1 hΓ
    refine (connected_iff _).2 ⟨hV, (preconnected_iff _).2 fun a b => ?_⟩
    obtain ⟨p⟩ := (preconnected_iff Γ).1 hpre a b
    induction p with
    | nil => exact ⟨.nil⟩
    | cons _ f ih =>
      obtain ⟨q⟩ := ih
      by_cases hf : f.1 = e₂ ∨ f.1 = Γ.rev e₂
      · have hf' : Γ.src f.1 = Γ.tgt f.1 := by
          rcases hf with hf | hf <;> simp [hf, hloop]
        obtain rfl := f.2.1.symm.trans (hf'.trans f.2.2)
        exact ⟨q⟩
      · exact ⟨q.cons ⟨⟨f.1, not_or.1 hf⟩, f.2⟩⟩
  · exact (deleteEdgeHom h h₂ hsrc htgt).connected_of_surjective Function.surjective_id hΓ

/-- Deleting a geometric edge lowers the number of geometric edges by one. -/
theorem card_geomEdge_deleteEdge [Finite Γ.GeomEdge] (e : Γ.E) :
    Nat.card (Γ.deleteEdge e).GeomEdge + 1 = Nat.card Γ.GeomEdge :=
  card_geomEdge_add_one Γ e Subtype.val Subtype.val_injective (fun _ => rfl) fun f =>
    ⟨by rintro ⟨g, rfl⟩; exact g.2, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩

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

/-- The fold of two darts `e₁`, `e₂` with distinct terminal vertices: the graph obtained from `Γ`
by deleting the dart `e₂`, its reverse and the vertex `t(e₂)`, every dart of `Γ` at `t(e₂)` being
attached to `t(e₁)`. -/
@[expose] noncomputable def fold (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) : SerreGraph.{u, v} where
  V := {a : Γ.V // a ≠ Γ.tgt e₂}
  E := {f : Γ.E // f ≠ e₂ ∧ f ≠ Γ.rev e₂}
  src f := Γ.foldV e₁ e₂ h (Γ.src f.1)
  rev f := ⟨Γ.rev f.1, fun hf => f.2.2 ((Γ.rev_rev f.1).symm.trans (congrArg Γ.rev hf)),
    fun hf => f.2.1 (Γ.rev_injective hf)⟩
  rev_rev f := Subtype.ext (Γ.rev_rev f.1)
  rev_ne f hf := Γ.rev_ne f.1 (congrArg Subtype.val hf)

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
  mapE := foldE (ne_of_apply_ne Γ.tgt h) (ne_rev_of_src_eq_of_tgt_ne hsrc h)
  map_src f := by
    -- `fold_src` does not rewrite here: `foldE _ _ f` is typed as a subtype of `Γ.E` rather than
    -- as a dart of the fold, so the source in the fold is unfolded by hand.
    change Γ.foldV e₁ e₂ h (Γ.src (foldE _ _ f).1) = Γ.foldV e₁ e₂ h (Γ.src f)
    by_cases hf : f = e₂ <;> by_cases hf' : f = Γ.rev e₂ <;> simp_all [Γ.rev_ne]
  map_rev f := Subtype.ext (foldE_rev_apply _ _ f)

section foldHom

variable {Γ} {e₁ e₂ : Γ.E} (h : Γ.tgt e₁ ≠ Γ.tgt e₂) (hsrc : Γ.src e₁ = Γ.src e₂)

/-- The vertex map of the folding map is the vertex map `foldV` of the fold. -/
@[simp] theorem foldHom_mapV (a : Γ.V) : (foldHom h hsrc).mapV a = Γ.foldV e₁ e₂ h a :=
  (rfl)

/-- The dart map of the folding map is the dart map `foldE` of the fold. -/
theorem foldHom_mapE (f : Γ.E) : (foldHom h hsrc).mapE f =
    foldE (ne_of_apply_ne Γ.tgt h) (ne_rev_of_src_eq_of_tgt_ne hsrc h) f :=
  (rfl)

-- With `Hom.map_rev`, `simp` also computes the image of the reverse of `e₂`.
/-- The folding map sends `e₂` to `e₁`. -/
@[simp] theorem foldHom_mapE_self : ((foldHom h hsrc).mapE e₂).1 = e₁ :=
  foldE_self (ne_of_apply_ne Γ.tgt h) (ne_rev_of_src_eq_of_tgt_ne hsrc h)

/-- The folding map fixes every dart other than `e₂` and its reverse. -/
@[simp] theorem foldHom_mapE_val (f : (Γ.fold e₁ e₂ h).E) : (foldHom h hsrc).mapE f.1 = f :=
  foldE_val (ne_of_apply_ne Γ.tgt h) (ne_rev_of_src_eq_of_tgt_ne hsrc h) f

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
one. -/
theorem card_geomEdge_fold [Finite Γ.GeomEdge] (e₁ e₂ : Γ.E) (h : Γ.tgt e₁ ≠ Γ.tgt e₂) :
    Nat.card (Γ.fold e₁ e₂ h).GeomEdge + 1 = Nat.card Γ.GeomEdge :=
  card_geomEdge_add_one Γ e₂ Subtype.val Subtype.val_injective (fun _ => rfl) fun f =>
    ⟨by rintro ⟨g, rfl⟩; exact g.2, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩

end SerreGraph

end TauCeti
