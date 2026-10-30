/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Basic

/-!
# Folding a pair of equally labelled darts

A Stallings fold identifies two darts with the same source and label, their reverses, and
their target vertices. The resulting labelled graph comes with a surjective morphism from
the original graph. This construction also handles loop darts and parallel darts.

The quotient follows I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free
groups*, §2, Definition 2.4 and Lemma 2.5.
-/

public section

namespace TauCeti.StallingsGraph

universe u v w

variable {α : Type u} (S : StallingsGraph.{u, v, w} α)
variable (f₁ f₂ : S.graph.E)
variable (hsrc : S.graph.src f₁ = S.graph.src f₂)
variable (hlabel : S.label f₁ = S.label f₂)

private def vertexRel (x y : S.graph.V) : Prop :=
  x = S.graph.tgt f₁ ∧ y = S.graph.tgt f₂

private def dartRel (e e' : S.graph.E) : Prop :=
  (e = f₁ ∧ e' = f₂) ∨
    (e = S.graph.rev f₁ ∧ e' = S.graph.rev f₂)

private theorem vertex_sound :
    Quot.mk (vertexRel S f₁ f₂) (S.graph.tgt f₁) =
      Quot.mk (vertexRel S f₁ f₂) (S.graph.tgt f₂) :=
  Quot.sound ⟨rfl, rfl⟩

private theorem dart_sound :
    Quot.mk (dartRel S f₁ f₂) f₁ = Quot.mk (dartRel S f₁ f₂) f₂ :=
  Quot.sound (Or.inl ⟨rfl, rfl⟩)

private def foldSrc : Quot (dartRel S f₁ f₂) → Quot (vertexRel S f₁ f₂) :=
  Quot.lift (fun e => Quot.mk _ (S.graph.src e)) (by
    intro e e' h
    rcases h with ⟨he, he'⟩ | ⟨he, he'⟩
    · rw [he, he']
      exact congrArg (Quot.mk (vertexRel S f₁ f₂)) hsrc
    · rw [he, he']
      simpa only [S.graph.src_rev] using vertex_sound S f₁ f₂)

private def foldRev : Quot (dartRel S f₁ f₂) → Quot (dartRel S f₁ f₂) :=
  Quot.lift (fun e => Quot.mk _ (S.graph.rev e)) (by
    intro e e' h
    rcases h with ⟨he, he'⟩ | ⟨he, he'⟩
    · rw [he, he']
      exact Quot.sound (Or.inr ⟨rfl, rfl⟩)
    · rw [he, he']
      simpa only [S.graph.rev_rev] using dart_sound S f₁ f₂)

private def foldLabel : Quot (dartRel S f₁ f₂) → α × Bool :=
  Quot.lift S.label (by
    intro e e' h
    rcases h with ⟨he, he'⟩ | ⟨he, he'⟩
    · rw [he, he']
      exact hlabel
    · rw [he, he']
      simpa only [S.label_rev] using
        congrArg (fun x : α × Bool => (x.1, !x.2)) hlabel)

/-- The labelled graph obtained by identifying two equally labelled outgoing darts. -/
def foldAt : StallingsGraph α where
  graph := {
    V := Quot (vertexRel S f₁ f₂)
    E := Quot (dartRel S f₁ f₂)
    src := foldSrc S f₁ f₂ hsrc
    rev := foldRev S f₁ f₂
    rev_rev := by
      intro e
      induction e using Quot.ind with
      | _ e => simp only [foldRev, S.graph.rev_rev]
    rev_ne := by
      intro e he
      induction e using Quot.ind with
      | _ e =>
        have hl := congrArg (foldLabel S f₁ f₂ hlabel) he
        simp only [foldLabel, foldRev, S.label_rev] at hl
        have hb := congrArg Prod.snd hl
        cases h : (S.label e).2 <;> simp [h] at hb }
  base := Quot.mk _ S.base
  label := foldLabel S f₁ f₂ hlabel
  label_rev := by
    intro e
    induction e using Quot.ind with
    | _ e => exact S.label_rev e

/-- The canonical label-preserving morphism into a Stallings fold. -/
def foldHom : S.Hom (S.foldAt f₁ f₂ hsrc hlabel) where
  graphHom := {
    mapV := Quot.mk _
    mapE := Quot.mk _
    map_src := by intro e; rfl
    map_rev := by intro e; rfl }
  map_base := rfl
  map_label := by intro e; rfl

/-- Two vertices have the same image exactly when the fold relation identifies them. -/
theorem foldHom_mapV_eq_iff (x y : S.graph.V) :
    (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapV x =
      (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapV y ↔
      Relation.EqvGen (fun a b => a = S.graph.tgt f₁ ∧ b = S.graph.tgt f₂) x y := by
  -- The vertex map of foldHom reduces to Quot.mk for the vertex relation.
  change Quot.mk (vertexRel S f₁ f₂) x = Quot.mk (vertexRel S f₁ f₂) y ↔ _
  exact ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

/-- Two darts have the same image exactly when the fold relation identifies them. -/
theorem foldHom_mapE_eq_iff (e e' : S.graph.E) :
    (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapE e =
      (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapE e' ↔
      Relation.EqvGen (fun a b =>
        (a = f₁ ∧ b = f₂) ∨
          (a = S.graph.rev f₁ ∧ b = S.graph.rev f₂)) e e' := by
  -- The dart map of foldHom reduces to Quot.mk for the dart relation.
  change Quot.mk (dartRel S f₁ f₂) e = Quot.mk (dartRel S f₁ f₂) e' ↔ _
  exact ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

/-- The two selected darts have the same image in the fold. -/
theorem foldHom_mapE_eq :
    (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapE f₁ =
      (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapE f₂ :=
  dart_sound S f₁ f₂

/-- The target vertices of the folded darts have the same image. -/
theorem foldHom_mapV_tgt_eq :
    (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapV (S.graph.tgt f₁) =
      (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapV (S.graph.tgt f₂) :=
  vertex_sound S f₁ f₂

/-- Every vertex of the fold comes from the original graph. -/
theorem foldHom_mapV_surjective :
    Function.Surjective (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapV :=
  Quot.mk_surjective

/-- Every dart of the fold comes from the original graph. -/
theorem foldHom_mapE_surjective :
    Function.Surjective (S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapE :=
  Quot.mk_surjective

/-- A labelled morphism that identifies the folded darts factors through their fold. -/
def foldLift {T : StallingsGraph α} (g : S.Hom T)
    (h : g.graphHom.mapE f₁ = g.graphHom.mapE f₂) :
    (S.foldAt f₁ f₂ hsrc hlabel).Hom T where
  graphHom := {
    mapV := Quot.lift g.graphHom.mapV (by
      intro x y hxy
      rcases hxy with ⟨hx, hy⟩
      rw [hx, hy]
      simpa only [g.graphHom.map_tgt] using
        congrArg T.graph.tgt h)
    mapE := Quot.lift g.graphHom.mapE (by
      intro e e' he
      rcases he with ⟨he, he'⟩ | ⟨he, he'⟩
      · rw [he, he']
        exact h
      · rw [he, he']
        simpa only [g.graphHom.map_rev] using
          congrArg T.graph.rev h)
    map_src := by
      intro e
      induction e using Quot.ind with
      | _ e => exact g.graphHom.map_src e
    map_rev := by
      intro e
      induction e using Quot.ind with
      | _ e => exact g.graphHom.map_rev e }
  map_base := g.map_base
  map_label := by
    intro e
    induction e using Quot.ind with
    | _ e => exact g.map_label e

/-- The lifted vertex map computes on vertices from the original graph. -/
@[simp] theorem foldLift_mapV_foldHom {T : StallingsGraph α} (g : S.Hom T)
    (h : g.graphHom.mapE f₁ = g.graphHom.mapE f₂) (x : S.graph.V) :
    (S.foldLift f₁ f₂ hsrc hlabel g h).graphHom.mapV
      ((S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapV x) = g.graphHom.mapV x := by
  -- Quot.lift computes on the vertex representative supplied by Quot.mk.
  unfold foldLift foldHom foldAt
  rfl

/-- The lifted dart map computes on darts from the original graph. -/
@[simp] theorem foldLift_mapE_foldHom {T : StallingsGraph α} (g : S.Hom T)
    (h : g.graphHom.mapE f₁ = g.graphHom.mapE f₂) (e : S.graph.E) :
    (S.foldLift f₁ f₂ hsrc hlabel g h).graphHom.mapE
      ((S.foldHom f₁ f₂ hsrc hlabel).graphHom.mapE e) = g.graphHom.mapE e := by
  -- Quot.lift computes on the dart representative supplied by Quot.mk.
  unfold foldLift foldHom foldAt
  rfl

/-- Composing the fold quotient with its descended morphism recovers the original map. -/
@[simp] theorem foldLift_comp_foldHom {T : StallingsGraph α} (g : S.Hom T)
    (h : g.graphHom.mapE f₁ = g.graphHom.mapE f₂) :
    Hom.comp (S.foldLift f₁ f₂ hsrc hlabel g h) (S.foldHom f₁ f₂ hsrc hlabel) = g := by
  apply Hom.ext
  apply SerreGraph.Hom.ext
  · funext x
    simp
  · funext e
    simp

/-- Morphisms out of a fold agree if they agree after composition with its quotient map. -/
theorem foldHom_ext {T : StallingsGraph α}
    {k k' : (S.foldAt f₁ f₂ hsrc hlabel).Hom T}
    (hkk : Hom.comp k (S.foldHom f₁ f₂ hsrc hlabel) =
      Hom.comp k' (S.foldHom f₁ f₂ hsrc hlabel)) : k = k' := by
  apply Hom.ext
  apply SerreGraph.Hom.ext
  · funext x
    obtain ⟨y, rfl⟩ := S.foldHom_mapV_surjective f₁ f₂ hsrc hlabel x
    simpa only [Hom.comp_graphHom, SerreGraph.Hom.comp_mapV,
      Function.comp_apply] using congrArg (fun m : S.Hom T => m.graphHom.mapV y) hkk
  · funext e
    obtain ⟨d, rfl⟩ := S.foldHom_mapE_surjective f₁ f₂ hsrc hlabel e
    simpa only [Hom.comp_graphHom, SerreGraph.Hom.comp_mapE,
      Function.comp_apply] using congrArg (fun m : S.Hom T => m.graphHom.mapE d) hkk

/-- The lift is the unique morphism whose composite with the quotient map is `g`. -/
theorem foldLift_unique {T : StallingsGraph α} (g : S.Hom T)
    (h : g.graphHom.mapE f₁ = g.graphHom.mapE f₂)
    (k : (S.foldAt f₁ f₂ hsrc hlabel).Hom T)
    (hk : Hom.comp k (S.foldHom f₁ f₂ hsrc hlabel) = g) :
    k = S.foldLift f₁ f₂ hsrc hlabel g h :=
  S.foldHom_ext f₁ f₂ hsrc hlabel
    (hk.trans (S.foldLift_comp_foldHom f₁ f₂ hsrc hlabel g h).symm)

/-- A fold of a graph with finitely many vertices has finitely many vertices. -/
instance [Finite S.graph.V] : Finite (S.foldAt f₁ f₂ hsrc hlabel).graph.V :=
  Finite.of_surjective _ (S.foldHom_mapV_surjective f₁ f₂ hsrc hlabel)

/-- A fold of a graph with finitely many darts has finitely many darts. -/
instance [Finite S.graph.E] : Finite (S.foldAt f₁ f₂ hsrc hlabel).graph.E :=
  Finite.of_surjective _ (S.foldHom_mapE_surjective f₁ f₂ hsrc hlabel)

end TauCeti.StallingsGraph
