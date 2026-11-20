/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Subdivisions of multispan diagrams

Copies of chamber and face objects, with identity faces joining chamber copies,
form a new incidence category. Its projection forgets the copies and sends
identity faces to their original chamber. Any coefficient category supports the
refined index and its comparison with the original diagram pulled back along
this projection. The identity-face relation records the graph used for descent.

Adapted from `Mei/CategoryTheory/Limits/Multispan/Subdivision.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
The original source credits Codex and carries the notice
Copyright (c) 2026 Mei contributors. All rights reserved.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.MultispanShape

universe w₁ w₂ w₃

/-- Copies of chambers and faces, with additional identity faces inside each chamber. -/
structure Subdivision (J : MultispanShape) where
  /-- Copies of each original chamber. -/
  chambers : J.R → Type w₁
  /-- Copies of each original face. -/
  faces : J.L → Type w₂
  /-- The source chamber copy incident to a copied original face. -/
  source : ∀ b, faces b → chambers (J.fst b)
  /-- The target chamber copy incident to a copied original face. -/
  target : ∀ b, faces b → chambers (J.snd b)
  /-- The new identity faces inside each original chamber. -/
  edges : J.R → Type w₃
  /-- Source of an identity face. -/
  edgeSource : ∀ j, edges j → chambers j
  /-- Target of an identity face. -/
  edgeTarget : ∀ j, edges j → chambers j

namespace Subdivision

variable {J : MultispanShape} (D : Subdivision J)

/-- The refined incidence shape, retaining copied faces and added identity faces. -/
abbrev shape : MultispanShape where
  L := (Σ b, D.faces b) ⊕ (Σ j, D.edges j)
  R := Σ j, D.chambers j
  fst
    | .inl ⟨b, c⟩ => ⟨J.fst b, D.source b c⟩
    | .inr ⟨j, e⟩ => ⟨j, D.edgeSource j e⟩
  snd
    | .inl ⟨b, c⟩ => ⟨J.snd b, D.target b c⟩
    | .inr ⟨j, e⟩ => ⟨j, D.edgeTarget j e⟩

/-- The first endpoint of a copied face is its chosen source chamber copy. -/
@[simp] theorem shape_fst_inl (b : J.L) (a : D.faces b) :
    D.shape.fst (.inl ⟨b, a⟩) = ⟨J.fst b, D.source b a⟩ := (rfl)

/-- The second endpoint of a copied face is its chosen target chamber copy. -/
@[simp] theorem shape_snd_inl (b : J.L) (a : D.faces b) :
    D.shape.snd (.inl ⟨b, a⟩) = ⟨J.snd b, D.target b a⟩ := (rfl)

/-- The first endpoint of an identity face is its source copy. -/
@[simp] theorem shape_fst_inr (j : J.R) (e : D.edges j) :
    D.shape.fst (.inr ⟨j, e⟩) = ⟨j, D.edgeSource j e⟩ := (rfl)

/-- The second endpoint of an identity face is its target copy. -/
@[simp] theorem shape_snd_inr (j : J.R) (e : D.edges j) :
    D.shape.snd (.inr ⟨j, e⟩) = ⟨j, D.edgeTarget j e⟩ := (rfl)

/-- Forget the copied indices and send each identity face to its old chamber.
The body is exposed so pulled-back coefficient objects have their original carriers. -/
@[expose]
def projection : WalkingMultispan D.shape ⥤ WalkingMultispan J :=
  MultispanIndex.multispan
    { left
        | .inl ⟨b, _⟩ => .left b
        | .inr ⟨j, _⟩ => .right j
      right j := .right j.1
      fst
        | .inl ⟨b, _⟩ => WalkingMultispan.Hom.fst b
        | .inr ⟨_, _⟩ => 𝟙 _
      snd
        | .inl ⟨b, _⟩ => WalkingMultispan.Hom.snd b
        | .inr ⟨_, _⟩ => 𝟙 _ }

/-- A copied face projects to its original face. -/
@[simp] theorem projection_obj_left_inl (b : J.L) (a : D.faces b) :
    D.projection.obj (.left (.inl ⟨b, a⟩)) = .left b := (rfl)

/-- An identity face projects to the original chamber. -/
@[simp] theorem projection_obj_left_inr (j : J.R) (e : D.edges j) :
    D.projection.obj (.left (.inr ⟨j, e⟩)) = .right j := (rfl)

/-- A copied chamber projects to the original chamber. -/
@[simp] theorem projection_obj_right (j : J.R) (a : D.chambers j) :
    D.projection.obj (.right ⟨j, a⟩) = .right j := (rfl)

/-- The first incidence of a copied face projects to the old first incidence. -/
@[simp] theorem projection_map_fst_inl (b : J.L) (a : D.faces b) :
    D.projection.map (WalkingMultispan.Hom.fst (J := D.shape) (.inl ⟨b, a⟩)) =
      eqToHom (D.projection_obj_left_inl b a) ≫ WalkingMultispan.Hom.fst b ≫
        eqToHom (D.projection_obj_right (J.fst b) (D.source b a)).symm := (rfl)

/-- The second incidence of a copied face projects to the old second incidence. -/
@[simp] theorem projection_map_snd_inl (b : J.L) (a : D.faces b) :
    D.projection.map (WalkingMultispan.Hom.snd (J := D.shape) (.inl ⟨b, a⟩)) =
      eqToHom (D.projection_obj_left_inl b a) ≫ WalkingMultispan.Hom.snd b ≫
        eqToHom (D.projection_obj_right (J.snd b) (D.target b a)).symm := (rfl)

/-- The first incidence of an identity face projects to an identity. -/
@[simp] theorem projection_map_fst_inr (j : J.R) (e : D.edges j) :
    D.projection.map (WalkingMultispan.Hom.fst (J := D.shape) (.inr ⟨j, e⟩)) =
      eqToHom ((D.projection_obj_left_inr j e).trans
        (D.projection_obj_right j (D.edgeSource j e)).symm) := (rfl)

/-- The second incidence of an identity face projects to an identity. -/
@[simp] theorem projection_map_snd_inr (j : J.R) (e : D.edges j) :
    D.projection.map (WalkingMultispan.Hom.snd (J := D.shape) (.inr ⟨j, e⟩)) =
      eqToHom ((D.projection_obj_left_inr j e).trans
        (D.projection_obj_right j (D.edgeTarget j e)).symm) := (rfl)

/-- Two copies joined by an identity face, with the displayed orientation. -/
def edgeRel (j : J.R) (a b : D.chambers j) : Prop :=
  ∃ e, D.edgeSource j e = a ∧ D.edgeTarget j e = b

/-- An oriented identity edge witnesses the relation between its endpoint copies. -/
@[simp]
theorem edgeRel_iff (j : J.R) (a b : D.chambers j) :
    D.edgeRel j a b ↔ ∃ e, D.edgeSource j e = a ∧ D.edgeTarget j e = b := Iff.rfl

variable {C : Type*} [Category* C] (I : MultispanIndex J C)

/-- The refined coefficient diagram copies original spans and uses identity spans
at the new internal faces. -/
abbrev index : MultispanIndex D.shape C where
  left
    | .inl ⟨b, _⟩ => I.left b
    | .inr ⟨j, _⟩ => I.right j
  right j := I.right j.1
  fst
    | .inl ⟨b, _⟩ => I.fst b
    | .inr ⟨_, _⟩ => 𝟙 _
  snd
    | .inl ⟨b, _⟩ => I.snd b
    | .inr ⟨_, _⟩ => 𝟙 _

/-- A copied face retains the original face object. -/
@[simp] theorem index_left_inl (b : J.L) (a : D.faces b) :
    (D.index I).left (.inl ⟨b, a⟩) = I.left b := (rfl)

/-- An identity face carries the object of its original chamber. -/
@[simp] theorem index_left_inr (j : J.R) (e : D.edges j) :
    (D.index I).left (.inr ⟨j, e⟩) = I.right j := (rfl)

/-- Copied chamber coefficients are unchanged. -/
@[simp]
theorem index_right (j : J.R) (a : D.chambers j) :
    (D.index I).right ⟨j, a⟩ = I.right j := (rfl)

/-- A copied face has the original source incidence. -/
@[simp]
theorem index_fst_inl (b : J.L) (a : D.faces b) :
    (D.index I).fst (.inl ⟨b, a⟩) = I.fst b := (rfl)

/-- A copied face has the original target incidence. -/
@[simp]
theorem index_snd_inl (b : J.L) (a : D.faces b) :
    (D.index I).snd (.inl ⟨b, a⟩) = I.snd b := (rfl)

/-- An internal identity face has identity source incidence. -/
@[simp]
theorem index_fst_inr (j : J.R) (e : D.edges j) :
    (D.index I).fst (.inr ⟨j, e⟩) = 𝟙 (I.right j) := (rfl)

/-- An internal identity face has identity target incidence. -/
@[simp]
theorem index_snd_inr (j : J.R) (e : D.edges j) :
    (D.index I).snd (.inr ⟨j, e⟩) = 𝟙 (I.right j) := (rfl)

/-- Refined objects agree with their images under the incidence projection. -/
theorem index_multispan_obj (x : WalkingMultispan D.shape) :
    (D.index I).multispan.obj x = (D.projection ⋙ I.multispan).obj x := by
  rcases x with (⟨b, a⟩ | ⟨j, e⟩) | ⟨j, a⟩ <;> rfl

/-- The refined coefficient diagram is the pullback along the incidence projection. -/
def multispanIso : (D.index I).multispan ≅ D.projection ⋙ I.multispan :=
  WalkingMultispan.functorExt
    (fun b => by rcases b with (⟨b, a⟩ | ⟨j, e⟩) <;> exact Iso.refl _)
    (fun j => Iso.refl _)
    (by
      rintro (⟨b, a⟩ | ⟨j, e⟩) <;>
        dsimp [index, projection, MultispanIndex.multispan] <;>
        simp only [← WalkingMultispan.Hom.id_eq_id, Category.id_comp, Category.comp_id])
    (by
      rintro (⟨b, a⟩ | ⟨j, e⟩) <;>
        dsimp [index, projection, MultispanIndex.multispan] <;>
        simp only [← WalkingMultispan.Hom.id_eq_id, Category.id_comp, Category.comp_id])

/-- The comparison to the pullback has identity components after identifying its objects. -/
@[simp] theorem multispanIso_hom_app (x : WalkingMultispan D.shape) :
    (D.multispanIso I).hom.app x = eqToHom (D.index_multispan_obj I x) := by
  rcases x with (⟨b, a⟩ | ⟨j, e⟩) | ⟨j, a⟩ <;> rfl

/-- The inverse comparison has the inverse identity components on the same objects. -/
@[simp] theorem multispanIso_inv_app (x : WalkingMultispan D.shape) :
    (D.multispanIso I).inv.app x = eqToHom (D.index_multispan_obj I x).symm := by
  rcases x with (⟨b, a⟩ | ⟨j, e⟩) | ⟨j, a⟩ <;> rfl

end Subdivision
end CategoryTheory.Limits.MultispanShape
