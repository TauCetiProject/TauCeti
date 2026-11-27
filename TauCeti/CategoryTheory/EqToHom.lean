/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Transporting categorical morphisms along object equalities

This file provides general lemmas for removing and rearranging the conjugations by `eqToHom` that
arise when categorical objects are identified propositionally. They apply in an arbitrary category
and avoid exposing the definitional equality of the objects being transported.

## Main results

* `TauCeti.eqToHom_self_comp`: transporting along an equality of an object with itself, which may
  only be definitional, leaves a composite unchanged.
* `TauCeti.eqToHom_conjugate_cancel`: transporting a morphism and then transporting it back leaves
  it unchanged.
* `TauCeti.eqToHom_conj_conj`: composing two successive endpoint transports agrees with
  transporting directly along the composite equalities.
* `TauCeti.eqToHom_conjugate_eq_id`, `TauCeti.eqToHom_conjugate_eq_comp` and
  `TauCeti.eqToHom_conjugate_add`: transporting an identity, a composite or a sum gives the
  identity, the composite of the transports or the sum of the transports.
* `TauCeti.eqToHom_conjugate_square`: conjugating every edge preserves and reflects commutativity of
  a square.
* `TauCeti.eq_of_eqToHom_conjugate`: two morphisms with equal conjugates are equal.
* `TauCeti.eq_of_heq_id`: two parallel morphisms heterogeneously equal to identities on
  propositionally equal objects are equal.
* `TauCeti.eq_of_heq_conj`: two parallel morphisms heterogeneously equal to heterogeneously equal
  morphisms are equal.
* `TauCeti.eqToHom_conjugate_vertical_square_of_horizontal_square`: commutativity with conjugated
  horizontal edges gives commutativity after moving the conjugations to the vertical edges.
* `TauCeti.eqToHom_eq_iso_hom_map_eqToHom`: transport along an index equality is conjugate, through
  identifications `Y i ≅ F.obj (X i)`, to the image under a functor `F` of the transport.
* `TauCeti.eqToIso_conjugate_trans`: conjugating an isomorphism in two stages by `eqToIso` agrees
  with conjugating along the composite object equalities.
* `CategoryTheory.Functor.map_heq`: a functor sends morphisms which agree up to equalities of their
  endpoints to morphisms which agree in the same way.
* `CategoryTheory.Functor.eqToHom_conjugate_map_conjugate`: transporting a morphism along object
  equalities, applying a functor, and transporting along equalities of the images agrees with
  applying the functor and transporting directly along the composed equalities.
* `CategoryTheory.Functor.map_comp_eqToHom_of_isThin`: on a thin category, the images under a
  functor of two morphisms between equal endpoints agree up to the transports along those
  equalities.
* `CategoryTheory.Functor.map_homOfLE_eq` and `CategoryTheory.Functor.unop_map_homOfLE_eq`: a
  functor out of a preorder sends inequalities with equal endpoints to the same morphism, up to the
  identifications of the endpoints.
* `CategoryTheory.Functor.eqToHom_conjugate_map_eqToHom_conjugate`: transporting `F.map` of a
  conjugated morphism back along the induced object equalities recovers the conjugate of `F.map`.
* `CategoryTheory.Functor.map_comp_eq_of_eqToHom_conjugate`: a commuting triangle of conjugated
  images under a functor `F` after an epimorphism yields equality of the corresponding images under
  `F`.
-/

public section

namespace TauCeti

open CategoryTheory

/-- Composing with `eqToHom h` for `h : Y = Y` does nothing. This is useful when `h` is a proof
between objects that are definitionally equal but not syntactically equal, so that `simp` with
`eqToHom_refl` does not apply. -/
theorem eqToHom_self_comp {C : Type*} [Category* C] {Y Z : C} (h : Y = Y) (f : Y ⟶ Z) :
    eqToHom h ≫ f = f := by simp

/-- Transporting a morphism along object equalities and then back leaves it unchanged. -/
theorem eqToHom_conjugate_cancel {C : Type*} [Category* C] {X X' Y Y' : C}
    (hX : X = X') (hY : Y = Y') (f : X' ⟶ Y') :
    eqToHom hX.symm ≫ (eqToHom hX ≫ f ≫ eqToHom hY.symm) ≫ eqToHom hY = f := by
  subst X'
  subst Y'
  simp

/-- Composing two successive endpoint transports around a morphism `m` agrees with transporting
directly along the composite object equalities. -/
theorem eqToHom_conj_conj {C : Type*} [Category* C] {a b c d e f : C}
    (h₁ : a = b) (h₂ : b = c) (m : c ⟶ d) (h₃ : d = e) (h₄ : e = f) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ m ≫ eqToHom h₃) ≫ eqToHom h₄ =
      eqToHom (h₁.trans h₂) ≫ m ≫ eqToHom (h₃.trans h₄) := by
  subst h₁ h₂ h₃ h₄
  simp

/-- **A transported identity is the identity**: conjugating a morphism equal to `𝟙 Y` by the
object equality `X = Y` gives `𝟙 X`. -/
theorem eqToHom_conjugate_eq_id {C : Type*} [Category* C] {X Y : C} (h : X = Y)
    (f : Y ⟶ Y) (hf : f = 𝟙 Y) : eqToHom h ≫ f ≫ eqToHom h.symm = 𝟙 X := by
  subst h
  simp [hf]

/-- **Transport distributes over composition**: if `f = g ≫ h`, the transport of `f` is the
composite of the transports of `g` and `h`. -/
theorem eqToHom_conjugate_eq_comp {C : Type*} [Category* C] {X X' Y Y' Z Z' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (f : X' ⟶ Z') (g : X' ⟶ Y') (h : Y' ⟶ Z')
    (hf : f = g ≫ h) :
    eqToHom hX ≫ f ≫ eqToHom hZ.symm =
      (eqToHom hX ≫ g ≫ eqToHom hY.symm) ≫ eqToHom hY ≫ h ≫ eqToHom hZ.symm := by
  subst hX
  subst hY
  subst hZ
  simp [hf]

/-- **Transport is additive**: in a preadditive category, if `f = g + h`, the transport of `f` is
the sum of the transports of `g` and `h`. -/
theorem eqToHom_conjugate_add {C : Type*} [Category* C] [Preadditive C] {X X' Y Y' : C}
    (hX : X = X') (hY : Y' = Y) {f g h : X' ⟶ Y'} (hfgh : f = g + h) :
    eqToHom hX ≫ f ≫ eqToHom hY
      = (eqToHom hX ≫ g ≫ eqToHom hY) + (eqToHom hX ≫ h ≫ eqToHom hY) := by
  subst hX
  subst hY
  simp [hfgh]

/-- **Conjugating a commuting square by object equalities leaves it commuting**, and nothing else
becomes commuting that way: the square of transported edges commutes exactly when the original
one does. -/
theorem eqToHom_conjugate_square {C : Type*} [Category* C] {X X' Y Y' Z Z' W W' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (hW : W = W')
    (f : X' ⟶ Y') (g : Y' ⟶ Z') (f' : X' ⟶ W') (g' : W' ⟶ Z') :
    (eqToHom hX ≫ f ≫ eqToHom hY.symm) ≫ eqToHom hY ≫ g ≫ eqToHom hZ.symm =
        (eqToHom hX ≫ f' ≫ eqToHom hW.symm) ≫ eqToHom hW ≫ g' ≫ eqToHom hZ.symm ↔
      f ≫ g = f' ≫ g' := by
  subst hX
  subst hY
  subst hZ
  subst hW
  simp

/-- **Two morphisms conjugated to the same morphism are equal**: conjugating back cancels, by
`TauCeti.eqToHom_conjugate_cancel`, on both sides at once. -/
theorem eq_of_eqToHom_conjugate {C : Type*} [Category* C] {X X' Y Y' : C} (hX : X' = X)
    (hY : Y = Y') {f g : X ⟶ Y}
    (h : eqToHom hX ≫ f ≫ eqToHom hY = eqToHom hX ≫ g ≫ eqToHom hY) : f = g :=
  (eqToHom_conjugate_cancel hX hY.symm f).symm.trans
    ((congrArg (fun u : X' ⟶ Y' ↦ eqToHom hX.symm ≫ u ≫ eqToHom hY.symm) h).trans
      (eqToHom_conjugate_cancel hX hY.symm g))

/-- Two parallel morphisms `f g : X ⟶ Y` are equal if `f ≍ 𝟙 A` and `g ≍ 𝟙 B` for
propositionally equal objects `A = B`. -/
theorem eq_of_heq_id {C : Type*} [Category* C] {X Y A B : C} {f g : X ⟶ Y}
    (hf : f ≍ 𝟙 A) (hg : g ≍ 𝟙 B) (h : A = B) : f = g := by
  subst h
  exact eq_of_heq (hf.trans hg.symm)

/-- Two parallel morphisms `f g : X ⟶ Y` that are heterogeneously equal to morphisms `m` and
`m'` with `m ≍ m'` are equal. -/
theorem eq_of_heq_conj {C : Type*} [Category* C] {X Y A B A' B' : C} {f g : X ⟶ Y}
    {m : A ⟶ B} {m' : A' ⟶ B'} (hf : f ≍ m) (hg : g ≍ m') (hm : m ≍ m') : f = g :=
  eq_of_heq (hf.trans (hm.trans hg.symm))

/-- **A square with conjugated horizontal edges yields a square with conjugated vertical edges.**
The horizontal conjugations cancel from the conclusion, while the vertical edges acquire the
corresponding conjugations. -/
theorem eqToHom_conjugate_vertical_square_of_horizontal_square {C : Type*} [Category* C]
    {A A' B B' D D' E E' : C} (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    (p : A' ⟶ B') (q : E' ⟶ D') (f : B ⟶ D) (g : A ⟶ E)
    (h : (eqToHom hA ≫ p ≫ eqToHom hB.symm) ≫ f = g ≫ eqToHom hE ≫ q ≫ eqToHom hD.symm) :
    p ≫ (eqToHom hB.symm ≫ f ≫ eqToHom hD) = (eqToHom hA.symm ≫ g ≫ eqToHom hE) ≫ q :=
  (eqToHom_conjugate_square hA hB hD hE p _ _ q).mp (by simpa using h)

/-- **Transport along an index equality commutes with identifications through a functor**: given
families `X` in `C` and `Y` in `D` with isomorphisms `e i : Y i ≅ F.obj (X i)`, the transport
`Y i ⟶ Y j` along `i = j` is the conjugate by `e` of the image under `F` of the transport
`X i ⟶ X j`. -/
theorem eqToHom_eq_iso_hom_map_eqToHom {ι C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X : ι → C} {Y : ι → D} (e : ∀ i, Y i ≅ F.obj (X i)) {i j : ι} (h : i = j) :
    eqToHom (congrArg Y h) = (e i).hom ≫ F.map (eqToHom (congrArg X h)) ≫ (e j).inv := by
  subst h
  simp

/-- **Two-stage transport of an isomorphism**: conjugating `e : Y ≅ Z` by `eqToIso` along
`X = Y` and `Z = V`, and then along `W = X` and `V = U`, agrees with conjugating along the
composite equalities `W = Y` and `Z = U`. -/
theorem eqToIso_conjugate_trans {C : Type*} [Category* C] {U V W X Y Z : C}
    (h₁ : W = X) (h₂ : X = Y) (e : Y ≅ Z) (h₃ : Z = V) (h₄ : V = U) :
    eqToIso (h₁.trans h₂) ≪≫ e ≪≫ eqToIso (h₃.trans h₄) =
      eqToIso h₁ ≪≫ (eqToIso h₂ ≪≫ e ≪≫ eqToIso h₃) ≪≫ eqToIso h₄ := by
  subst h₁ h₂ h₃ h₄
  simp

end TauCeti

namespace CategoryTheory.Functor

/-- A functor sends morphisms which agree up to equalities of their endpoints to morphisms which
agree in the same way. -/
theorem map_heq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X Y X' Y' : C}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (hX : X = X') (hY : Y = Y') (h : f ≍ f') :
    F.map f ≍ F.map f' := by
  subst hX hY
  rw [eq_of_heq h]

/-- Transporting a morphism along object equalities, applying a functor `F`, and transporting along
equalities of the images agrees with applying `F` and transporting directly along the composed
equalities. -/
theorem eqToHom_conjugate_map_conjugate {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X X' Y Y' : C} {A B : D} (hX : X = X') (hY : Y = Y')
    (hA : A = F.obj X) (hB : B = F.obj Y) (f : X' ⟶ Y') :
    eqToHom hA ≫ F.map (eqToHom hX ≫ f ≫ eqToHom hY.symm) ≫ eqToHom hB.symm =
      eqToHom (hA.trans (congrArg F.obj hX)) ≫ F.map f ≫
        eqToHom (hB.trans (congrArg F.obj hY)).symm := by
  subst hX hY hA hB
  simp

/-- On a thin category, such as a preorder, the images under a functor `F` of two morphisms
`f : X ⟶ Y` and `g : X' ⟶ Y'` between equal endpoints agree up to the transports along those
equalities, since `f` and `g` agree up to the same transports. -/
theorem map_comp_eqToHom_of_isThin {C D : Type*} [Category* C] [Category* D] [Quiver.IsThin C]
    (F : C ⥤ D) {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y') :
    F.map f ≫ eqToHom (congrArg F.obj hY) = eqToHom (congrArg F.obj hX) ≫ F.map g := by
  subst hX hY
  simp [Subsingleton.elim f g]

/-- A functor out of a preorder sends inequalities with equal endpoints to the same morphism, up to
the identifications of the endpoints. -/
theorem map_homOfLE_eq {α D : Type*} [Preorder α] [Category* D] (G : α ⥤ D) {a a' b b' : α}
    (ha : a = a') (hb : b = b') (h : a ≤ b) :
    G.map (homOfLE h) =
      eqToHom (congrArg G.obj ha) ≫ G.map (homOfLE (ha ▸ hb ▸ h)) ≫
        eqToHom (congrArg G.obj hb).symm := by
  subst ha hb
  simp

/-- The variant of `CategoryTheory.Functor.map_homOfLE_eq` for the opposites of the morphisms given
by a functor `α ⥤ Dᵒᵖ`. -/
theorem unop_map_homOfLE_eq {α D : Type*} [Preorder α] [Category* D] (G : α ⥤ Dᵒᵖ)
    {a a' b b' : α} (ha : a = a') (hb : b = b') (h : a ≤ b) :
    (G.map (homOfLE h)).unop =
      eqToHom (congrArg (fun j ↦ Opposite.unop (G.obj j)) hb) ≫
        (G.map (homOfLE (ha ▸ hb ▸ h))).unop ≫
          eqToHom (congrArg (fun j ↦ Opposite.unop (G.obj j)) ha).symm := by
  subst ha hb
  simp

/-- Transporting `F.map` of a conjugated morphism back along the induced object equalities
recovers the conjugate of `F.map u`. -/
theorem eqToHom_conjugate_map_eqToHom_conjugate {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A₁ A₂ B₁ B₂ : C} {P Q : D}
    (hA : A₁ = A₂) (hB : B₁ = B₂) (hP : P = F.obj A₁) (hQ : Q = F.obj B₁)
    (hP' : P = F.obj A₂) (hQ' : Q = F.obj B₂) (u : A₁ ⟶ B₁) :
    eqToHom hP' ≫ F.map (eqToHom hA.symm ≫ u ≫ eqToHom hB) ≫ eqToHom hQ'.symm =
      eqToHom hP ≫ F.map u ≫ eqToHom hQ.symm := by
  subst hA hB hP hQ
  simp

/-- Given an epimorphism `u : J ⟶ F.obj I` and morphisms whose images under `F` are conjugated
by `eqToHom`s into a commuting triangle `ηB ≫ ψ = ηA`, the functor `F` identifies `eB ≫ f`
with `eA`. -/
theorem map_comp_eq_of_eqToHom_conjugate {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {I B A : C} {J B' A' : D}
    {hB : B' = F.obj B} {hA : F.obj A = A'}
    {u : J ⟶ F.obj I} [Epi u]
    {eB : I ⟶ B} {eA : I ⟶ A} {f : B ⟶ A}
    {ηB : J ⟶ B'} {ηA : J ⟶ A'} {ψ : B' ⟶ A'}
    (hηB : ηB = u ≫ F.map eB ≫ eqToHom hB.symm)
    (hηA : ηA = u ≫ F.map eA ≫ eqToHom hA)
    (hψ : ψ = eqToHom hB ≫ F.map f ≫ eqToHom hA)
    (h : ηB ≫ ψ = ηA) :
    F.map (eB ≫ f) = F.map eA := by
  subst hB hA
  rw [hηB, hηA, hψ] at h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc,
    ← Functor.map_comp] at h
  exact (cancel_epi u).mp h

end CategoryTheory.Functor
