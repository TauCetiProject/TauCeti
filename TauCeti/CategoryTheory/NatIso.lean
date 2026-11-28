/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.NatIso

/-!
# Natural isomorphisms and morphism equality

A general lemma complementing Mathlib's `CategoryTheory.NatIso.naturality_1` and
`CategoryTheory.NatIso.naturality_2`: naturally isomorphic functors identify the same pairs of
parallel morphisms.

## Main results

* `CategoryTheory.NatIso.map_eq_iff`: for a natural isomorphism `e : F ≅ G`, `F.map f = F.map g`
  holds if and only if `G.map f = G.map g`.
* `CategoryTheory.NatIso.inv_app_of_hom_app` and `CategoryTheory.NatIso.inv_app_eqToHom`: compute
  the inverse component `e.inv.app X` from an identification of `e.hom.app X`.
* `CategoryTheory.NatIso.eq_of_hom_app_eqToHom` and
  `CategoryTheory.NatIso.eq_eqToIso_of_hom_app_eqToHom`: natural isomorphisms whose components
  are all `eqToHom`s agree (and equal `eqToIso`).
* `CategoryTheory.NatIso.whiskerRight_leftUnitor_eq_eqToIso_of_hom_app_eqToHom`,
  `CategoryTheory.NatIso.whiskerLeft_rightUnitor_eq_eqToIso_of_hom_app_eqToHom`, and
  `CategoryTheory.NatIso.whiskerRight_associator_eq_whiskerLeft_of_hom_app_eqToHom`: unit and
  associativity coherence laws for natural isomorphisms whose components are all `eqToHom`s.
-/

public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.NatIso

/-- Naturally isomorphic functors identify the same pairs of parallel morphisms. -/
theorem map_eq_iff {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : C} {f g : X ⟶ Y} :
    F.map f = F.map g ↔ G.map f = G.map g :=
  ⟨fun h ↦ by rw [← NatIso.naturality_1 e, ← NatIso.naturality_1 e, h],
   fun h ↦ by rw [← NatIso.naturality_2 e, ← NatIso.naturality_2 e, h]⟩

/-- If the `hom` component of a natural isomorphism `e` at `X` equals `i.hom`, then its `inv`
component at `X` equals `i.inv`. -/
theorem inv_app_of_hom_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : F ≅ G) (X : C) (i : F.obj X ≅ G.obj X)
    (h : e.hom.app X = i.hom) : e.inv.app X = i.inv :=
  congrArg Iso.inv (Iso.ext h : e.app X = i)

/-- If the `hom` component of a natural isomorphism `e` at `X` is `eqToHom h`, then its `inv`
component at `X` is `eqToHom h.symm`. -/
theorem inv_app_eqToHom {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : F ≅ G) (X : C) {h : F.obj X = G.obj X}
    (he : e.hom.app X = eqToHom h) : e.inv.app X = eqToHom h.symm :=
  (inv_app_of_hom_app e X (eqToIso h) he).trans (eqToIso.inv h)

/-- Two natural isomorphisms `e₁ e₂ : F ≅ G` whose components are both `eqToHom`s are equal. -/
theorem eq_of_hom_app_eqToHom {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F G : C ⥤ D} {e₁ e₂ : F ≅ G}
    (h₁ : ∀ X : C, ∃ p : F.obj X = G.obj X, e₁.hom.app X = eqToHom p)
    (h₂ : ∀ X : C, ∃ p : F.obj X = G.obj X, e₂.hom.app X = eqToHom p) :
    e₁ = e₂ := by
  ext X
  obtain ⟨p₁, hp₁⟩ := h₁ X
  obtain ⟨p₂, hp₂⟩ := h₂ X
  rw [hp₁, hp₂]

/-- A natural isomorphism `e : F ≅ G` between equal functors `h : F = G` whose components are
all `eqToHom`s equals `eqToIso h`. -/
theorem eq_eqToIso_of_hom_app_eqToHom {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F G : C ⥤ D} (e : F ≅ G) (h : F = G)
    (he : ∀ X : C, ∃ p : F.obj X = G.obj X, e.hom.app X = eqToHom p) :
    e = eqToIso h :=
  eq_of_hom_app_eqToHom he fun X ↦ ⟨Functor.congr_obj h X, by rw [eqToIso.hom, eqToHom_app]⟩

/-- Left unit coherence for natural isomorphisms whose components are all `eqToHom`s. -/
theorem whiskerRight_leftUnitor_eq_eqToIso_of_hom_app_eqToHom
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F : C ⥤ D} {I : C ⥤ C} {G : C ⥤ D} (e₁ : F ≅ I ⋙ G) (e₂ : I ≅ 𝟭 C) (h : F = G)
    (he₁ : ∀ X : C, ∃ p, e₁.hom.app X = eqToHom p)
    (he₂ : ∀ X : C, ∃ p, e₂.hom.app X = eqToHom p) :
    e₁ ≪≫ Functor.isoWhiskerRight e₂ G ≪≫ Functor.leftUnitor G = eqToIso h :=
  eq_eqToIso_of_hom_app_eqToHom _ _ fun X ↦
    have ⟨p₁, hp₁⟩ := he₁ X; have ⟨p₂, hp₂⟩ := he₂ X
    ⟨p₁.trans (congrArg G.obj p₂), by simp [hp₁, hp₂, eqToHom_map]⟩

/-- Right unit coherence for natural isomorphisms whose components are all `eqToHom`s. -/
theorem whiskerLeft_rightUnitor_eq_eqToIso_of_hom_app_eqToHom
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} {I : D ⥤ D} (e₁ : F ≅ G ⋙ I) (e₂ : I ≅ 𝟭 D) (h : F = G)
    (he₁ : ∀ X : C, ∃ p, e₁.hom.app X = eqToHom p)
    (he₂ : ∀ Y : D, ∃ p, e₂.hom.app Y = eqToHom p) :
    e₁ ≪≫ Functor.isoWhiskerLeft G e₂ ≪≫ Functor.rightUnitor G = eqToIso h :=
  eq_eqToIso_of_hom_app_eqToHom _ _ fun X ↦
    have ⟨p₁, hp₁⟩ := he₁ X; have ⟨p₂, hp₂⟩ := he₂ (G.obj X)
    ⟨p₁.trans p₂, by simp [hp₁, hp₂]⟩

/-- Associativity coherence for natural isomorphisms whose components are all `eqToHom`s. -/
theorem whiskerRight_associator_eq_whiskerLeft_of_hom_app_eqToHom
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {K : Type u₄} [Category.{v₄} K]
    {FGH FGH' : C ⥤ K} {FG : C ⥤ E} {GH : D ⥤ K} {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ K}
    (e₁ : FGH ≅ FG ⋙ H) (e₂ : FG ≅ F ⋙ G) (e₃ : FGH' ≅ F ⋙ GH) (e₄ : GH ≅ G ⋙ H)
    (h : FGH = FGH')
    (he₁ : ∀ X : C, ∃ p, e₁.hom.app X = eqToHom p)
    (he₂ : ∀ X : C, ∃ p, e₂.hom.app X = eqToHom p)
    (he₃ : ∀ X : C, ∃ p, e₃.hom.app X = eqToHom p)
    (he₄ : ∀ Y : D, ∃ p, e₄.hom.app Y = eqToHom p) :
    e₁ ≪≫ Functor.isoWhiskerRight e₂ H ≪≫ Functor.associator F G H =
      eqToIso h ≪≫ e₃ ≪≫ Functor.isoWhiskerLeft F e₄ :=
  eq_of_hom_app_eqToHom
    (fun X ↦ have ⟨p₁, hp₁⟩ := he₁ X; have ⟨p₂, hp₂⟩ := he₂ X
      ⟨p₁.trans (congrArg H.obj p₂), by simp [hp₁, hp₂, eqToHom_map]⟩)
    (fun X ↦ have ⟨p₃, hp₃⟩ := he₃ X; have ⟨p₄, hp₄⟩ := he₄ (F.obj X)
      ⟨(Functor.congr_obj h X).trans (p₃.trans p₄), by simp [hp₃, hp₄]⟩)

end CategoryTheory.NatIso
