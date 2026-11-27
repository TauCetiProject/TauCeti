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
-/

public section

universe v₁ v₂ u₁ u₂

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

end CategoryTheory.NatIso
