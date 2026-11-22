/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# Enriched categories and enriched functors: transport and lifting

This file provides transport lemmas along object equalities for enriched identities, enriched
composition, and enriched functors, together with a general lifting construction for enriched
functors along an enriched functor that is an isomorphism on every hom object.

## Main definitions

* `CategoryTheory.EnrichedFunctor.lift`: lift an enriched functor `G : EnrichedFunctor V A D` along
  `F : EnrichedFunctor V C D` with isomorphisms on hom objects, given a prescribed object map
  `obj : A → C` compatible with `F.obj`.

## Main results

* `CategoryTheory.eId_comp_eqToHom`, `CategoryTheory.tensorHom_eqToHom_comp_eComp`: compatibility of
  enriched identities and composition with `eqToHom` transports on hom objects.
* `CategoryTheory.EnrichedFunctor.map_comp_eqToHom`: compatibility of `F.map` with `eqToHom`
  transports on hom objects.
* `CategoryTheory.EnrichedFunctor.lift_obj`, `CategoryTheory.EnrichedFunctor.lift_map`:
  object and hom-map computation rules for `lift`.
* `CategoryTheory.EnrichedFunctor.lift_comp`, `CategoryTheory.EnrichedFunctor.lift_unique`:
  postcomposing `lift` with `F` recovers `G`, and `lift` is the unique lift with the prescribed
  object map.
-/

public section

open CategoryTheory MonoidalCategory

universe w v u₁ u₂ u₃

namespace CategoryTheory

section Transport

variable {V : Type v} [Category.{w} V] [MonoidalCategory V] {C : Type u₁} [EnrichedCategory V C]

/-- Transporting an enriched identity along an equality of objects gives the enriched identity
at the target object. -/
@[reassoc]
lemma eId_comp_eqToHom {c c' : C} (h : c = c') :
    eId V c ≫ eqToHom (by rw [h]) = eId V c' := by
  subst h
  simp

/-- Enriched composition is compatible with transporting hom objects along equalities of
objects. -/
@[reassoc]
lemma tensorHom_eqToHom_comp_eComp {a a' b b' c c' : C}
    (ha : a = a') (hb : b = b') (hc : c = c') :
    (eqToHom (by rw [ha, hb]) ⊗ₘ eqToHom (by rw [hb, hc])) ≫ eComp V a' b' c' =
      eComp V a b c ≫ eqToHom (by rw [ha, hc]) := by
  subst ha hb hc
  simp

end Transport

namespace EnrichedFunctor

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]
  {A : Type u₁} {C : Type u₂} {D : Type u₃}
  [EnrichedCategory V A] [EnrichedCategory V C] [EnrichedCategory V D]

/-- An enriched functor commutes with transporting hom objects along equalities of objects. -/
@[reassoc]
lemma map_comp_eqToHom (F : EnrichedFunctor V C D) {a a' b b' : C}
    (ha : a = a') (hb : b = b') :
    F.map a b ≫ eqToHom (by rw [ha, hb]) = eqToHom (by rw [ha, hb]) ≫ F.map a' b' := by
  subst ha hb
  simp

/-- Lift an enriched functor `G : EnrichedFunctor V A D` along `F : EnrichedFunctor V C D`
inducing isomorphisms on all hom objects, with a prescribed object map `obj : A → C` satisfying
`F.obj (obj a) = G.obj a`. -/
noncomputable def lift (F : EnrichedFunctor V C D) [∀ a b : C, IsIso (F.map a b)]
    (G : EnrichedFunctor V A D) (obj : A → C) (hobj : ∀ a : A, F.obj (obj a) = G.obj a) :
    EnrichedFunctor V A C where
  obj := obj
  map i j := G.map i j ≫ eqToHom (by rw [hobj i, hobj j]) ≫ inv (F.map (obj i) (obj j))
  map_id i := by
    rw [← cancel_mono (F.map _ _)]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, F.map_id,
      G.map_id_assoc, eId_comp_eqToHom (hobj i).symm]
  map_comp i j k := by
    rw [← cancel_mono (F.map _ _)]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, F.map_comp,
      tensorHom_comp_tensorHom_assoc, G.map_comp_assoc]
    rw [← tensorHom_comp_tensorHom_assoc,
      tensorHom_eqToHom_comp_eComp (hobj i).symm (hobj j).symm (hobj k).symm]

/-- The lifted enriched functor acts on objects by the prescribed object map. -/
@[simp]
lemma lift_obj (F : EnrichedFunctor V C D) [∀ a b : C, IsIso (F.map a b)]
    (G : EnrichedFunctor V A D) (obj : A → C) (hobj : ∀ a : A, F.obj (obj a) = G.obj a)
    (a : A) :
    (lift F G obj hobj).obj a = obj a :=
  (rfl)

/-- The lifted enriched functor acts on hom objects by composing `G.map`, equality transport along
`hobj`, and the inverse of `F.map`, up to the object identification `lift_obj`. -/
@[simp, reassoc]
lemma lift_map (F : EnrichedFunctor V C D) [∀ a b : C, IsIso (F.map a b)]
    (G : EnrichedFunctor V A D) (obj : A → C) (hobj : ∀ a : A, F.obj (obj a) = G.obj a)
    (i j : A) :
    (lift F G obj hobj).map i j =
      G.map i j ≫ eqToHom (by rw [hobj i, hobj j]) ≫ inv (F.map (obj i) (obj j)) ≫
        eqToHom (by rw [lift_obj, lift_obj]) := by
  simp [lift]

/-- Postcomposing `lift F G obj hobj` with `F` recovers `G`. -/
@[simp]
lemma lift_comp (F : EnrichedFunctor V C D) [∀ a b : C, IsIso (F.map a b)]
    (G : EnrichedFunctor V A D) (obj : A → C) (hobj : ∀ a : A, F.obj (obj a) = G.obj a) :
    (lift F G obj hobj).comp V F = G := by
  refine EnrichedFunctor.ext V hobj fun i j ↦ ?_
  -- `EnrichedFunctor.comp` and `lift` are semireducible, so `((lift F G obj hobj).comp V F).obj`
  -- in the `eqToHom` domain from `EnrichedFunctor.ext` does not unify with `F.obj (obj _)` at
  -- `reducible` transparency for `EnrichedFunctor.comp_map` and `eqToHom_trans`.
  change ((lift F G obj hobj).map i j ≫
      F.map ((lift F G obj hobj).obj i) ((lift F G obj hobj).obj j)) ≫
      eqToHom (by simp only [lift_obj, hobj]) = G.map i j
  rw [lift_map]
  simp only [Category.assoc,
    ← F.map_comp_eqToHom_assoc (lift_obj F G obj hobj i).symm (lift_obj F G obj hobj j).symm,
    IsIso.inv_hom_id_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Uniqueness of the lift of `G` along `F` for a prescribed object map `obj`. -/
lemma lift_unique {F : EnrichedFunctor V C D} [∀ a b : C, IsIso (F.map a b)]
    {G : EnrichedFunctor V A D} {obj : A → C} {hobj : ∀ a : A, F.obj (obj a) = G.obj a}
    (H : EnrichedFunctor V A C) (hH_obj : ∀ a : A, H.obj a = obj a)
    (hH_comp : H.comp V F = G) :
    H = lift F G obj hobj := by
  subst hH_comp
  refine EnrichedFunctor.ext V hH_obj fun i j ↦ ?_
  dsimp only [lift, EnrichedFunctor.comp]
  rw [← cancel_mono (F.map (obj i) (obj j))]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← F.map_comp_eqToHom (hH_obj i) (hH_obj j)]

end EnrichedFunctor

end CategoryTheory
