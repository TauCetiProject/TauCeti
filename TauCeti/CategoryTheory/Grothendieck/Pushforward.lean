/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Grothendieck.Pullback

/-!
# Pushing sections forward along fiber functors

A natural transformation between category-valued diagrams sends sections and
vertical labels to sections and vertical labels. Together with restriction of
sections, this transports labels between systems over different bases.
`pullback_pushforward` identifies the two orders of these operations.

A natural transformation between represented coefficient diagrams induces a map
on the coefficient limits along a section. This map is equivariant for vertical
labels; an invertible coefficient transformation gives an isomorphism.

The constructions use Mathlib's `Grothendieck.map`, `Functor.Fiber`, whiskering
and `Limits.limMap`, retaining the existing strict-section carrier.

## Attribution

Adapted from `Mei/CategoryTheory/Grothendieck/Pushforward.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original author credit is retained; the file uses the required Tau Ceti copyright header.
-/

public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Grothendieck CategoryTheory.Limits

universe v u w z v' u'

namespace TauCeti.CategoryTheory.Grothendieck.Section

variable {D : Type u} [Category.{v} D] {C C' C'' : D ⥤ Cat.{w, z}}

/-- Push a section forward along a natural transformation of its fibers. -/
-- Expose the underlying functor so its objects compute in dependent label types.
@[expose]
def pushforward (h : C ⟶ C') (s : Section C) : Section C' :=
  Functor.Fiber.mk (a := s.toFunctor ⋙ Grothendieck.map h) (by
    exact (Functor.assoc s.toFunctor (Grothendieck.map h) (forget C')).trans
      ((congrArg (s.toFunctor ⋙ ·) (functor_comp_forget (α := h))).trans
        s.toFunctor_comp_forget))

/-- The underlying functor is postcomposition by the induced Grothendieck functor. -/
@[simp]
theorem pushforward_toFunctor (h : C ⟶ C') (s : Section C) :
    (pushforward h s).toFunctor = s.toFunctor ⋙ Grothendieck.map h := (rfl)

/-- Push a vertical label forward along a natural transformation of fibers. -/
def pushforwardHom (h : C ⟶ C') {s t : Section C} (α : s ⟶ t) :
    pushforward h s ⟶ pushforward h t :=
  homMk (whiskerRight (hom α) (Grothendieck.map h)) (by
    ext d
    have he := NatTrans.congr_app (whiskerRight_hom_forget α) d
    convert he using 1 <;> rfl)

/-- A pushed-forward label is the image of the original component. -/
@[simp]
theorem hom_pushforwardHom (h : C ⟶ C') {s t : Section C} (α : s ⟶ t) :
    hom (pushforwardHom h α) = whiskerRight (hom α) (Grothendieck.map h) := by
  unfold pushforwardHom
  -- `Fiber.mk` must reduce to identify the endpoints of the whiskered label.
  erw [hom_homMk]

/-- Fiber functors act functorially on sections and vertical labels. -/
-- The object map must compute to `pushforward` in types of section morphisms.
@[expose]
def pushforwardFunctor (h : C ⟶ C') : Section C ⥤ Section C' where
  obj s := pushforward h s
  map α := pushforwardHom h α
  map_id s := by
    apply hom_ext
    intro d
    simp only [hom_pushforwardHom, hom, _root_.CategoryTheory.Functor.map_id,
      whiskerRight_app, NatTrans.id_app]
    -- Fiber.mk retains the postcomposed functor and its object endpoints.
    rfl
  map_comp α β := by
    apply hom_ext
    intro d
    simp only [hom_pushforwardHom, hom, Functor.map_comp, whiskerRight_app,
      NatTrans.comp_app]
    -- Fiber.mk retains the postcomposed functor and its object endpoints.
    rfl

@[simp]
theorem pushforwardFunctor_obj (h : C ⟶ C') (s : Section C) :
    (pushforwardFunctor h).obj s = pushforward h s := (rfl)

@[simp]
theorem pushforwardFunctor_map (h : C ⟶ C') {s t : Section C} (α : s ⟶ t) :
    (pushforwardFunctor h).map α = pushforwardHom h α := (rfl)

/-- Pushing forward by identity fiber functors fixes a section. -/
@[simp]
theorem pushforward_id (s : Section C) : pushforward (𝟙 C) s = s := by
  apply Functor.Fiber.fiberInclusion_obj_inj
  simp only [pushforward_toFunctor, Grothendieck.map_id_eq, Functor.comp_id]

/-- Successive fiber functors push a section forward by their composite. -/
@[simp]
theorem pushforward_comp (h : C ⟶ C') (k : C' ⟶ C'') (s : Section C) :
    pushforward (h ≫ k) s = pushforward k (pushforward h s) := by
  apply Functor.Fiber.fiberInclusion_obj_inj
  simp only [pushforward_toFunctor, Grothendieck.map_comp_eq, Functor.assoc]

variable {V : Type u'} [Category.{v'} V]
  {A : Grothendieck C ⥤ V} {A' : Grothendieck C' ⥤ V}

/-- Restrict a coefficient comparison to a section and its pushed-forward section. -/
def coefficientPushforward (h : C ⟶ C') (η : A ⟶ Grothendieck.map h ⋙ A')
    (s : Section C) : s.toFunctor ⋙ A ⟶ (pushforward h s).toFunctor ⋙ A' :=
  whiskerLeft s.toFunctor η ≫
    (Functor.associator s.toFunctor (Grothendieck.map h) A').inv

/-- The coefficient comparison acts at the object chosen by the section. -/
@[simp]
theorem coefficientPushforward_app (h : C ⟶ C')
    (η : A ⟶ Grothendieck.map h ⋙ A') (s : Section C) (d : D) :
    (coefficientPushforward h η s).app d = η.app (s.toFunctor.obj d) := by
  unfold coefficientPushforward
  -- Reduce the section wrapper to evaluate the associator at its object.
  erw [NatTrans.comp_app, whiskerLeft_app, Functor.associator_inv_app, Category.comp_id]

/-- A coefficient comparison is natural in vertical labels. -/
@[reassoc]
theorem coefficientPushforward_naturality (h : C ⟶ C')
    (η : A ⟶ Grothendieck.map h ⋙ A') {s t : Section C} (α : s ⟶ t) :
    whiskerRight (hom α) A ≫ coefficientPushforward h η t =
      coefficientPushforward h η s ≫
        whiskerRight (hom (pushforwardHom h α)) A' := by
  ext d
  simp only [NatTrans.comp_app, coefficientPushforward_app, whiskerRight_app,
    hom_pushforwardHom]
  exact η.naturality ((hom α).app d)

/-- Invertible coefficient transformations remain invertible along sections. -/
instance isIso_coefficientPushforward (h : C ⟶ C')
    (η : A ⟶ Grothendieck.map h ⋙ A') [IsIso η] (s : Section C) :
    IsIso (coefficientPushforward h η s) := by
  unfold coefficientPushforward
  -- The target diagram is the associator's target after reducing `Fiber.mk`.
  exact inferInstanceAs (IsIso (whiskerLeft s.toFunctor η ≫
    (Functor.associator s.toFunctor (Grothendieck.map h) A').inv))

/-- The induced comparison between completed coefficient objects along sections. -/
noncomputable def coefficientPushforwardLimit (h : C ⟶ C')
    (η : A ⟶ Grothendieck.map h ⋙ A') (s : Section C)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit ((pushforward h s).toFunctor ⋙ A')] :
    limit (s.toFunctor ⋙ A) ⟶ limit ((pushforward h s).toFunctor ⋙ A') :=
  limMap (coefficientPushforward h η s)

/-- The comparison is computed on each matching-family component by `η`. -/
@[reassoc (attr := simp)]
theorem coefficientPushforwardLimit_π (h : C ⟶ C')
    (η : A ⟶ Grothendieck.map h ⋙ A') (s : Section C)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit ((pushforward h s).toFunctor ⋙ A')] (d : D) :
    coefficientPushforwardLimit h η s ≫ limit.π ((pushforward h s).toFunctor ⋙ A') d =
      limit.π (s.toFunctor ⋙ A) d ≫ η.app (s.toFunctor.obj d) := by
  exact (limMap_π (coefficientPushforward h η s) d).trans
    (congrArg (limit.π (s.toFunctor ⋙ A) d ≫ ·) (coefficientPushforward_app h η s d))

/-- Coefficient-limit comparisons intertwine the represented vertical labels. -/
@[reassoc]
theorem coefficientPushforwardLimit_naturality (h : C ⟶ C')
    (η : A ⟶ Grothendieck.map h ⋙ A') {s t : Section C} (α : s ⟶ t)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)]
    [HasLimit ((pushforward h s).toFunctor ⋙ A')]
    [HasLimit ((pushforward h t).toFunctor ⋙ A')] :
    limMap (whiskerRight (hom α) A) ≫ coefficientPushforwardLimit h η t =
      coefficientPushforwardLimit h η s ≫
        limMap (whiskerRight (hom (pushforwardHom h α)) A') := by
  apply limit.hom_ext
  intro d
  simp only [coefficientPushforwardLimit, Category.assoc, limMap_π_assoc, limMap_π]
  exact congrArg (limit.π (s.toFunctor ⋙ A) d ≫ ·)
    (NatTrans.congr_app (coefficientPushforward_naturality h η α) d)

/-- An invertible coefficient comparison identifies the two coefficient limits;
the fiber functors themselves need not be equivalences. -/
instance isIso_coefficientPushforwardLimit (h : C ⟶ C')
    (η : A ⟶ Grothendieck.map h ⋙ A') [IsIso η] (s : Section C)
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit ((pushforward h s).toFunctor ⋙ A')] :
    IsIso (coefficientPushforwardLimit h η s) := by
  exact inferInstanceAs (IsIso (limMap (coefficientPushforward h η s)))

/-- Restricting a pushed-forward section agrees with pushing forward its restriction. -/
theorem pullback_pushforward {E : Type*} [Category* E] (H : E ⥤ D) (h : C ⟶ C') (s : Section C) :
    pullback H (pushforward h s) = pushforward (whiskerLeft H h) (pullback H s) := by
  apply Functor.Fiber.fiberInclusion_obj_inj
  suffices h : (pullback H (pushforward h s)).toFunctor =
      (pushforward (whiskerLeft H h) (pullback H s)).toFunctor by
    exact h
  exact liftFunctor_comp_map H h (H ⋙ s.toFunctor)
    (comp_toFunctor_comp_forget H s)

end TauCeti.CategoryTheory.Grothendieck.Section
