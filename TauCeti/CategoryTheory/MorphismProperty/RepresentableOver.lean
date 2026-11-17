/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import TauCeti.CategoryTheory.Comma.Presheaf.OverYoneda

/-!
# Relative representability over a base

Relative representability of morphisms with respect to a functor `F : C ⥤ D`
(Mathlib's `Functor.relativelyRepresentable` and `MorphismProperty.relative`) is unchanged when
the target is replaced through an equivalence `e : D ≌ D'` and `F` by a functor `F'` with
`F ⋙ e.functor ≅ F'`. For a fully faithful `F` and `X : C`, a morphism of `Over (F.obj X)` is
relatively representable with respect to `Over.post F : Over X ⥤ Over (F.obj X)` exactly when its
underlying morphism of `D` is relatively representable with respect to `F`.

Together with the equivalence `TauCeti.overYonedaEquivPresheafOver X` between presheaves over
`yoneda.obj X` and presheaves on `Over X`, these show that a morphism of presheaves over
`yoneda.obj X` is representable (with base changes in a class `P`) exactly when the corresponding
morphism of presheaves on `Over X` is representable by objects of `Over X` (with base changes
whose underlying morphisms are in `P`).

## Main results

* `CategoryTheory.Functor.relativelyRepresentable_equivalence_map_iff` and
  `CategoryTheory.MorphismProperty.relative_equivalence_map_iff`: transport along an equivalence
  of target categories.
* `CategoryTheory.Functor.relativelyRepresentable_overPost_iff` and
  `CategoryTheory.MorphismProperty.relative_overPost_iff`: relative representability with respect
  to `Over.post F` is relative representability of the underlying morphism.
* `TauCeti.relativelyRepresentable_overYonedaEquivPresheafOver_map_iff` and
  `TauCeti.presheaf_overYonedaEquivPresheafOver_map_iff`: the case of presheaves over a
  representable presheaf.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Equivalence

variable {D' : Type u₃} [Category.{v₃} D'] {F : C ⥤ D} {F' : C ⥤ D'} {e : D ≌ D'}
  (i : F ⋙ e.functor ≅ F')

include i

/-- A square with a side `F.map snd` is a pullback square exactly when its image under the
equivalence `e`, with `F ⋙ e.functor` replaced by `F'` through `i`, is a pullback square. -/
lemma isPullback_equivalence_map_iff {X Y : D} {f : X ⟶ Y} {a b : C} {g : F.obj a ⟶ Y}
    {fst : F.obj b ⟶ X} {snd : b ⟶ a} :
    IsPullback (i.inv.app b ≫ e.functor.map fst) (F'.map snd) (e.functor.map f)
      (i.inv.app a ≫ e.functor.map g) ↔ IsPullback fst (F.map snd) f g := by
  have hsnd : F'.map snd ≫ i.inv.app a = i.inv.app b ≫ e.functor.map (F.map snd) :=
    i.inv.naturality snd
  constructor
  · intro h
    refine IsPullback.of_map e.functor (e.functor.map_injective ?_) ?_
    · have := h.w
      simp only [Category.assoc, reassoc_of% hsnd, cancel_epi] at this
      simpa only [Functor.map_comp] using this
    · exact h.of_iso (i.app b).symm (Iso.refl _) (i.app a).symm (Iso.refl _) (by simp) hsnd
        (by simp) (by simp)
  · intro h
    exact (h.map e.functor).of_iso (i.app b) (Iso.refl _) (i.app a) (Iso.refl _)
      (by simp) (i.hom.naturality snd) (by simp) (by simp)

/-- Relative representability is invariant under replacing the target category through an
equivalence `e : D ≌ D'`, the functor `F` by `F'` with `F ⋙ e.functor ≅ F'`. -/
theorem Functor.relativelyRepresentable_equivalence_map_iff {X Y : D} (f : X ⟶ Y) :
    F'.relativelyRepresentable (e.functor.map f) ↔ F.relativelyRepresentable f := by
  constructor
  · intro h a g
    obtain ⟨b, snd, fst', hb⟩ := h (i.inv.app a ≫ e.functor.map g)
    refine ⟨b, snd, e.functor.preimage (i.hom.app b ≫ fst'), ?_⟩
    rw [← isPullback_equivalence_map_iff i]
    simpa using hb
  · intro h a g'
    obtain ⟨b, snd, fst, hb⟩ := h (e.functor.preimage (i.hom.app a ≫ g'))
    refine ⟨b, snd, i.inv.app b ≫ e.functor.map fst, ?_⟩
    simpa using (isPullback_equivalence_map_iff i).2 hb

/-- The morphism property `P.relative` is invariant under replacing the target category through
an equivalence `e : D ≌ D'`, the functor `F` by `F'` with `F ⋙ e.functor ≅ F'`. -/
theorem MorphismProperty.relative_equivalence_map_iff (P : MorphismProperty C) {X Y : D}
    (f : X ⟶ Y) : P.relative F' (e.functor.map f) ↔ P.relative F f := by
  refine and_congr (Functor.relativelyRepresentable_equivalence_map_iff i f) ⟨?_, ?_⟩
  · intro h a b g fst snd hb
    exact h (i.inv.app a ≫ e.functor.map g) _ snd ((isPullback_equivalence_map_iff i).2 hb)
  · intro h a b g' fst' snd hb
    refine h (e.functor.preimage (i.hom.app a ≫ g')) (e.functor.preimage (i.hom.app b ≫ fst'))
      snd ?_
    rw [← isPullback_equivalence_map_iff i]
    simpa using hb

end Equivalence

section Over

variable (F : C ⥤ D) {X : C}

/-- A square in `Over (F.obj X)` with a side `(Over.post F).map snd` is a pullback square exactly
when the underlying square in `D` is. -/
lemma isPullback_overPost_iff {A B : Over (F.obj X)} {f : A ⟶ B} {a b : Over X}
    {g : (Over.post F).obj a ⟶ B} {fst : (Over.post F).obj b ⟶ A} {snd : b ⟶ a} :
    IsPullback fst ((Over.post F).map snd) f g ↔
      IsPullback fst.left (F.map snd.left) f.left g.left := by
  refine ⟨fun h ↦ h.map (Over.forget _), fun h ↦ IsPullback.of_map (Over.forget _) ?_ h⟩
  ext
  exact h.w

variable {F}

/-- A pullback square in `D` with sides `F.map snd` and `g.left`, for `g : (Over.post F).obj a ⟶ B`
in `Over (F.obj X)`, lifts to a pullback square in `Over (F.obj X)`, with `b` lying over `X`
through `snd ≫ a.hom`. -/
lemma isPullback_overPost_homMk {A B : Over (F.obj X)} {f : A ⟶ B} {a : Over X} {b : C}
    {g : (Over.post F).obj a ⟶ B} {fst : F.obj b ⟶ A.left} {snd : b ⟶ a.left}
    (h : IsPullback fst (F.map snd) f.left g.left) :
    IsPullback (Over.homMk (U := (Over.post F).obj (Over.mk (snd ≫ a.hom))) fst
        (by rw [← Over.w f, reassoc_of% h.w, Over.w g]; exact (F.map_comp _ _).symm) : _ ⟶ A)
      ((Over.post F).map (Over.homMk snd : Over.mk (snd ≫ a.hom) ⟶ a)) f g :=
  (isPullback_overPost_iff F).2 h

variable [F.Full]

/-- A morphism `g : F.obj a ⟶ B.left` to the underlying object of `B : Over (F.obj X)`, regarded
as a morphism of `Over (F.obj X)` out of the image under `Over.post F` of `a` over `X`. -/
noncomputable abbrev Over.postHomMk {B : Over (F.obj X)} {a : C} (g : F.obj a ⟶ B.left) :
    (Over.post F).obj (Over.mk (F.preimage (g ≫ B.hom))) ⟶ B :=
  Over.homMk g (by simp)

/-- Relative representability with respect to `Over.post F` of a morphism of `Over (F.obj X)` is
relative representability of the underlying morphism with respect to `F`. -/
theorem Functor.relativelyRepresentable_overPost_iff {A B : Over (F.obj X)} (f : A ⟶ B) :
    (Over.post F).relativelyRepresentable f ↔ F.relativelyRepresentable f.left := by
  constructor
  · intro h a g
    obtain ⟨b, snd, fst, hb⟩ := h (Over.postHomMk g)
    exact ⟨b.left, snd.left, fst.left, (isPullback_overPost_iff F).1 hb⟩
  · intro h a g
    obtain ⟨b, snd, fst, hb⟩ := h g.left
    exact ⟨_, _, _, isPullback_overPost_homMk hb⟩

/-- For a morphism property `P` of `C`, the relative property with respect to `Over.post F` of
the inverse image of `P` in `Over X` holds for a morphism of `Over (F.obj X)` exactly when
`P.relative F` holds for its underlying morphism. -/
theorem MorphismProperty.relative_overPost_iff (P : MorphismProperty C) {A B : Over (F.obj X)}
    (f : A ⟶ B) :
    (P.inverseImage (Over.forget X)).relative (Over.post F) f ↔ P.relative F f.left := by
  refine and_congr (Functor.relativelyRepresentable_overPost_iff f) ⟨?_, ?_⟩
  · intro h a b g fst snd hb
    exact h (Over.postHomMk g) _ _
      (isPullback_overPost_homMk (g := Over.postHomMk g) (snd := snd) hb)
  · intro h a b g fst snd hb
    exact h g.left fst.left snd.left ((isPullback_overPost_iff F).1 hb)

end Over

end CategoryTheory

namespace TauCeti

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {X : C}

/-- A morphism of presheaves over `yoneda.obj X` is representable exactly when the corresponding
morphism of presheaves on `Over X` is representable by objects of `Over X`. -/
theorem relativelyRepresentable_overYonedaEquivPresheafOver_map_iff
    {A B : Over (yoneda.obj X)} (f : A ⟶ B) :
    yoneda.relativelyRepresentable ((overYonedaEquivPresheafOver X).functor.map f) ↔
      yoneda.relativelyRepresentable f.left :=
  (Functor.relativelyRepresentable_equivalence_map_iff
    (overYonedaEquivPresheafOverYonedaIso X) f).trans
      (Functor.relativelyRepresentable_overPost_iff f)

/-- A morphism of presheaves over `yoneda.obj X` is representable with base changes in `P`
exactly when the corresponding morphism of presheaves on `Over X` is representable by objects of
`Over X` with base changes whose underlying morphisms are in `P`. -/
theorem presheaf_overYonedaEquivPresheafOver_map_iff (P : MorphismProperty C)
    {A B : Over (yoneda.obj X)} (f : A ⟶ B) :
    (P.inverseImage (Over.forget X)).presheaf ((overYonedaEquivPresheafOver X).functor.map f) ↔
      P.presheaf f.left :=
  (MorphismProperty.relative_equivalence_map_iff
    (overYonedaEquivPresheafOverYonedaIso X) _ f).trans
      (MorphismProperty.relative_overPost_iff P f)

/-- Morphisms in `Over (yoneda.obj X)` from `yoneda.obj Y` lying over `yoneda.obj X` through
`yoneda.map Y.hom` correspond to morphisms from the representable presheaf `yoneda.obj Y` on
`Over X`, through the equivalence `overYonedaEquivPresheafOver X`. -/
@[expose, simps]
noncomputable def overYonedaEquivPresheafOverHomEquiv (Y : Over X) (F : Over (yoneda.obj X)) :
    (Over.mk (yoneda.map Y.hom) ⟶ F) ≃
      (yoneda.obj Y ⟶ (overYonedaEquivPresheafOver X).functor.obj F) where
  toFun g := (overYonedaEquivPresheafOverYonedaIso X).inv.app Y ≫
    (overYonedaEquivPresheafOver X).functor.map g
  invFun g := (overYonedaEquivPresheafOver X).functor.preimage
    ((overYonedaEquivPresheafOverYonedaIso X).hom.app Y ≫ g)
  left_inv g := by simp
  right_inv g := by simp

/-- A morphism from a representable presheaf on `Over X` is representable by objects of
`Over X` exactly when the underlying morphism of presheaves on `C` of the corresponding morphism
over `yoneda.obj X` is representable. -/
theorem relativelyRepresentable_overYonedaEquivPresheafOverHomEquiv_iff {Y : Over X}
    {F : Over (yoneda.obj X)} (g : Over.mk (yoneda.map Y.hom) ⟶ F) :
    yoneda.relativelyRepresentable (overYonedaEquivPresheafOverHomEquiv Y F g) ↔
      yoneda.relativelyRepresentable g.left :=
  (MorphismProperty.cancel_left_of_respectsIso _ _ _).trans
    (relativelyRepresentable_overYonedaEquivPresheafOver_map_iff g)

/-- A morphism from a representable presheaf on `Over X` is representable with base changes
whose underlying morphisms are in `P` exactly when the underlying morphism of presheaves on `C`
of the corresponding morphism over `yoneda.obj X` is representable with base changes in `P`. -/
theorem presheaf_overYonedaEquivPresheafOverHomEquiv_iff (P : MorphismProperty C) {Y : Over X}
    {F : Over (yoneda.obj X)} (g : Over.mk (yoneda.map Y.hom) ⟶ F) :
    (P.inverseImage (Over.forget X)).presheaf (overYonedaEquivPresheafOverHomEquiv Y F g) ↔
      P.presheaf g.left :=
  (MorphismProperty.cancel_left_of_respectsIso _ _ _).trans
    (presheaf_overYonedaEquivPresheafOver_map_iff P g)

end TauCeti
