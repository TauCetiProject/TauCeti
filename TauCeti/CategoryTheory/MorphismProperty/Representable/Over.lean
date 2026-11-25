/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Comma.Over
public import TauCeti.CategoryTheory.Comma.Presheaf.OverYoneda
public import TauCeti.CategoryTheory.MorphismProperty.Representable.Basic

/-!
# Relative representability over a base

For a fully faithful `F : C ⥤ D` and `X : C`, a morphism of `Over (F.obj X)` is relatively
representable with respect to `Over.post F : Over X ⥤ Over (F.obj X)` exactly when its underlying
morphism of `D` is relatively representable with respect to `F`.

Together with the equivalence `TauCeti.overYonedaEquivPresheafOver X` between presheaves over
`yoneda.obj X` and presheaves on `Over X`, and the invariance of relative representability under
an equivalence of target categories
(`CategoryTheory.Functor.relativelyRepresentable_equivalence_map_iff`), these show that a morphism
of presheaves over `yoneda.obj X` is representable (with base changes in a class `P`) exactly when
the corresponding morphism of presheaves on `Over X` is representable by objects of `Over X`
(with base changes whose underlying morphisms are in `P`).

## Main results

* `CategoryTheory.Functor.relativelyRepresentable_overPost_iff` and
  `CategoryTheory.MorphismProperty.relative_overPost_iff`: relative representability with respect
  to `Over.post F` is relative representability of the underlying morphism.
* `CategoryTheory.Over.relativelyRepresentable_overYonedaEquivPresheafOver_map_iff` and
  `CategoryTheory.MorphismProperty.presheaf_overYonedaEquivPresheafOver_map_iff`: the case of
  presheaves over a representable presheaf.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Over

variable {F : C ⥤ D} [F.Full] {X : C}

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
    exact ⟨_, _, _, hb.overPost_homMk⟩

/-- For a morphism property `P` of `C`, the relative property with respect to `Over.post F` of
the inverse image of `P` in `Over X` holds for a morphism of `Over (F.obj X)` exactly when
`P.relative F` holds for its underlying morphism. -/
theorem MorphismProperty.relative_overPost_iff (P : MorphismProperty C) {A B : Over (F.obj X)}
    (f : A ⟶ B) :
    (P.inverseImage (Over.forget X)).relative (Over.post F) f ↔ P.relative F f.left := by
  refine and_congr (Functor.relativelyRepresentable_overPost_iff f) ⟨?_, ?_⟩
  · intro h a b g fst snd hb
    exact h (Over.postHomMk g) _ _
      (IsPullback.overPost_homMk (g := Over.postHomMk g) (snd := snd) hb)
  · intro h a b g fst snd hb
    exact h g.left fst.left snd.left ((isPullback_overPost_iff F).1 hb)

end Over

end CategoryTheory

open CategoryTheory

namespace TauCeti

variable {C : Type u₁} [Category.{v₁} C] {X : C}

/-- A morphism of presheaves over `yoneda.obj X` is representable exactly when the corresponding
morphism of presheaves on `Over X` is representable by objects of `Over X`. -/
theorem _root_.CategoryTheory.Over.relativelyRepresentable_overYonedaEquivPresheafOver_map_iff
    {A B : Over (yoneda.obj X)} (f : A ⟶ B) :
    yoneda.relativelyRepresentable ((overYonedaEquivPresheafOver X).functor.map f) ↔
      yoneda.relativelyRepresentable f.left :=
  (Functor.relativelyRepresentable_equivalence_map_iff
    (overYonedaEquivPresheafOverYonedaIso X) f).trans
      (Functor.relativelyRepresentable_overPost_iff f)

/-- A morphism of presheaves over `yoneda.obj X` is representable with base changes in `P`
exactly when the corresponding morphism of presheaves on `Over X` is representable by objects of
`Over X` with base changes whose underlying morphisms are in `P`. -/
theorem _root_.CategoryTheory.MorphismProperty.presheaf_overYonedaEquivPresheafOver_map_iff
    (P : MorphismProperty C) {A B : Over (yoneda.obj X)} (f : A ⟶ B) :
    (P.inverseImage (Over.forget X)).presheaf ((overYonedaEquivPresheafOver X).functor.map f) ↔
      P.presheaf f.left :=
  (MorphismProperty.relative_equivalence_map_iff
    (overYonedaEquivPresheafOverYonedaIso X) _ f).trans
      (MorphismProperty.relative_overPost_iff P f)

/-- A morphism from a representable presheaf on `Over X` is representable by objects of
`Over X` exactly when the underlying morphism of presheaves on `C` of the corresponding morphism
over `yoneda.obj X` is representable. -/
theorem _root_.CategoryTheory.Over.relativelyRepresentable_overYonedaEquivPresheafOverHomEquiv_iff
    {Y : Over X} {F : Over (yoneda.obj X)} (g : Over.mk (yoneda.map Y.hom) ⟶ F) :
    yoneda.relativelyRepresentable (Over.overYonedaEquivPresheafOverHomEquiv Y F g) ↔
      yoneda.relativelyRepresentable g.left := by
  rw [Over.overYonedaEquivPresheafOverHomEquiv_apply]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).trans
    (Over.relativelyRepresentable_overYonedaEquivPresheafOver_map_iff g)

/-- A morphism from a representable presheaf on `Over X` is representable with base changes
whose underlying morphisms are in `P` exactly when the underlying morphism of presheaves on `C`
of the corresponding morphism over `yoneda.obj X` is representable with base changes in `P`. -/
theorem _root_.CategoryTheory.MorphismProperty.presheaf_overYonedaEquivPresheafOverHomEquiv_iff
    (P : MorphismProperty C) {Y : Over X}
    {F : Over (yoneda.obj X)} (g : Over.mk (yoneda.map Y.hom) ⟶ F) :
    (P.inverseImage (Over.forget X)).presheaf (Over.overYonedaEquivPresheafOverHomEquiv Y F g) ↔
      P.presheaf g.left := by
  rw [Over.overYonedaEquivPresheafOverHomEquiv_apply]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).trans
    (P.presheaf_overYonedaEquivPresheafOver_map_iff g)

end TauCeti
