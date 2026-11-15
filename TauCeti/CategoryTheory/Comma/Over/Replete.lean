/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import TauCeti.CategoryTheory.Comma.Over.Pullback
public import TauCeti.CategoryTheory.Limits.Replete

/-!
# Repleteness of slice categories and descent along covers

Every slice of a replete category with binary products is replete (`TauCeti.isReplete_over`).
Conversely, when epimorphisms are stable under base change, repleteness is local on the base
(Bhatt–Scholze, Lemma 3.1.3):

* `TauCeti.IsReplete.of_over_of_epi_snd`: if `Over U` is replete, `U ⨯ -` preserves epimorphisms,
  and every second projection `U ⨯ Z ⟶ Z` is an epimorphism, then `C` is replete, by descending
  along `Over.star U : C ⥤ Over U`;
* `TauCeti.IsReplete.of_over_epi` and `TauCeti.isReplete_over_iff`: when epimorphisms are stable
  under base change and `U ⟶ ⊤_ C` is an epimorphism, `Over U` is replete if and only if `C` is
  replete;
* `TauCeti.IsReplete.of_over_pullback_epi`: repleteness of slices descends along any epimorphism
  `f : X ⟶ Y` via `Over.pullback f : Over Y ⥤ Over X`;
* `TauCeti.IsReplete.of_forall_over_of_jointly_epi_snd`: repleteness descends from a family of
  slices `Over (U i)` whose second projections `U i ⨯ Z ⟶ Z` are jointly epimorphic, avoiding any
  coproduct hypothesis on `C`.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015),
  Lemmas 3.1.2 and 3.1.3.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C]

/-- Every slice of a replete category with binary products is replete. This applies,
in particular, to slices of replete topoi. -/
instance isReplete_over [HasBinaryProducts C] [IsReplete C] (X : C) : IsReplete (Over X) :=
  have : IsConnected ℕᵒᵖ := IsCofiltered.isConnected ℕᵒᵖ
  IsReplete.of_reflectsEpimorphisms (Over.forget X)

/-- If `Over U` is replete, `U ⨯ -` preserves epimorphisms, and every second projection
`U ⨯ Z ⟶ Z` is an epimorphism, then `C` is replete. -/
theorem IsReplete.of_over_of_epi_snd [HasBinaryProducts C] (U : C)
    [(prod.functor.obj U).PreservesEpimorphisms] [∀ Z : C, Epi (prod.snd : U ⨯ Z ⟶ Z)]
    [IsReplete (Over U)] : IsReplete C :=
  IsReplete.of_reflectsEpimorphisms (Over.star U)

/-- **Repleteness descends from a slice over an epimorphic cover** (Bhatt–Scholze, Lemma 3.1.3).
In a category with binary products and a terminal object in which epimorphisms are stable under
base change, if `U ⟶ ⊤_ C` is an epimorphism and `Over U` is replete, then `C` is replete. -/
theorem IsReplete.of_over_epi [HasBinaryProducts C] [HasTerminal C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange] (U : C) [Epi (terminal.from U)]
    [IsReplete (Over U)] : IsReplete C :=
  have (Z : C) : Epi (prod.snd : U ⨯ Z ⟶ Z) :=
    MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
      (IsPullback.of_hasBinaryProduct' U Z) ‹_›
  IsReplete.of_over_of_epi_snd U

/-- In a category with binary products and a terminal object in which epimorphisms are stable under
base change, if `U ⟶ ⊤_ C` is an epimorphism, then `Over U` is replete if and only if `C` is
replete. -/
theorem isReplete_over_iff [HasBinaryProducts C] [HasTerminal C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange] (U : C) [Epi (terminal.from U)] :
    IsReplete (Over U) ↔ IsReplete C :=
  ⟨fun _ ↦ IsReplete.of_over_epi U, fun _ ↦ inferInstance⟩

/-- **Repleteness of slices descends along epimorphisms** (Bhatt–Scholze, Lemma 3.1.3). If
`f : X ⟶ Y` is an epimorphism in a category in which epimorphisms are stable under base change,
`Over.forget Y` preserves epimorphisms (for example when `C` has binary products), and `Over X` is
replete, then `Over Y` is replete. -/
theorem IsReplete.of_over_pullback_epi [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
    {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] [(Over.forget Y).PreservesEpimorphisms] [Epi f]
    [IsReplete (Over X)] : IsReplete (Over Y) :=
  have (Z : C) (g : Z ⟶ Y) : Epi (pullback.fst g f) :=
    MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
      (IsPullback.of_hasPullback g f).flip ‹_›
  IsReplete.of_reflectsEpimorphisms (Over.pullback f)

/-- **Repleteness descends from a jointly epimorphic family of slices.** If each `Over (U i)` is
replete, each `U i ⨯ -` preserves epimorphisms, and the second projections `U i ⨯ Z ⟶ Z` are
jointly epimorphic for every `Z : C`, then `C` is replete. -/
theorem IsReplete.of_forall_over_of_jointly_epi_snd {I : Type*} [HasBinaryProducts C] (U : I → C)
    [∀ i, (prod.functor.obj (U i)).PreservesEpimorphisms] [∀ i, IsReplete (Over (U i))]
    (hU : ∀ {Z W : C} (a b : Z ⟶ W),
      (∀ i, (prod.snd : U i ⨯ Z ⟶ Z) ≫ a = prod.snd ≫ b) → a = b) :
    IsReplete C :=
  IsReplete.of_jointlyReflectEpimorphisms
    (Over.jointlyFaithful_star U hU).jointlyReflectEpimorphisms

end TauCeti
