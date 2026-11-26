/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Recognizing localization functors up to isomorphism

Mathlib characterizes a localization functor `L : C ⥤ D` with respect to `W` by the strict
universal property of `W.Localization` (`CategoryTheory.Functor.IsLocalization.mk'`). Here a
functor inverting `W` is recognized as a localization from universal properties that only hold up
to isomorphism, as they arise from `∞`-categorical localizations: the localization functor
`W.Q` factors through `L` up to isomorphism, and precomposition with `L` reflects isomorphisms of
endofunctors of `D`.

## Main results

* `CategoryTheory.Functor.IsLocalization.of_nonempty_iso`: the recognition criterion.
-/

public section

namespace CategoryTheory.Functor.IsLocalization

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)

/-- A functor `L : C ⥤ D` inverting `W` is a localization with respect to `W` when the
localization functor `W.Q` factors through `L` up to isomorphism, and two endofunctors of `D`
are isomorphic as soon as their composites with `L` are. -/
theorem of_nonempty_iso (hL : W.IsInvertedBy L)
    (hS : ∃ G : D ⥤ W.Localization, Nonempty (L ⋙ G ≅ W.Q))
    (hR : ∀ F₁ F₂ : D ⥤ D, Nonempty (L ⋙ F₁ ≅ L ⋙ F₂) → Nonempty (F₁ ≅ F₂)) :
    L.IsLocalization W := by
  obtain ⟨G, ⟨e⟩⟩ := hS
  let F := Localization.Construction.lift L hL
  have hF : W.Q ⋙ F = L := Localization.Construction.fac L hL
  -- The functor `F ⋙ G` is isomorphic to the identity since its composite with `W.Q` is.
  let e₁ : F ⋙ G ≅ 𝟭 _ := (Localization.fullyFaithfulWhiskeringLeft W.Q W _).preimageIso
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (eqToIso hF) G ≪≫ e ≪≫
      (Functor.rightUnitor _).symm)
  -- The functor `G ⋙ F` is isomorphic to the identity since its composite with `L` is.
  obtain ⟨e₂⟩ : Nonempty (G ⋙ F ≅ 𝟭 D) := hR _ _ ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e F ≪≫ eqToIso hF ≪≫ (Functor.rightUnitor _).symm⟩
  exact ⟨hL, (CategoryTheory.Equivalence.mk F G e₁.symm e₂).isEquivalence_functor⟩

end CategoryTheory.Functor.IsLocalization
