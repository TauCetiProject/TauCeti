/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Prorepresentability

/-!
# Any two fibre functors of a Galois category are isomorphic

Let `C` be a Galois category and `F`, `G : C ⥤ FintypeCat` two fibre functors. This file shows
that every natural transformation `F ⟶ G` is an isomorphism, and that such a natural
transformation exists. Hence the fibre functors of `C` form a connected groupoid: in the
language of étale fundamental groups, any two base points are joined by a path, and conjugation
along a path (`CategoryTheory.Iso.conjAut`) identifies the fundamental groups `Aut F` and
`Aut G`, non-canonically.

Mathlib proves the special case of endomorphisms, `FibreFunctor.end_isIso`, for fibre functors
valued in `FintypeCat` of the morphism universe of `C`. Here both statements hold for any
fibre functors valued in `FintypeCat` of an arbitrary universe.

That `η : F ⟶ G` is bijective on the fibre of `X` is checked through Galois objects.
Two points of `F.obj X` come from a single point `a` of a Galois object `A` along two maps
`A ⟶ X`, and these maps agree because they agree on the point `η.app A a` of the connected
object `A`. Any point of `G.obj X` comes from a point of a Galois object `A`, and `Aut A` acts
transitively on `G.obj A`, so it is in the image of `η`.

For existence, `F` is pro-represented by its pointed Galois objects
(`PointedGaloisObject.isColimit`), so by the pro-Coyoneda lemma
(`colimitCoyonedaHomIsoLimit'`) a natural transformation `F ⟶ G` is the same as a compatible
family of points of `G` on these objects; Mathlib's `endEquivSectionsFibers` is the case
`G = F`. The fibres of `G` on Galois objects are finite and nonempty and the pointed Galois
objects form a cofiltered category, so such a family exists by
`nonempty_sections_of_finite_cofiltered_system`. The general universe case reduces
to the case of the morphism universe of `C` along the equivalence `FintypeCat.uSwitch`.

## Main results

* `CategoryTheory.PreGaloisCategory.FiberFunctor.bijective_app`: a natural transformation
  between fibre functors is bijective on every fibre.
* `CategoryTheory.PreGaloisCategory.FiberFunctor.isIso`: every natural transformation between
  fibre functors is an isomorphism.
* `CategoryTheory.PreGaloisCategory.FiberFunctor.nonempty_hom`: there is a natural
  transformation between any two fibre functors.
* `CategoryTheory.PreGaloisCategory.FiberFunctor.nonempty_iso`: any two fibre functors are
  isomorphic.

## References

* A. Grothendieck, *SGA 1*, Exposé V, §5.
* H. W. Lenstra, *Galois theory for schemes*, Section 3.
* The Stacks Project, Section 58.3, *Galois categories*.
-/

public section

universe u₁ u₂ w

namespace CategoryTheory.PreGaloisCategory

open Limits

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]

namespace FiberFunctor

section Bijective

variable {F G : C ⥤ FintypeCat.{w}} [FiberFunctor F] [FiberFunctor G]

/-- **A natural transformation between fibre functors is bijective on every fibre.** -/
theorem bijective_app (η : F ⟶ G) (X : C) : Function.Bijective (η.app X) := by
  have nat {Y Z : C} (f : Y ⟶ Z) (y : F.obj Y) : η.app Z (F.map f y) = G.map f (η.app Y y) :=
    congr($(η.naturality f) y)
  constructor
  · -- Two points of `F.obj X` come from one point of a Galois object along two maps.
    intro x₁ x₂ h
    obtain ⟨A, f, a, _, hf⟩ :=
      exists_hom_from_galois_of_fiber F (X ⨯ X) ((fiberBinaryProductEquiv F X X).symm (x₁, x₂))
    have h₁ : F.map (f ≫ prod.fst) a = x₁ := by simp [hf]
    have h₂ : F.map (f ≫ prod.snd) a = x₂ := by simp [hf]
    have : f ≫ prod.fst = f ≫ prod.snd :=
      evaluation_injective_of_isConnected G A X (η.app A a) <| by
        simpa only [← nat, h₁, h₂] using h
    rw [← h₁, ← h₂, this]
  · -- A point of `G.obj X` comes from a Galois object, on whose fibre `Aut A` is transitive.
    intro y
    obtain ⟨A, g, b, _, hg⟩ := exists_hom_from_galois_of_fiber G X y
    obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut A) (η.app A a) b
    refine ⟨F.map (σ.asIso.hom ≫ g) a, ?_⟩
    rw [nat, G.map_comp, FintypeCat.comp_apply, ← hg, ← hσ, smul_def]

/-- **Every natural transformation between fibre functors is an isomorphism.** -/
instance isIso (η : F ⟶ G) : IsIso η :=
  have (X : C) : IsIso (η.app X) :=
    (ConcreteCategory.isIso_iff_bijective (η.app X)).mpr (bijective_app η X)
  NatIso.isIso_of_isIso_app η

end Bijective

section Existence

/-- The case of fibre functors valued in `FintypeCat` of the morphism universe of `C`, where `F`
is pro-represented by its pointed Galois objects. -/
private theorem nonempty_hom_aux (F G : C ⥤ FintypeCat.{u₂}) [FiberFunctor F] [FiberFunctor G] :
    Nonempty (F ⟶ G) := by
  -- By the pro-Coyoneda lemma, a natural transformation `F ⟶ G` is a compatible family of
  -- points of `G` on the pointed Galois objects of `F`; these fibres are finite and nonempty.
  let D := PointedGaloisObject.incl F ⋙ (G ⋙ FintypeCat.incl) ⋙ uliftFunctor.{u₁}
  have (A : PointedGaloisObject F) : Finite (D.obj A) :=
    inferInstanceAs (Finite (ULift (G.obj A.obj)))
  have (A : PointedGaloisObject F) : Nonempty (D.obj A) :=
    have := A.isGalois
    ⟨⟨(nonempty_fiber_of_isConnected G A.obj).some⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system D
  let η : F ⋙ FintypeCat.incl ⟶ G ⋙ FintypeCat.incl :=
    (colimit.isoColimitCocone ⟨_, PointedGaloisObject.isColimit F⟩).inv ≫
      (colimitCoyonedaHomIsoLimit' _ _).inv ((Types.limitEquivSections D).symm ⟨s, hs⟩)
  exact ⟨(Functor.FullyFaithful.whiskeringRight
    (Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl) C).preimage η⟩

end Existence

variable (F G : C ⥤ FintypeCat.{w}) [FiberFunctor F] [FiberFunctor G]

/-- **There is a natural transformation between any two fibre functors** of a Galois
category. -/
theorem nonempty_hom : Nonempty (F ⟶ G) := by
  obtain ⟨η⟩ := nonempty_hom_aux (F ⋙ FintypeCat.uSwitch.{w, u₂}) (G ⋙ FintypeCat.uSwitch)
  exact ⟨(Functor.FullyFaithful.whiskeringRight
    (Functor.FullyFaithful.ofFullyFaithful FintypeCat.uSwitch.{w, u₂}) C).preimage η⟩

/-- **Any two fibre functors of a Galois category are isomorphic.** -/
theorem nonempty_iso : Nonempty (F ≅ G) :=
  (nonempty_hom F G).map fun η ↦ asIso η

end FiberFunctor

end CategoryTheory.PreGaloisCategory
