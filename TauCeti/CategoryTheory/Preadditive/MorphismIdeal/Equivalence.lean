/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Functor

/-!
# Equivalences of quotients by morphism ideals

Let `F : C ⥤ D` be an additive functor carrying a morphism ideal `I` of `C` into a morphism ideal
`J` of `D`, so that `F` induces `I.map J F hF : C/I ⥤ D/J`. This file records how the properties
of `F` pass to the induced functor:

* the induced functor is faithful exactly when `I` contains every morphism that `F` sends into
  `J`, that is when `J.comap F ≤ I`; no faithfulness of `F` itself is needed;
* it is full when `F` is full, and essentially surjective when `F` is;
* consequently an equivalence `e : C ≌ D` with `I = J.comap e.functor` induces an equivalence
  `C/I ≌ D/J`, whose inverse is the functor induced by `e.inverse`.

Pulling back along an equivalence is inverse to pulling back along its inverse, so the hypothesis
`I = J.comap e.functor` says precisely that `e` carries `I` onto `J`.

This is the mechanism by which an equivalence of additive categories matching two ideals, such as
an exact equivalence matching projective-injective objects, identifies the corresponding
quotient categories.

## Main definitions

* `TauCeti.MorphismIdeal.mapEquivalence`: the equivalence `C/I ≌ D/J` induced by an equivalence
  `C ≌ D` carrying `I` onto `J`.

## Main results

* `TauCeti.MorphismIdeal.faithful_lift_iff`, `full_lift`, `essSurj_lift`, and
  `isEquivalence_lift`: faithfulness, fullness, essential surjectivity, and equivalence for a
  functor lifted through the quotient by an ideal in its kernel.
* `TauCeti.MorphismIdeal.map_map_quotientFunctor_map_eq_iff`: two morphisms become equal under
  the induced functor exactly when `F` sends their difference into `J`.
* `TauCeti.MorphismIdeal.faithful_map_iff`: the induced functor is faithful if and only if
  `J.comap F ≤ I`.
* `TauCeti.MorphismIdeal.full_map` and `TauCeti.MorphismIdeal.essSurj_map`: fullness and
  essential surjectivity descend to quotients.
* `TauCeti.MorphismIdeal.isEquivalence_map`: an equivalence with `J.comap F ≤ I` induces an
  equivalence of quotients.
* `TauCeti.MorphismIdeal.comap_inverse_comap_functor` and
  `TauCeti.MorphismIdeal.comap_functor_comap_inverse`: pullback along an equivalence and along
  its inverse are mutually inverse.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995),
  Chapter IV, Section 1.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, LMS Lecture Note Series 119, CUP (1988), Section I.2.
-/

public section

universe v u v' u'

namespace TauCeti

open CategoryTheory

namespace MorphismIdeal

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/-! ### Properties of induced functors -/

section lift

variable (I : MorphismIdeal C) (F : C ⥤ D) [F.Additive] (hF : I ≤ F.kerIdeal)

/-- A functor lifted from a quotient is faithful exactly when its kernel is the quotient ideal. -/
theorem faithful_lift_iff : (I.lift F hF).Faithful ↔ F.kerIdeal ≤ I := by
  constructor
  · intro _ X Y f hf
    rw [← sub_zero f, ← I.quotientFunctor_map_eq_iff]
    apply (I.lift F hF).map_injective
    simpa only [Quotient.lift_map_functor_map, F.map_zero] using
      (Functor.mem_kerIdeal_hom F).1 hf
  · intro h
    refine Functor.faithful_of_comp_essSurj _ I.quotientFunctor fun X Y f g hfg ↦ ?_
    obtain ⟨f, rfl⟩ := I.quotientFunctor.map_surjective f
    obtain ⟨g, rfl⟩ := I.quotientFunctor.map_surjective g
    rw [I.quotientFunctor_map_eq_iff]
    apply (le_def.1 h) _
    rw [Functor.mem_kerIdeal_hom, F.map_sub]
    simpa only [Quotient.lift_map_functor_map] using sub_eq_zero.mpr hfg

/-- The lift of a full functor is full. -/
instance full_lift [F.Full] : (I.lift F hF).Full := by
  have : (I.quotientFunctor ⋙ I.lift F hF).Full := by
    rw [Quotient.lift_spec]
    infer_instance
  exact Functor.full_of_comp_essSurj _ I.quotientFunctor fun X Y φ ↦
    ⟨I.quotientFunctor.map ((I.quotientFunctor ⋙ I.lift F hF).preimage φ),
      (I.quotientFunctor ⋙ I.lift F hF).map_preimage φ⟩

/-- The lift of an essentially surjective functor is essentially surjective. -/
instance essSurj_lift [F.EssSurj] : (I.lift F hF).EssSurj := by
  have : (I.quotientFunctor ⋙ I.lift F hF).EssSurj := by
    rw [Quotient.lift_spec]
    infer_instance
  exact ⟨fun Y ↦ Functor.essImage_comp_apply_of_essSurj.1
    (Functor.EssSurj.mem_essImage (I.quotientFunctor ⋙ I.lift F hF) Y)⟩

/-- A full, essentially surjective functor induces an equivalence after quotienting by its
kernel ideal. -/
theorem isEquivalence_lift [F.Full] [F.EssSurj] (h : F.kerIdeal ≤ I) :
    (I.lift F hF).IsEquivalence where
  faithful := (I.faithful_lift_iff F hF).2 h
  full := inferInstance
  essSurj := inferInstance

end lift

section map

variable (I : MorphismIdeal C) (J : MorphismIdeal D) (F : C ⥤ D) [F.Additive]
  (hF : I ≤ J.comap F)

/-- Two morphisms of `C` have the same image under the quotient functor followed by the induced
functor exactly when `F` sends their difference into `J`. -/
theorem map_map_quotientFunctor_map_eq_iff {X Y : C} (f g : X ⟶ Y) :
    (I.map J F hF).map (I.quotientFunctor.map f) = (I.map J F hF).map (I.quotientFunctor.map g) ↔
      f - g ∈ (J.comap F).hom X Y := by
  -- The composite `I.quotientFunctor ⋙ I.map J F hF` is only propositionally equal to
  -- `F ⋙ J.quotientFunctor`, so we generalize it before substituting.
  suffices ∀ Φ : C ⥤ J.Quotient, Φ = F ⋙ J.quotientFunctor →
      (Φ.map f = Φ.map g ↔ f - g ∈ (J.comap F).hom X Y) from
    this _ (I.quotientFunctor_comp_map J F hF)
  rintro _ rfl
  rw [Functor.comp_map, Functor.comp_map, J.quotientFunctor_map_eq_iff, ← Functor.map_sub,
    mem_comap_hom]

/-- The functor induced on quotients is faithful exactly when every morphism that `F` sends into
`J` already lies in `I`. -/
theorem faithful_map_iff : (I.map J F hF).Faithful ↔ J.comap F ≤ I := by
  rw [map_eq_lift I J F hF]
  rw [I.faithful_lift_iff, kerIdeal_comp_quotientFunctor]

/-- The induced functor on quotients is full when `F` is full. -/
instance full_map [F.Full] : (I.map J F hF).Full := by
  rw [map_eq_lift I J F hF]
  infer_instance

/-- The induced functor on quotients is essentially surjective when `F` is essentially
surjective. -/
instance essSurj_map [F.EssSurj] : (I.map J F hF).EssSurj := by
  rw [map_eq_lift I J F hF]
  infer_instance

/-- An equivalence `F` with `J.comap F ≤ I` induces an equivalence of quotients. -/
theorem isEquivalence_map [F.IsEquivalence] (h : J.comap F ≤ I) :
    (I.map J F hF).IsEquivalence := by
  rw [map_eq_lift I J F hF]
  apply I.isEquivalence_lift
  simpa only [kerIdeal_comp_quotientFunctor] using h

end map

/-! ### Ideals along an equivalence -/

section equivalence

variable (e : C ≌ D) [e.functor.Additive]

/-- Pulling an ideal back along an equivalence and then along its inverse recovers the ideal. -/
@[simp]
theorem comap_inverse_comap_functor (J : MorphismIdeal D) :
    (J.comap e.functor).comap e.inverse = J := by
  rw [← comap_comp, J.comap_eq_of_iso e.counitIso, comap_id]

/-- Pulling an ideal back along the inverse of an equivalence and then along the equivalence
recovers the ideal. -/
@[simp]
theorem comap_functor_comap_inverse (I : MorphismIdeal C) :
    (I.comap e.inverse).comap e.functor = I := by
  rw [← comap_comp, ← I.comap_eq_of_iso e.unitIso, comap_id]

variable (I : MorphismIdeal C) (J : MorphismIdeal D)

/-- If `e` carries `I` onto `J`, then its inverse carries `J` into `I`. -/
theorem le_comap_inverse (h : I = J.comap e.functor) : J ≤ I.comap e.inverse := by
  rw [h, comap_inverse_comap_functor]

/-- An equivalence `e : C ≌ D` carrying the ideal `I` onto the ideal `J` induces an equivalence
of the quotient categories `C/I ≌ D/J`. Its functor and inverse are the functors induced by
`e.functor` and `e.inverse`. -/
noncomputable def mapEquivalence (h : I = J.comap e.functor) : I.Quotient ≌ J.Quotient :=
  CategoryTheory.Equivalence.mk (I.map J e.functor h.le)
    (J.map I e.inverse (le_comap_inverse e I J h))
    (eqToIso (I.map_id).symm ≪≫ I.mapNatIso I (by simp)
        (I.le_comap_comp J I e.functor e.inverse h.le (le_comap_inverse e I J h)) e.unitIso ≪≫
      eqToIso (I.map_comp J I e.functor e.inverse h.le (le_comap_inverse e I J h)))
    (eqToIso (J.map_comp I J e.inverse e.functor (le_comap_inverse e I J h) h.le).symm ≪≫
      J.mapNatIso J (J.le_comap_comp I J e.inverse e.functor (le_comap_inverse e I J h) h.le)
        (by simp) e.counitIso ≪≫
      eqToIso J.map_id)

/-- The functor of the induced equivalence is the functor induced by `e.functor`. -/
@[simp]
theorem mapEquivalence_functor (h : I = J.comap e.functor) :
    (mapEquivalence e I J h).functor = I.map J e.functor h.le :=
  (rfl)

/-- The inverse of the induced equivalence is the functor induced by `e.inverse`. -/
@[simp]
theorem mapEquivalence_inverse (h : I = J.comap e.functor) :
    (mapEquivalence e I J h).inverse = J.map I e.inverse (le_comap_inverse e I J h) :=
  (rfl)

end equivalence

end MorphismIdeal

end TauCeti
