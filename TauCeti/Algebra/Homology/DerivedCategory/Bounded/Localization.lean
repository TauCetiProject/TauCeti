/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Acyclic

/-!
# The bounded derived category as a localization

Let `C` be an abelian category. Mathlib defines the bounded derived category
`DerivedCategory.Bounded C` as the full subcategory of `DerivedCategory C` on the objects that
are cohomologically bounded for the canonical t-structure. This file shows that it is the
localization of the homotopy category `TauCeti.HomotopyCategory.Bounded C` of strictly bounded
complexes with respect to the quasi-isomorphisms
(`TauCeti.HomotopyCategory.Bounded.quasiIso`), through the functor
`TauCeti.DerivedCategory.Bounded.Qh`. Hence functors out of `K^b(C)` inverting
quasi-isomorphisms descend to `D^b(C)`, together with their shift and triangulated structure.

The proof reduces to Mathlib's corresponding statement for bounded below complexes
(`DerivedCategory.Plus.Qh`). Inside the bounded below homotopy category, the bounded complexes
form a left localizing subcategory with respect to the acyclic complexes in the sense of Verdier:
a morphism from a complex strictly `≤ b` to an acyclic bounded below complex `Y` factors through
the canonical truncation `Y.truncLE b`, which is again acyclic and is bounded. Localizing
fully faithful localizer morphisms compose, so the induced functor from the localization of
`K^b(C)` to `D(C)` is fully faithful; its essential image is `D^b(C)`.

## References

* Mathlib's `Mathlib/Algebra/Homology/DerivedCategory/Plus.lean`, which proves the bounded below
  version and supplies the formal pattern followed here.
* Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque **239**
  (1996).
-/

public section

open CategoryTheory Category Limits Pretriangulated

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace DerivedCategory.Bounded

open _root_.DerivedCategory.TStructure

variable [HasDerivedCategory.{w} C]

variable (C) in
/-- The localization functor `K^b(C) ⥤ D^b(C)` from the homotopy category of bounded cochain
complexes to the bounded derived category. -/
noncomputable def Qh : HomotopyCategory.Bounded C ⥤ _root_.DerivedCategory.Bounded C :=
  t.bounded.lift (HomotopyCategory.Bounded.ι C ⋙ _root_.DerivedCategory.Qh) (by
    rintro ⟨K, hK⟩
    obtain ⟨K, rfl⟩ := _root_.HomotopyCategory.quotient_obj_surjective K
    rw [HomotopyCategory.bounded_quotient_obj_iff, CochainComplex.bounded_iff] at hK
    obtain ⟨a, b, _, _⟩ := hK
    exact ⟨⟨a, t.isGE_of_iso ((_root_.DerivedCategory.quotientCompQhIso C).symm.app K) a⟩,
      ⟨b, t.isLE_of_iso ((_root_.DerivedCategory.quotientCompQhIso C).symm.app K) b⟩⟩)

variable (C) in
/-- The functor `Qh C : K^b(C) ⥤ D^b(C)` is induced by
`DerivedCategory.Qh : HomotopyCategory C (.up ℤ) ⥤ DerivedCategory C`. -/
noncomputable def QhCompιIsoιCompQh :
    Qh C ⋙ _root_.DerivedCategory.Bounded.ι ≅
      HomotopyCategory.Bounded.ι C ⋙ _root_.DerivedCategory.Qh :=
  t.bounded.liftCompιIso _ _

/-! The bodies of `Qh` and `QhCompιIsoιCompQh` are not exposed, so the following characterizing
lemmas are proved with `(rfl)`, unfolding them inside this module, rather than exported as
definitional equalities. -/

/-- The underlying object in `D(C)` of the image of `X` under `Qh C` is the image of the underlying
complex under `DerivedCategory.Qh`. -/
lemma Qh_obj_obj (X : HomotopyCategory.Bounded C) :
    ((Qh C).obj X).obj = _root_.DerivedCategory.Qh.obj X.obj :=
  (rfl)

/-- The components of `QhCompιIsoιCompQh` are identities, transported along `Qh_obj_obj`. -/
@[simp]
lemma QhCompιIsoιCompQh_hom_app (X : HomotopyCategory.Bounded C) :
    (QhCompιIsoιCompQh C).hom.app X = eqToHom (Qh_obj_obj X) :=
  (rfl)

/-- The components of the inverse of `QhCompιIsoιCompQh` are identities, transported along
`Qh_obj_obj`. -/
@[simp]
lemma QhCompιIsoιCompQh_inv_app (X : HomotopyCategory.Bounded C) :
    (QhCompιIsoιCompQh C).inv.app X = eqToHom (Qh_obj_obj X).symm :=
  (rfl)

noncomputable instance : (Qh C).CommShift ℤ :=
  Functor.CommShift.ofComp (QhCompιIsoιCompQh C) ℤ

noncomputable instance : NatTrans.CommShift (QhCompιIsoιCompQh C).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

instance : (Qh C).IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right (QhCompιIsoιCompQh C)]
  infer_instance

instance : (Qh C).EssSurj where
  mem_essImage := by
    rintro ⟨X, ⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨K, _, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE_of_isLE a b
    refine ⟨⟨(_root_.HomotopyCategory.quotient C (.up ℤ)).obj K, ?_⟩,
      ⟨_root_.DerivedCategory.Bounded.ι.preimageIso
        ((_root_.DerivedCategory.quotientCompQhIso C).app _ ≪≫ e.symm)⟩⟩
    rw [HomotopyCategory.bounded_quotient_obj_iff, CochainComplex.bounded_iff]
    exact ⟨a, b, inferInstance, inferInstance⟩

section Localization

variable (C)

/-- The objects of the bounded below homotopy category which are isomorphic to bounded
complexes. -/
private abbrev boundedPlus : ObjectProperty (_root_.HomotopyCategory.Plus C) :=
  (HomotopyCategory.bounded C).isoClosure.inverseImage (_root_.HomotopyCategory.Plus.ι C)

/-- Inside the bounded below homotopy category, a morphism from a complex strictly `≤ b` to an
acyclic complex `Y` factors through the canonical truncation `Y.truncLE b`, which is bounded and
acyclic. -/
private instance : (boundedPlus C).IsVerdierLeftLocalizing
    (_root_.HomotopyCategory.Plus.subcategoryAcyclic C) where
  fac {X Y} φ hX hY := by
    obtain ⟨X₀, hX₀, ⟨e⟩⟩ := hX
    obtain ⟨X₀ : CochainComplex C ℤ, rfl⟩ := _root_.HomotopyCategory.quotient_obj_surjective X₀
    rw [HomotopyCategory.bounded_quotient_obj_iff] at hX₀
    obtain ⟨Y, hY'⟩ := Y
    obtain ⟨Y : CochainComplex C ℤ, rfl⟩ := _root_.HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨ψ, hψ⟩ := (_root_.HomotopyCategory.quotient C (.up ℤ)).map_surjective (e.inv ≫ φ.hom)
    replace hY : Y.Acyclic := by
      simpa only [ObjectProperty.prop_inverseImage_iff, ObjectProperty.ι_obj,
        _root_.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] using hY
    obtain ⟨c, _⟩ := (_root_.HomotopyCategory.plus_quotient_obj_iff Y).mp hY'
    obtain ⟨_, b, _, _⟩ := (CochainComplex.bounded_iff C X₀).mp hX₀
    have hZ : HomotopyCategory.bounded C
        ((_root_.HomotopyCategory.quotient C (.up ℤ)).obj (Y.truncLE b)) :=
      (HomotopyCategory.bounded_quotient_obj_iff _).mpr
        ((CochainComplex.bounded_iff C _).mpr ⟨c, b, inferInstance, inferInstance⟩)
    refine ⟨⟨_, HomotopyCategory.bounded_le_plus C _ hZ⟩,
      ObjectProperty.homMk (e.hom ≫ (_root_.HomotopyCategory.quotient C (.up ℤ)).map
        (inv (X₀.ιTruncLE b) ≫ CochainComplex.truncLEMap ψ b)),
      ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map (Y.ιTruncLE b)),
      ObjectProperty.le_isoClosure _ _ hZ, ?_, ?_⟩
    · exact (_root_.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mpr
        (hY.truncLE _)
    · ext
      simp [← Functor.map_comp, hψ]

/-- The inclusion of the bounded homotopy category into the objects of the bounded below homotopy
category which are isomorphic to bounded complexes. -/
private noncomputable abbrev toBoundedPlus :
    HomotopyCategory.Bounded C ⥤ (boundedPlus C).FullSubcategory :=
  (boundedPlus C).lift
    ((_root_.HomotopyCategory.plus C).lift (HomotopyCategory.Bounded.ι C)
      fun X ↦ HomotopyCategory.bounded_le_plus C _ X.property)
    fun X ↦ ObjectProperty.le_isoClosure _ _ X.property

private instance : (toBoundedPlus C).EssSurj where
  mem_essImage := by
    rintro ⟨X, Y, hY, ⟨e⟩⟩
    exact ⟨⟨Y, hY⟩, ⟨((boundedPlus C).fullyFaithfulι.comp
      (_root_.HomotopyCategory.Plus.fullyFaithfulι C)).preimageIso e.symm⟩⟩

private instance : (toBoundedPlus C).IsEquivalence :=
  have hG : (toBoundedPlus C).FullyFaithful := Functor.FullyFaithful.ofCompFaithful
    (G := (boundedPlus C).ι ⋙ _root_.HomotopyCategory.Plus.ι C)
    (HomotopyCategory.Bounded.fullyFaithfulι C)
  { full := hG.full
    faithful := hG.faithful }

/-- The inclusion of `K^b(C)` into the bounded below homotopy category, as a localizer morphism
for the quasi-isomorphisms. Since its functor is an equivalence onto the objects isomorphic to
bounded complexes, it induces an equivalence of localizations. -/
private noncomputable def toBoundedPlusLocalizerMorphism :
    LocalizerMorphism (HomotopyCategory.Bounded.subcategoryAcyclic C).trW
      ((_root_.HomotopyCategory.Plus.subcategoryAcyclic C).inverseImage
        (boundedPlus C).ι).trW where
  functor := toBoundedPlus C
  map _ _ f hf := by
    rw [ObjectProperty.inverseImage_trW_iff] at hf
    rw [MorphismProperty.inverseImage_iff, ObjectProperty.inverseImage_trW_iff,
      ObjectProperty.inverseImage_trW_iff]
    -- Both full subcategory inclusions send `f` to the same morphism of the homotopy category.
    exact hf

private instance : (toBoundedPlusLocalizerMorphism C).IsInduced where
  inverseImage_eq := by
    ext X Y f
    simp only [MorphismProperty.inverseImage_iff, ObjectProperty.inverseImage_trW_iff]
    -- Both full subcategory inclusions send `f` to the same morphism of the homotopy category.
    rfl

private instance : (toBoundedPlusLocalizerMorphism C).functor.IsEquivalence :=
  inferInstanceAs (toBoundedPlus C).IsEquivalence

/-- The functor `Qh C : K^b(C) ⥤ D^b(C)` is the localization of the bounded homotopy category at
the morphisms whose cone is acyclic. -/
instance : (Qh C).IsLocalization (HomotopyCategory.Bounded.subcategoryAcyclic C).trW := by
  have := (toBoundedPlusLocalizerMorphism C).isLocalizedEquivalence_of_isInduced
  exact ((toBoundedPlusLocalizerMorphism C).comp
    (((boundedPlus C).triangulatedLocalizerMorphism
      (_root_.HomotopyCategory.Plus.subcategoryAcyclic C)).comp
    ((_root_.HomotopyCategory.plus C).triangulatedLocalizerMorphism
      (_root_.HomotopyCategory.subcategoryAcyclic C)))).isLocalization_of_isLocalizedFullyFaithful
    (L₂ := _root_.DerivedCategory.Qh) (F := _root_.DerivedCategory.Bounded.ι)
    (QhCompιIsoιCompQh C).symm

/-- **The bounded derived category is a localization of the bounded homotopy category.** The
functor `Qh C : K^b(C) ⥤ D^b(C)` is the localization at the quasi-isomorphisms. -/
instance : (Qh C).IsLocalization (HomotopyCategory.Bounded.quasiIso C) := by
  rw [HomotopyCategory.Bounded.quasiIso_eq_subcategoryAcyclic_trW]
  infer_instance

instance : (Qh C).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _ (HomotopyCategory.Bounded.subcategoryAcyclic C).trW

end Localization

end DerivedCategory.Bounded

end TauCeti
