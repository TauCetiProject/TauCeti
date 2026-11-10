/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Plus
public import TauCeti.CategoryTheory.Exact.HomologicalComplex.Injective.Basic
public import TauCeti.CategoryTheory.Exact.HomologicalComplex.Injective.Resolution
public import TauCeti.CategoryTheory.Triangulated.Orthogonal.Localization

/-!
# The bounded below derived category via injectives

Let `E` be an exact structure with enough injectives. The homotopy category `K⁺(Inj E)` of bounded
below complexes of `E`-injective objects is equivalent to the bounded below derived category
`D⁺(E)`, as a triangulated category (Bühler, Example 10.23; Keller).

The proof combines two facts with the general description of a Verdier quotient by a right
orthogonal class, `CategoryTheory.ObjectProperty.isEquivalence_ι_comp_of_le_rightOrthogonal`:

* a map from an acyclic complex to a bounded below complex of injectives is null-homotopic
  (`TauCeti.ExactStructure.AcyclicData.quotient_map_eq_zero`), so the bounded below complexes of
  injectives are right orthogonal to the acyclic complexes;
* every bounded below complex has an injective resolution
  (`TauCeti.ExactStructure.EnoughInjectives.exists_injectiveResolution`).

## Main definitions

* `TauCeti.ExactStructure.plusInjective`: the objects of the homotopy category isomorphic to the
  class of a bounded below complex of injectives, a triangulated subcategory.
* `TauCeti.ExactStructure.injectivePlus`: the same objects in `K⁺(C)`.

## Main results

* `TauCeti.ExactStructure.injectivePlus_le_rightOrthogonal`: bounded below complexes of
  injectives are right orthogonal to the acyclic complexes in `K⁺(C)`.
* `TauCeti.ExactStructure.EnoughInjectives.isEquivalence_injectivePlus_ι_comp_Q`: with enough
  injectives, `K⁺(Inj E) ⥤ D⁺(E)` is an equivalence. It is a triangulated functor.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Theorem 10.22 and Example 10.23.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Math. **67** (1990),
  379--417, Section 4.1.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : ExactStructure C)

/-- The objects of the homotopy category isomorphic to the class of a bounded below complex of
`E`-injective objects. -/
def plusInjective : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun X ↦
  ∃ I : CochainComplex C ℤ, CochainComplex.plus C I ∧ (∀ n, E.isInjective (I.X n)) ∧
    Nonempty (X ≅ (HomotopyCategory.quotient C (.up ℤ)).obj I)

/-- An object of the homotopy category is in `E.plusInjective` exactly when it is isomorphic to the
class of a bounded below complex of injectives. -/
theorem plusInjective_iff (X : HomotopyCategory C (.up ℤ)) :
    E.plusInjective X ↔ ∃ I : CochainComplex C ℤ, CochainComplex.plus C I ∧
      (∀ n, E.isInjective (I.X n)) ∧ Nonempty (X ≅ (HomotopyCategory.quotient C (.up ℤ)).obj I) :=
  Iff.rfl

instance : E.plusInjective.IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨I, hb, hI, ⟨e'⟩⟩ ↦ ⟨I, hb, hI, ⟨e.symm ≪≫ e'⟩⟩

instance : E.plusInjective.ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient C (.up ℤ)).obj 0,
    Functor.map_isZero _ (isZero_zero _), 0, ⟨0, inferInstance⟩,
    fun n ↦ E.isInjective.prop_of_isZero
      ((HomologicalComplex.eval C _ n).map_isZero (isZero_zero _)), ⟨Iso.refl _⟩⟩

instance : E.plusInjective.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ ⟨I, hb, hI, ⟨e⟩⟩ ↦ ⟨I⟦n⟧,
    (CochainComplex.plus C).le_shift n I hb, fun k ↦ hI (k + n),
    ⟨(shiftFunctor _ n).mapIso e ≪≫
      ((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app I⟩⟩⟩

instance : E.plusInjective.IsTriangulatedClosed₃ where
  ext₃' T hT := fun ⟨K₁, ⟨n₁, _⟩, hI₁, ⟨e₁⟩⟩ ⟨K₂, ⟨n₂, _⟩, hI₂, ⟨e₂⟩⟩ ↦ by
    obtain ⟨f, hf⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective
      (e₁.inv ≫ T.mor₁ ≫ e₂.hom)
    refine ObjectProperty.le_isoClosure _ _ ⟨CochainComplex.mappingCone f,
      ⟨min (n₁ - 1) n₂, CochainComplex.isStrictlyGE_mappingCone f n₁ n₂ _⟩,
      E.isInjective_mappingCone_X f hI₁ hI₂,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
        (HomotopyCategory.mappingCone_triangleh_distinguished f) e₁ e₂ ?_)⟩⟩
    -- The goal is stated through the triangle of the mapping cone; its first morphism is the
    -- class of `f`.
    change T.mor₁ ≫ e₂.hom = e₁.hom ≫ (HomotopyCategory.quotient C (.up ℤ)).map f
    rw [hf]
    simp

instance : E.plusInjective.IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The bounded below complexes of injectives, as a triangulated subcategory `K⁺(Inj E)` of
`K⁺(C)`. -/
def injectivePlus : ObjectProperty (HomotopyCategory.Plus C) :=
  E.plusInjective.inverseImage (HomotopyCategory.Plus.ι C)

/-- An object of `K⁺(C)` is in `E.injectivePlus` exactly when its image in the homotopy category is
in `E.plusInjective`. -/
@[simp]
theorem injectivePlus_iff (X : HomotopyCategory.Plus C) :
    E.injectivePlus X ↔ E.plusInjective ((HomotopyCategory.Plus.ι C).obj X) :=
  Iff.rfl

instance : E.injectivePlus.IsTriangulated := by
  dsimp only [injectivePlus]
  infer_instance

/-- **Bounded below complexes of injectives are right orthogonal to acyclic complexes** in
`K⁺(C)`: every morphism from an acyclic complex to a bounded below complex of injectives is
zero. -/
theorem injectivePlus_le_rightOrthogonal : E.injectivePlus ≤ E.acyclicPlus.rightOrthogonal := by
  intro Y hY X f hX
  obtain ⟨I, ⟨n, _⟩, hI, ⟨e₂⟩⟩ := (E.plusInjective_iff _).1 ((E.injectivePlus_iff Y).1 hY)
  obtain ⟨K, hK, ⟨e₁⟩⟩ := (E.homotopyAcyclic_iff _).1 ((E.acyclicPlus_iff X).1 hX)
  obtain ⟨hK⟩ := (E.acyclic_iff K).1 hK
  obtain ⟨φ, hφ⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective (e₁.inv ≫ f.hom ≫ e₂.hom)
  have h : e₁.inv ≫ f.hom ≫ e₂.hom = 0 := by rw [← hφ, hK.quotient_map_eq_zero φ hI n]
  ext
  simpa using h

namespace EnoughInjectives

variable {E} (hE : E.EnoughInjectives)

include hE in
/-- **Injective resolutions in `K⁺(C)`**: every object of `K⁺(C)` has a morphism with acyclic cone
to a bounded below complex of injectives. -/
theorem exists_acyclicPlus_trW_injectivePlus (X : HomotopyCategory.Plus C) :
    ∃ (Y : HomotopyCategory.Plus C) (s : X ⟶ Y), E.injectivePlus Y ∧ E.acyclicPlus.trW s := by
  obtain ⟨n, _⟩ := (HomotopyCategory.plus_quotient_obj_iff X.obj.as).1 X.property
  obtain ⟨I, α, _, hI, hα⟩ := hE.exists_injectiveResolution X.obj.as n
  exact ⟨⟨(HomotopyCategory.quotient C (.up ℤ)).obj I,
      (HomotopyCategory.plus_quotient_obj_iff I).2 ⟨n, inferInstance⟩⟩,
    ObjectProperty.homMk ((HomotopyCategory.quotient C (.up ℤ)).map α),
    ⟨I, ⟨n, inferInstance⟩, hI, ⟨Iso.refl _⟩⟩,
    (E.acyclicPlus_trW_iff _).2 (E.homotopyAcyclic_trW_quotient_map α hα)⟩

include hE in
/-- **`K⁺(Inj E) ≃ D⁺(E)`** (Bühler, Example 10.23): for an exact structure with enough injectives,
the Verdier quotient functor restricts to an equivalence from the bounded below complexes of
injectives to the bounded below derived category. -/
theorem isEquivalence_injectivePlus_ι_comp_Q :
    (E.injectivePlus.ι ⋙ PlusDerivedCategory.Q E).IsEquivalence :=
  ObjectProperty.isEquivalence_ι_comp_of_le_rightOrthogonal _ E.injectivePlus_le_rightOrthogonal
    hE.exists_acyclicPlus_trW_injectivePlus

end EnoughInjectives

/-- The functor `K⁺(Inj E) ⥤ D⁺(E)` is triangulated. -/
example : (E.injectivePlus.ι ⋙ PlusDerivedCategory.Q E).IsTriangulated := inferInstance

end TauCeti.ExactStructure
