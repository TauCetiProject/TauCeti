/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic

/-!
# Additive functors on bounded homotopy categories

An additive functor acts termwise on bounded complexes and hence on their bounded homotopy
categories. This action commutes with suspension and preserves distinguished triangles.
An additive equivalence induces an equivalence of bounded homotopy categories. In particular,
an internal grading shift lifts termwise without shifting the cohomological degree.

The construction and the composition isomorphism follow Mathlib's corresponding development
for bounded-below homotopy categories in `Mathlib/Algebra/Homology/HomotopyCategory/Plus.lean`.
The comparison with single complexes uses Mathlib's `singleMapHomologicalComplex`.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v v' v'' u u' u''

namespace CategoryTheory

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

namespace Functor

section Complex

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
  [F.PreservesZeroMorphisms]

/-- Applying a zero-morphism-preserving functor termwise preserves boundedness. -/
theorem bounded_mapHomologicalComplex {K : CochainComplex C ℤ}
    (hK : CochainComplex.bounded C K) :
    CochainComplex.bounded D ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨a, b, ha, hb⟩ := (CochainComplex.bounded_iff C K).mp hK
  let := ha
  let := hb
  exact (CochainComplex.bounded_iff D _).mpr ⟨a, b, inferInstance, inferInstance⟩

end Complex

variable [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]

/-- Applying an additive functor preserves boundedness in the homotopy category. -/
theorem bounded_mapHomotopyCategory {K : HomotopyCategory C (.up ℤ)}
    (hK : TauCeti.HomotopyCategory.bounded C K) :
    TauCeti.HomotopyCategory.bounded D ((F.mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  exact (TauCeti.HomotopyCategory.bounded_quotient_obj_iff _).mpr
    (F.bounded_mapHomologicalComplex
      ((TauCeti.HomotopyCategory.bounded_quotient_obj_iff _).mp hK))

/-- The functor on bounded homotopy categories induced termwise by an additive functor. -/
@[implicit_reducible]
def mapHomotopyCategoryBounded :
    TauCeti.HomotopyCategory.Bounded C ⥤ TauCeti.HomotopyCategory.Bounded D :=
  (TauCeti.HomotopyCategory.bounded D).lift
    (TauCeti.HomotopyCategory.Bounded.ι C ⋙ F.mapHomotopyCategory (.up ℤ))
    (fun X ↦ F.bounded_mapHomotopyCategory X.property)

/-- The induced bounded functor agrees with the ordinary homotopy functor after inclusion. -/
def mapHomotopyCategoryBoundedCompι :
    F.mapHomotopyCategoryBounded ⋙ TauCeti.HomotopyCategory.Bounded.ι D ≅
      TauCeti.HomotopyCategory.Bounded.ι C ⋙ F.mapHomotopyCategory (.up ℤ) :=
  ObjectProperty.liftCompιIso ..

/-- The underlying object is the termwise image in the ordinary homotopy category. -/
@[simp]
theorem mapHomotopyCategoryBounded_obj_obj (K : TauCeti.HomotopyCategory.Bounded C) :
    (F.mapHomotopyCategoryBounded.obj K).obj =
      (F.mapHomotopyCategory (.up ℤ)).obj K.obj := (rfl)

/-- The underlying map is the image in the ordinary homotopy category. -/
@[simp]
theorem mapHomotopyCategoryBounded_map_hom {K L : TauCeti.HomotopyCategory.Bounded C}
    (f : K ⟶ L) :
    (F.mapHomotopyCategoryBounded.map f).hom =
      eqToHom (F.mapHomotopyCategoryBounded_obj_obj K) ≫
        (F.mapHomotopyCategory (.up ℤ)).map f.hom ≫
        eqToHom (F.mapHomotopyCategoryBounded_obj_obj L).symm := by
  simp [mapHomotopyCategoryBounded]

instance : F.mapHomotopyCategoryBounded.Additive := by
  dsimp only [mapHomotopyCategoryBounded]
  infer_instance

noncomputable instance : F.mapHomotopyCategoryBounded.CommShift ℤ :=
  inferInstanceAs (((TauCeti.HomotopyCategory.bounded D).lift
    (TauCeti.HomotopyCategory.Bounded.ι C ⋙ F.mapHomotopyCategory (.up ℤ))
    (fun X ↦ F.bounded_mapHomotopyCategory X.property)).CommShift ℤ)

instance : NatTrans.CommShift F.mapHomotopyCategoryBoundedCompι.hom ℤ := by
  exact ObjectProperty.commShift_liftCompιIso_hom (A := ℤ)
    (TauCeti.HomotopyCategory.bounded D)
    (TauCeti.HomotopyCategory.Bounded.ι C ⋙ F.mapHomotopyCategory (.up ℤ))
    (fun X ↦ F.bounded_mapHomotopyCategory X.property)

instance [HasZeroObject C] [HasBinaryBiproducts C] [HasZeroObject D] [HasBinaryBiproducts D] :
    F.mapHomotopyCategoryBounded.IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right F.mapHomotopyCategoryBoundedCompι]
  infer_instance

/-- Composition of additive functors agrees with composition of their bounded homotopy functors. -/
def mapHomotopyCategoryBoundedCompIso {E : Type u''} [Category.{v''} E] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive]
    (e : F ⋙ G ≅ H) :
    F.mapHomotopyCategoryBounded ⋙ G.mapHomotopyCategoryBounded ≅
      H.mapHomotopyCategoryBounded :=
  ((TauCeti.HomotopyCategory.Bounded.fullyFaithfulι E).whiskeringRight _).preimageIso
    (isoWhiskerLeft (TauCeti.HomotopyCategory.Bounded.ι C)
      (mapHomotopyCategoryCompIso e (.up ℤ)))

variable (C) in
/-- The bounded homotopy functor induced by the identity is isomorphic to the identity. -/
def mapHomotopyCategoryBoundedIdIso :
    (𝟭 C).mapHomotopyCategoryBounded ≅ 𝟭 (TauCeti.HomotopyCategory.Bounded C) :=
  ((TauCeti.HomotopyCategory.Bounded.fullyFaithfulι C).whiskeringRight _).preimageIso
    (isoWhiskerLeft (TauCeti.HomotopyCategory.Bounded.ι C)
      (Quotient.natIsoLift _
        ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ) ≪≫
          isoWhiskerRight (mapHomologicalComplexIdIso C (.up ℤ))
            (HomotopyCategory.quotient C (.up ℤ)) ≪≫
          (HomotopyCategory.quotient C (.up ℤ)).leftUnitor ≪≫
          (HomotopyCategory.quotient C (.up ℤ)).rightUnitor.symm)))

section Single

variable [HasZeroObject C] [HasZeroObject D]

/-- Termwise application commutes with placing an object in any cohomological degree. -/
noncomputable def mapHomotopyCategoryBoundedSingleFunctorIso (n : ℤ) :
    TauCeti.HomotopyCategory.Bounded.singleFunctor C n ⋙ F.mapHomotopyCategoryBounded ≅
      F ⋙ TauCeti.HomotopyCategory.Bounded.singleFunctor D n :=
  ((TauCeti.HomotopyCategory.Bounded.fullyFaithfulι D).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ F.mapHomotopyCategoryBoundedCompι ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (TauCeti.HomotopyCategory.Bounded.singleFunctorCompιIso C n) _ ≪≫
      isoWhiskerRight (HomotopyCategory.singleFunctorPostcompQuotientIso C n) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (F.mapHomotopyCategoryFactors (.up ℤ)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft F (HomotopyCategory.singleFunctorPostcompQuotientIso D n).symm ≪≫
      isoWhiskerLeft F (TauCeti.HomotopyCategory.Bounded.singleFunctorCompιIso D n).symm ≪≫
      (Functor.associator _ _ _).symm)

end Single

end Functor

namespace Equivalence

variable [Preadditive C] [Preadditive D]

/-- An additive equivalence induces an equivalence of bounded homotopy categories, with both
functors acting termwise. -/
noncomputable def mapHomotopyCategoryBounded (e : C ≌ D) [e.functor.Additive] :
    TauCeti.HomotopyCategory.Bounded C ≌ TauCeti.HomotopyCategory.Bounded D := by
  letI := e.inverse_additive
  exact Equivalence.mk e.functor.mapHomotopyCategoryBounded e.inverse.mapHomotopyCategoryBounded
    ((Functor.mapHomotopyCategoryBoundedIdIso C).symm ≪≫
      (Functor.mapHomotopyCategoryBoundedCompIso e.unitIso.symm).symm)
    (Functor.mapHomotopyCategoryBoundedCompIso e.counitIso ≪≫
      Functor.mapHomotopyCategoryBoundedIdIso D)

/-- The forward bounded equivalence acts by the original forward functor termwise. -/
@[simp]
theorem mapHomotopyCategoryBounded_functor (e : C ≌ D) [e.functor.Additive] :
    e.mapHomotopyCategoryBounded.functor = e.functor.mapHomotopyCategoryBounded := (rfl)

/-- The inverse bounded equivalence acts by the original inverse functor termwise. -/
@[simp]
theorem mapHomotopyCategoryBounded_inverse (e : C ≌ D) [e.functor.Additive] :
    e.mapHomotopyCategoryBounded.inverse = e.inverse.mapHomotopyCategoryBounded := by
  let := e.inverse_additive
  rfl

instance (e : C ≌ D) [e.functor.Additive] : e.mapHomotopyCategoryBounded.functor.Additive :=
  inferInstanceAs e.functor.mapHomotopyCategoryBounded.Additive

noncomputable instance (e : C ≌ D) [e.functor.Additive] :
    e.mapHomotopyCategoryBounded.functor.CommShift ℤ :=
  inferInstanceAs (e.functor.mapHomotopyCategoryBounded.CommShift ℤ)

instance (e : C ≌ D) [e.functor.Additive] [HasZeroObject C] [HasBinaryBiproducts C]
    [HasZeroObject D] [HasBinaryBiproducts D] :
    e.mapHomotopyCategoryBounded.functor.IsTriangulated :=
  inferInstanceAs e.functor.mapHomotopyCategoryBounded.IsTriangulated

end Equivalence

end CategoryTheory
