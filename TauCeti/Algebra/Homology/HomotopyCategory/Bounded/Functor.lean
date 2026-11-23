/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.CochainComplex.SingleFunctors
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Mk

/-!
# Additive functors on bounded homotopy categories

An additive functor acts termwise on bounded complexes and hence on their bounded homotopy
categories. This action commutes with suspension and preserves distinguished triangles.
An additive equivalence induces an equivalence of bounded homotopy categories. In particular,
an internal grading shift lifts termwise without shifting the cohomological degree.

The construction and the composition isomorphism follow Mathlib's corresponding development
for bounded-below homotopy categories in `Mathlib/Algebra/Homology/HomotopyCategory/Plus.lean`.
The comparison with single complexes uses Mathlib's `singleMapHomologicalComplex`.

On explicit complexes, the image of the class `TauCeti.HomotopyCategory.Bounded.mk K hK` is the
class of the termwise image of `K`, naturally in chain maps. For single complexes this
identification is compatible with `mapHomotopyCategoryBoundedSingleFunctorIso` and with the
identifications `TauCeti.HomotopyCategory.Bounded.mkSingleIsoShift` of shifted single complexes.

## Main definitions

* `CategoryTheory.Functor.mapHomotopyCategoryBounded`: the functor `Kᵇ(C) ⥤ Kᵇ(D)`.
* `CategoryTheory.Functor.mapHomotopyCategoryBoundedSingleFunctorIso`: it commutes with placing
  an object in a given degree.
* `CategoryTheory.Functor.mapHomotopyCategoryBoundedMkIso` and
  `CategoryTheory.Functor.mapHomotopyCategoryBoundedQuotientObjIso`: the image of the class of a
  bounded complex is the class of its termwise image.
* `CategoryTheory.Functor.mapHomotopyCategoryBoundedMkSingleIso`: the image of the class of
  `X[n]` is the class of `(F X)[n]`.

## Main results

* `CategoryTheory.Functor.mkMap_comp_mapHomotopyCategoryBoundedMkIso_inv`: naturality of
  `mapHomotopyCategoryBoundedMkIso`.
* `CategoryTheory.Functor.ι_map_mapHomotopyCategoryBounded_commShiftIso_hom_app`: the commutation
  with shifts, compared with the one of `F.mapHomotopyCategory`.
* `CategoryTheory.Functor.mapHomotopyCategoryBoundedSingleFunctorIso_hom_app_comp` and
  `mkSingleIsoShift_hom_comp_shift_mapHomotopyCategoryBoundedMkSingleIso_inv` (in the same
  namespace): `mapHomotopyCategoryBoundedMkSingleIso` is compatible with `singleFunctorObjIsoMk`
  and with shifts.
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

section Shift

/-- **The functor `K(C) ⥤ K(D)` commutes with shifts compatibly with the termwise functor**: on the
class of a complex `K`, its commutation with the shift is the class of the commutation of
`F.mapHomologicalComplex` with the shift. -/
@[reassoc]
theorem mapHomotopyCategory_map_quotient_commShiftIso_hom_app (n : ℤ) (K : CochainComplex C ℤ) :
    (F.mapHomotopyCategory (.up ℤ)).map
        (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).hom.app K) ≫
        ((F.mapHomotopyCategory (.up ℤ)).commShiftIso n).hom.app _ =
      (HomotopyCategory.quotient D (.up ℤ)).map
          (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app K) ≫
        ((HomotopyCategory.quotient D (.up ℤ)).commShiftIso n).hom.app _ := by
  have h := NatTrans.shift_app_comm (F.mapHomotopyCategoryFactors (.up ℤ)).hom n K
  simpa [Functor.commShiftIso_comp_hom_app, mapHomotopyCategoryFactors_hom_app] using h

/-- **The functor `Kᵇ(C) ⥤ Kᵇ(D)` commutes with shifts compatibly with `K(C) ⥤ K(D)`**: after the
inclusions into the homotopy categories, its commutation with the shift is the one of
`F.mapHomotopyCategory`. -/
@[reassoc]
theorem ι_map_mapHomotopyCategoryBounded_commShiftIso_hom_app (n : ℤ)
    (K : TauCeti.HomotopyCategory.Bounded C) :
    (TauCeti.HomotopyCategory.Bounded.ι D).map
        ((F.mapHomotopyCategoryBounded.commShiftIso n).hom.app K) ≫
        ((TauCeti.HomotopyCategory.Bounded.ι D).commShiftIso n).hom.app _ ≫
        (F.mapHomotopyCategoryBoundedCompι.hom.app K)⟦n⟧' =
      F.mapHomotopyCategoryBoundedCompι.hom.app (K⟦n⟧) ≫
        (F.mapHomotopyCategory (.up ℤ)).map
          (((TauCeti.HomotopyCategory.Bounded.ι C).commShiftIso n).hom.app K) ≫
        ((F.mapHomotopyCategory (.up ℤ)).commShiftIso n).hom.app _ := by
  have h := NatTrans.shift_app_comm F.mapHomotopyCategoryBoundedCompι.hom n K
  simpa [Functor.commShiftIso_comp_hom_app] using h

end Shift

section Mk

/-- The image in `Kᵇ(D)` of the class of a bounded complex `K` is the class of the termwise image
of `K`. -/
noncomputable def mapHomotopyCategoryBoundedMkIso (K : CochainComplex C ℤ)
    (hK : CochainComplex.bounded C K) :
    F.mapHomotopyCategoryBounded.obj (TauCeti.HomotopyCategory.Bounded.mk K hK) ≅
      TauCeti.HomotopyCategory.Bounded.mk _ (F.bounded_mapHomologicalComplex hK) :=
  (TauCeti.HomotopyCategory.Bounded.fullyFaithfulι D).preimageIso
    (F.mapHomotopyCategoryBoundedCompι.app (TauCeti.HomotopyCategory.Bounded.mk K hK))

theorem ι_map_mapHomotopyCategoryBoundedMkIso_hom (K : CochainComplex C ℤ)
    (hK : CochainComplex.bounded C K) :
    (TauCeti.HomotopyCategory.Bounded.ι D).map (F.mapHomotopyCategoryBoundedMkIso K hK).hom =
      F.mapHomotopyCategoryBoundedCompι.hom.app (TauCeti.HomotopyCategory.Bounded.mk K hK) :=
  (TauCeti.HomotopyCategory.Bounded.fullyFaithfulι D).map_preimage _

theorem ι_map_mapHomotopyCategoryBoundedMkIso_inv (K : CochainComplex C ℤ)
    (hK : CochainComplex.bounded C K) :
    (TauCeti.HomotopyCategory.Bounded.ι D).map (F.mapHomotopyCategoryBoundedMkIso K hK).inv =
      F.mapHomotopyCategoryBoundedCompι.inv.app (TauCeti.HomotopyCategory.Bounded.mk K hK) :=
  (TauCeti.HomotopyCategory.Bounded.fullyFaithfulι D).map_preimage _

/-- The comparison `mapHomotopyCategoryBoundedMkIso` is natural in maps of bounded complexes. -/
@[reassoc]
theorem mkMap_comp_mapHomotopyCategoryBoundedMkIso_inv {K L : CochainComplex C ℤ}
    {hK : CochainComplex.bounded C K} {hL : CochainComplex.bounded C L} (φ : K ⟶ L) :
    TauCeti.HomotopyCategory.Bounded.mkMap ((F.mapHomologicalComplex (.up ℤ)).map φ) ≫
        (F.mapHomotopyCategoryBoundedMkIso L hL).inv =
      (F.mapHomotopyCategoryBoundedMkIso K hK).inv ≫
        F.mapHomotopyCategoryBounded.map (TauCeti.HomotopyCategory.Bounded.mkMap φ) := by
  apply (TauCeti.HomotopyCategory.Bounded.ι D).map_injective
  rw [Functor.map_comp, Functor.map_comp, ι_map_mapHomotopyCategoryBoundedMkIso_inv,
    ι_map_mapHomotopyCategoryBoundedMkIso_inv]
  exact F.mapHomotopyCategoryBoundedCompι.inv.naturality
    (TauCeti.HomotopyCategory.Bounded.mkMap φ : TauCeti.HomotopyCategory.Bounded.mk K hK ⟶ _)

/-- The image in `Kᵇ(D)` of the class of a bounded complex `K` under the quotient functor is the
class of the termwise image of `K`. -/
noncomputable def mapHomotopyCategoryBoundedQuotientObjIso (K : CochainComplex.Bounded C) :
    F.mapHomotopyCategoryBounded.obj ((TauCeti.HomotopyCategory.Bounded.quotient C).obj K) ≅
      (TauCeti.HomotopyCategory.Bounded.quotient D).obj
        ⟨_, F.bounded_mapHomologicalComplex K.property⟩ :=
  (TauCeti.HomotopyCategory.Bounded.fullyFaithfulι D).preimageIso
    (F.mapHomotopyCategoryBoundedCompι.app _ ≪≫
      (F.mapHomotopyCategory (.up ℤ)).mapIso
        ((TauCeti.HomotopyCategory.Bounded.quotientCompιIso C).app K) ≪≫
      (F.mapHomotopyCategoryFactors (.up ℤ)).app K.obj ≪≫
      ((TauCeti.HomotopyCategory.Bounded.quotientCompιIso D).app
        ⟨_, F.bounded_mapHomologicalComplex K.property⟩).symm)

end Mk

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

/-- In the homotopy category, the comparison `mapHomotopyCategoryBoundedSingleFunctorIso` is the
comparison `HomologicalComplex.singleMapHomologicalComplex` of single complexes. -/
theorem ι_map_mapHomotopyCategoryBoundedSingleFunctorIso_hom_app (n : ℤ) (X : C) :
    (TauCeti.HomotopyCategory.Bounded.ι D).map
        ((F.mapHomotopyCategoryBoundedSingleFunctorIso n).hom.app X) =
      F.mapHomotopyCategoryBoundedCompι.hom.app _ ≫
        (F.mapHomotopyCategory (.up ℤ)).map
          ((TauCeti.HomotopyCategory.Bounded.singleFunctorCompιIso C n).hom.app X) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.app X) ≫
        (TauCeti.HomotopyCategory.Bounded.singleFunctorCompιIso D n).inv.app (F.obj X) := by
  -- The comparisons `singleFunctorPostcompQuotientIso` are identities by definition.
  have h₁ : (HomotopyCategory.singleFunctorPostcompQuotientIso C n).hom.app X = 𝟙 _ := rfl
  have h₂ : (HomotopyCategory.singleFunctorPostcompQuotientIso D n).inv.app (F.obj X) = 𝟙 _ := rfl
  simp only [comp_obj, ObjectProperty.ι_obj, mapHomotopyCategoryBoundedSingleFunctorIso,
    whiskeringRight_obj_obj, FullyFaithful.preimageIso_hom, Iso.trans_hom, isoWhiskerLeft_hom,
    Iso.symm_hom, isoWhiskerRight_hom, FullyFaithful.whiskeringRight_preimage_app,
    NatTrans.comp_app, associator_hom_app, whiskerLeft_app, associator_inv_app, whiskerRight_app,
    HomotopyCategory.quotient_obj_singleFunctors_obj, h₁, map_id,
    mapHomotopyCategoryFactors_hom_app, h₂, Category.comp_id, Category.id_comp,
    ObjectProperty.ι_map, ObjectProperty.homMk_hom]
  -- The identities sit on objects which agree with the neighbouring ones only up to unfolding.
  erw [Category.id_comp ((TauCeti.HomotopyCategory.Bounded.singleFunctorCompιIso D n).inv.app
      (F.obj X)), Category.id_comp ((HomotopyCategory.quotient D (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.app X) ≫
        (TauCeti.HomotopyCategory.Bounded.singleFunctorCompιIso D n).inv.app (F.obj X))]
  rfl

/-- The image in `Kᵇ(D)` of the class of `X[n]` is the class of `(F X)[n]`. -/
noncomputable def mapHomotopyCategoryBoundedMkSingleIso (n : ℤ) (X : C) :
    F.mapHomotopyCategoryBounded.obj
        (TauCeti.HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single n X)) ≅
      TauCeti.HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single n (F.obj X)) where
  hom := (F.mapHomotopyCategoryBoundedMkIso _ _).hom ≫ TauCeti.HomotopyCategory.Bounded.mkMap
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.app X)
  inv := TauCeti.HomotopyCategory.Bounded.mkMap
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).inv.app X) ≫
    (F.mapHomotopyCategoryBoundedMkIso _ _).inv
  hom_inv_id := by simp [← TauCeti.HomotopyCategory.Bounded.mkMap_comp_assoc]
  inv_hom_id := by simp [← TauCeti.HomotopyCategory.Bounded.mkMap_comp]

/-- The inverse of `mapHomotopyCategoryBoundedMkSingleIso` is the class of the comparison of single
complexes, followed by `mapHomotopyCategoryBoundedMkIso`. -/
theorem mapHomotopyCategoryBoundedMkSingleIso_inv (n : ℤ) (X : C) :
    (F.mapHomotopyCategoryBoundedMkSingleIso n X).inv =
      TauCeti.HomotopyCategory.Bounded.mkMap
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).inv.app X) ≫
        (F.mapHomotopyCategoryBoundedMkIso _ _).inv :=
  (rfl)

/-- **Evaluation of `mapHomotopyCategoryBoundedMkSingleIso` in the homotopy category**: it is the
comparison `HomologicalComplex.singleMapHomologicalComplex` of single complexes. -/
@[reassoc]
theorem ι_map_mapHomotopyCategoryBoundedMkSingleIso_inv_comp (n : ℤ) (X : C) :
    (TauCeti.HomotopyCategory.Bounded.ι D).map (F.mapHomotopyCategoryBoundedMkSingleIso n X).inv ≫
        F.mapHomotopyCategoryBoundedCompι.hom.app _ =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).inv.app X) := by
  rw [mapHomotopyCategoryBoundedMkSingleIso_inv, Functor.map_comp,
    TauCeti.HomotopyCategory.Bounded.ι_map_mkMap, ι_map_mapHomotopyCategoryBoundedMkIso_inv,
    Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- In the homotopy category, `mapHomotopyCategoryBoundedSingleFunctorIso` followed by the
identification `singleFunctorObjIsoMk` of `(F X)[n]` with the class of the single complex is the
comparison `HomologicalComplex.singleMapHomologicalComplex` of single complexes. -/
@[reassoc]
theorem ι_map_mapHomotopyCategoryBoundedSingleFunctorIso_hom_app_comp (n : ℤ) (X : C) :
    (TauCeti.HomotopyCategory.Bounded.ι D).map
        ((F.mapHomotopyCategoryBoundedSingleFunctorIso n).hom.app X) ≫
        (TauCeti.HomotopyCategory.Bounded.ι D).map
          (TauCeti.HomotopyCategory.Bounded.singleFunctorObjIsoMk n (F.obj X)).hom =
      F.mapHomotopyCategoryBoundedCompι.hom.app _ ≫
        (F.mapHomotopyCategory (.up ℤ)).map
          ((TauCeti.HomotopyCategory.Bounded.singleFunctorCompιIso C n).hom.app X) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).hom.app X) := by
  rw [ι_map_mapHomotopyCategoryBoundedSingleFunctorIso_hom_app,
    TauCeti.HomotopyCategory.Bounded.ι_map_singleFunctorObjIsoMk_hom]
  -- `(singleFunctorCompιIso D n).inv.app (F.obj X)` ends at `ι.obj ((singleFunctor D n).obj _)`,
  -- which is `ι.obj ((F ⋙ singleFunctor D n).obj X)` only after unfolding `Functor.comp`, so
  -- reassociating and cancelling it are matched up to this unfolding.
  erw [Category.assoc (obj := HomotopyCategory D (.up ℤ)),
    Category.assoc (obj := HomotopyCategory D (.up ℤ)),
    Category.assoc (obj := HomotopyCategory D (.up ℤ)),
    Iso.inv_hom_id_app (TauCeti.HomotopyCategory.Bounded.singleFunctorCompιIso D n) (F.obj X),
    Category.comp_id]

/-- The comparison `mapHomotopyCategoryBoundedSingleFunctorIso` agrees with
`mapHomotopyCategoryBoundedMkSingleIso` through the classes `singleFunctorObjIsoMk` of single
complexes. -/
@[reassoc]
theorem mapHomotopyCategoryBoundedSingleFunctorIso_hom_app_comp (n : ℤ) (X : C) :
    (F.mapHomotopyCategoryBoundedSingleFunctorIso n).hom.app X ≫
        (TauCeti.HomotopyCategory.Bounded.singleFunctorObjIsoMk n (F.obj X)).hom ≫
        (F.mapHomotopyCategoryBoundedMkSingleIso n X).inv =
      F.mapHomotopyCategoryBounded.map
        (TauCeti.HomotopyCategory.Bounded.singleFunctorObjIsoMk n X).hom := by
  apply (TauCeti.HomotopyCategory.Bounded.ι D).map_injective
  rw [← cancel_mono (F.mapHomotopyCategoryBoundedCompι.hom.app _)]
  have h := F.mapHomotopyCategoryBoundedCompι.hom.naturality
    (TauCeti.HomotopyCategory.Bounded.singleFunctorObjIsoMk n X).hom
  simp only [Functor.comp_map,
    TauCeti.HomotopyCategory.Bounded.ι_map_singleFunctorObjIsoMk_hom] at h
  rw [h, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    ι_map_mapHomotopyCategoryBoundedMkSingleIso_inv_comp,
    ι_map_mapHomotopyCategoryBoundedSingleFunctorIso_hom_app_comp_assoc]
  -- The image of `singleMapHomologicalComplex` sits on `(HomotopyCategory.singleFunctor C n).obj`
  -- `X`, the class of a single complex only after unfolding `HomotopyCategory.singleFunctors`.
  erw [← Functor.map_comp (HomotopyCategory.quotient D (.up ℤ)),
    Iso.hom_inv_id_app (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n) X,
    Functor.map_id, Category.comp_id]
  rfl

/-- The shift of `mapHomotopyCategoryBoundedMkSingleIso` after `mkSingleIsoShift`, evaluated in
the homotopy category. -/
private theorem ι_map_mkSingleIsoShift_hom_comp_shift_mapHomotopyCategoryBoundedMkSingleIso_inv
    (n a a' : ℤ) (h : n + a = a') (X : C) :
    (TauCeti.HomotopyCategory.Bounded.ι D).map
        ((TauCeti.HomotopyCategory.Bounded.mkSingleIsoShift n a a' h (F.obj X)).hom ≫
          (F.mapHomotopyCategoryBoundedMkSingleIso a' X).inv⟦n⟧') ≫
        ((TauCeti.HomotopyCategory.Bounded.ι D).commShiftIso n).hom.app _ ≫
        (F.mapHomotopyCategoryBoundedCompι.hom.app _)⟦n⟧' =
      (HomotopyCategory.quotient D (.up ℤ)).map
          (((CochainComplex.singleFunctors D).shiftIso n a a' h).inv.app (F.obj X) ≫
            ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) a').inv.app X)⟦n⟧') ≫
        ((HomotopyCategory.quotient D (.up ℤ)).commShiftIso n).hom.app _ := by
  rw [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality_assoc,
    ← Functor.map_comp, ι_map_mapHomotopyCategoryBoundedMkSingleIso_inv_comp,
    TauCeti.HomotopyCategory.Bounded.ι_map_mkSingleIsoShift_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.commShiftIso_hom_naturality,
    Functor.map_comp, Iso.app_inv]

/-- `mapHomotopyCategoryBoundedMkSingleIso` followed by the image of `mkSingleIsoShift`, evaluated
in the homotopy category. -/
private theorem ι_map_mapHomotopyCategoryBoundedMkSingleIso_inv_comp_map_mkSingleIsoShift_hom
    (n a a' : ℤ) (h : n + a = a') (X : C) :
    (TauCeti.HomotopyCategory.Bounded.ι D).map ((F.mapHomotopyCategoryBoundedMkSingleIso a X).inv ≫
        F.mapHomotopyCategoryBounded.map
          (TauCeti.HomotopyCategory.Bounded.mkSingleIsoShift n a a' h X).hom ≫
        (F.mapHomotopyCategoryBounded.commShiftIso n).hom.app _) ≫
        ((TauCeti.HomotopyCategory.Bounded.ι D).commShiftIso n).hom.app _ ≫
        (F.mapHomotopyCategoryBoundedCompι.hom.app _)⟦n⟧' =
      (HomotopyCategory.quotient D (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) a).inv.app X ≫
            (F.mapHomologicalComplex (.up ℤ)).map
              (((CochainComplex.singleFunctors C).shiftIso n a a' h).inv.app X) ≫
            ((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app _) ≫
        ((HomotopyCategory.quotient D (.up ℤ)).commShiftIso n).hom.app _ := by
  have hφ := F.mapHomotopyCategoryBoundedCompι.hom.naturality
    (TauCeti.HomotopyCategory.Bounded.mkSingleIsoShift n a a' h X).hom
  simp only [Functor.comp_map, TauCeti.HomotopyCategory.Bounded.ι_map_mkSingleIsoShift_hom] at hφ
  simp only [Functor.map_comp, Category.assoc,
    ι_map_mapHomotopyCategoryBounded_commShiftIso_hom_app, reassoc_of% hφ,
    ι_map_mapHomotopyCategoryBoundedMkSingleIso_inv_comp_assoc, Functor.mapHomotopyCategory_map,
    Iso.app_inv]
  rw [← Functor.map_comp_assoc (F.mapHomotopyCategory (.up ℤ))
      (((TauCeti.HomotopyCategory.Bounded.ι C).commShiftIso n).inv.app _),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  -- `ι.obj (mk K _)` is `quotient.obj K` by definition of `mk`.
  erw [mapHomotopyCategory_map_quotient_commShiftIso_hom_app]

/-- **`mapHomotopyCategoryBoundedMkSingleIso` commutes with shifts**: for `n + a = a'`, it is
compatible with the identifications `mkSingleIsoShift` of the class of `X[a]` with the shift by
`n` of the class of `X[a']`. -/
@[reassoc]
theorem mkSingleIsoShift_hom_comp_shift_mapHomotopyCategoryBoundedMkSingleIso_inv
    (n a a' : ℤ) (h : n + a = a') (X : C) :
    (TauCeti.HomotopyCategory.Bounded.mkSingleIsoShift n a a' h (F.obj X)).hom ≫
        (F.mapHomotopyCategoryBoundedMkSingleIso a' X).inv⟦n⟧' =
      (F.mapHomotopyCategoryBoundedMkSingleIso a X).inv ≫
        F.mapHomotopyCategoryBounded.map
          (TauCeti.HomotopyCategory.Bounded.mkSingleIsoShift n a a' h X).hom ≫
        (F.mapHomotopyCategoryBounded.commShiftIso n).hom.app _ := by
  apply (TauCeti.HomotopyCategory.Bounded.ι D).map_injective
  rw [← cancel_mono (((TauCeti.HomotopyCategory.Bounded.ι D).commShiftIso n).hom.app _ ≫
    (F.mapHomotopyCategoryBoundedCompι.hom.app _)⟦n⟧'),
    ι_map_mkSingleIsoShift_hom_comp_shift_mapHomotopyCategoryBoundedMkSingleIso_inv,
    ι_map_mapHomotopyCategoryBoundedMkSingleIso_inv_comp_map_mkSingleIsoShift_hom,
    CochainComplex.singleMapHomologicalComplex_inv_app_comp_shiftIso]
  -- The two sides differ only in how the object `F (X[a'])` is written.
  rfl

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
