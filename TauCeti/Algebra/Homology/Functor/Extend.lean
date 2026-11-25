/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Functors applied to complexes extended by zero

Let `e : c.Embedding c'` be an embedding of complex shapes and `F : C ⥤ D` a functor preserving
zero morphisms between categories with zero objects. Applying `F` termwise to the extension
`K.extend e` of a complex `K` gives the extension of `F(K)`: in the degrees of the image of `e`
both complexes have the terms of `F(K)`, and in the other degrees both are zero. This is
`CategoryTheory.Functor.mapHomologicalComplexExtendIso`, a natural isomorphism
`e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅ F.mapHomologicalComplex c ⋙ e.extendFunctor D`.
For an additive functor it descends to homotopy categories
(`CategoryTheory.Functor.mapHomotopyCategoryExtendIso`).

For instance, an injective resolution indexed by `ℕ` becomes a complex indexed by `ℤ` by
extension along `ComplexShape.embeddingUpNat`, and these isomorphisms say that applying a functor
commutes with this reindexing.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C D : Type*} [Category* C] [Category* D]

section ZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroObject C] [HasZeroMorphisms D] [HasZeroObject D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c')

open Classical in
/-- The isomorphism between the terms of `F(K.extend e)` and of `F(K).extend e`: in a degree
`e.f i` both are `F(K.X i)`, and in the other degrees both are zero. -/
def mapHomologicalComplexExtendXIso (K : HomologicalComplex C c) (i' : ι') :
    F.obj ((K.extend e).X i') ≅ (((F.mapHomologicalComplex c).obj K).extend e).X i' :=
  if h : ∃ i, e.f i = i' then
    F.mapIso (K.extendXIso e h.choose_spec) ≪≫
      (((F.mapHomologicalComplex c).obj K).extendXIso e h.choose_spec).symm
  else
    (F.map_isZero (K.isZero_extend_X e i' (by simpa using h))).iso
      (((F.mapHomologicalComplex c).obj K).isZero_extend_X e i' (by simpa using h))

lemma mapHomologicalComplexExtendXIso_hom {K : HomologicalComplex C c} {i : ι} {i' : ι'}
    (h : e.f i = i') :
    (F.mapHomologicalComplexExtendXIso e K i').hom =
      F.map (K.extendXIso e h).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv := by
  have h' : ∃ i, e.f i = i' := ⟨i, h⟩
  obtain rfl : h'.choose = i := e.injective_f (h'.choose_spec.trans h.symm)
  simp [mapHomologicalComplexExtendXIso, h']

/-- Applying `F` to the extension of a complex gives the extension of `F` applied to it. -/
def mapHomologicalComplexExtendObjIso (K : HomologicalComplex C c) :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅ ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (F.mapHomologicalComplexExtendXIso e K) (by
    intro i' j' _
    by_cases hj : ∃ j, e.f j = j'
    · by_cases hi : ∃ i, e.f i = i'
      · obtain ⟨i, rfl⟩ := hi
        obtain ⟨j, rfl⟩ := hj
        rw [mapHomologicalComplexExtendXIso_hom F e rfl,
          mapHomologicalComplexExtendXIso_hom F e rfl, Functor.mapHomologicalComplex_obj_d,
          HomologicalComplex.extend_d_eq _ e rfl rfl, HomologicalComplex.extend_d_eq _ e rfl rfl]
        simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_map_assoc,
          Functor.mapHomologicalComplex_obj_d]
      · exact (F.map_isZero (K.isZero_extend_X e i' (by simpa using hi))).eq_of_src _ _
    · exact (((F.mapHomologicalComplex c).obj K).isZero_extend_X e j'
        (by simpa using hj)).eq_of_tgt _ _)

@[simp]
lemma mapHomologicalComplexExtendObjIso_hom_f (K : HomologicalComplex C c) (i' : ι') :
    (F.mapHomologicalComplexExtendObjIso e K).hom.f i' =
      (F.mapHomologicalComplexExtendXIso e K i').hom :=
  (rfl)

/-- The isomorphisms `F(K.extend e) ≅ F(K).extend e` are natural in `K`. -/
@[reassoc]
lemma mapHomologicalComplexExtendObjIso_hom_naturality {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) ≫
        (F.mapHomologicalComplexExtendObjIso e L).hom =
      (F.mapHomologicalComplexExtendObjIso e K).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext i'
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      mapHomologicalComplexExtendObjIso_hom_f, mapHomologicalComplexExtendObjIso_hom_f,
      mapHomologicalComplexExtendXIso_hom F e rfl, mapHomologicalComplexExtendXIso_hom F e rfl,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.extendMap_f _ e rfl,
      HomologicalComplex.extendMap_f _ e rfl]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_map_assoc,
      Functor.mapHomologicalComplex_map_f]
  · exact (F.map_isZero (K.isZero_extend_X e i' (by simpa using hi))).eq_of_src _ _

/-- Applying `F` to extensions of complexes gives the extensions of `F` applied to them,
naturally. -/
def mapHomologicalComplexExtendIso :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor D :=
  NatIso.ofComponents (F.mapHomologicalComplexExtendObjIso e)
    (F.mapHomologicalComplexExtendObjIso_hom_naturality e)

@[simp]
lemma mapHomologicalComplexExtendIso_hom_app (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexExtendIso e).hom.app K =
      (F.mapHomologicalComplexExtendObjIso e K).hom :=
  (rfl)

end ZeroMorphisms

variable [Preadditive C] [HasZeroObject C] [Preadditive D] [HasZeroObject D] (F : C ⥤ D)
  [F.Additive] (e : c.Embedding c') [e.IsRelIff]

/-- Applying an additive functor `F` commutes with extension along `e` on homotopy
categories. -/
def mapHomotopyCategoryExtendIso :
    e.extendHomotopyFunctor C ⋙ F.mapHomotopyCategory c' ≅
      F.mapHomotopyCategory c ⋙ e.extendHomotopyFunctor D :=
  Quotient.natIsoLift _
    (isoWhiskerRight (F.mapHomologicalComplexExtendIso e) (HomotopyCategory.quotient D c'))

@[simp]
lemma mapHomotopyCategoryExtendIso_hom_app_quotient_obj (K : HomologicalComplex C c) :
    (F.mapHomotopyCategoryExtendIso e).hom.app ((HomotopyCategory.quotient C c).obj K) =
      (HomotopyCategory.quotient D c').map (F.mapHomologicalComplexExtendObjIso e K).hom :=
  (rfl)

end CategoryTheory.Functor
