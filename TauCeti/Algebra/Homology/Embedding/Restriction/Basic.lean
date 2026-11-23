/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Single

/-!
# Mapping restricted homological complexes

This file provides the comparison between first restricting a homological complex along an
embedding of complex shapes and then mapping it, and first mapping the complex and then
restricting it. This transports mapped or forgotten complexes through shape reindexing, allowing
results about a restricted complex to be compared with the corresponding restriction of the
mapped complex.

It also restricts single complexes: an object placed in a degree `e.f i` of the image of the
embedding restricts to the same object placed in degree `i`.

## Main results

* `ComplexShape.Embedding.mapRestrictionIso`: mapping homological complexes commutes with
  restriction along a shape embedding.
* `HomologicalComplex.restrictionSingleIso`: the restriction of the single complex `X[i']` along
  an embedding `e` with `e.f i = i'` is the single complex `X[i]`. This is the restriction
  counterpart of Mathlib's `HomologicalComplex.extendSingleIso`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace ComplexShape.Embedding

/-- Mapping homological complexes commutes with restriction along a shape embedding. The two
composites have definitionally equal objects, so each component is an identity morphism. -/
noncomputable def mapRestrictionIso
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms] [e.IsRelIff]
    (K : HomologicalComplex C c') :
    (F.mapHomologicalComplex c).obj ((e.restrictionFunctor C).obj K) ≅
      (e.restrictionFunctor D).obj ((F.mapHomologicalComplex c').obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    -- Both differentials unfold to `F.map (K.d (e.f i) (e.f j))`; Mathlib has no lemma for this.
    change 𝟙 _ ≫ F.map (K.d (e.f i) (e.f j)) = F.map (K.d (e.f i) (e.f j)) ≫ 𝟙 _
    simp)

/-- The forward component of `mapRestrictionIso` is the identity. -/
@[simp]
theorem mapRestrictionIso_hom_f
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms] [e.IsRelIff]
    (K : HomologicalComplex C c') (i : ι) :
    (e.mapRestrictionIso F K).hom.f i = 𝟙 (F.obj (K.X (e.f i))) := by
  rw [mapRestrictionIso]
  rfl

/-- The inverse component of `mapRestrictionIso` is the identity. -/
@[simp]
theorem mapRestrictionIso_inv_f
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms] [e.IsRelIff]
    (K : HomologicalComplex C c') (i : ι) :
    (e.mapRestrictionIso F K).inv.f i = 𝟙 (F.obj (K.X (e.f i))) := by
  rw [mapRestrictionIso]
  rfl

end ComplexShape.Embedding

namespace HomologicalComplex

section Single

variable {C ι ι' : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {c : ComplexShape ι} {c' : ComplexShape ι'} [DecidableEq ι] [DecidableEq ι']
  (e : c.Embedding c') [e.IsRelIff]
  (X : C) (i : ι) (i' : ι') (h : e.f i = i')

/-- The restriction of the single complex `X[i']` along an embedding `e` with `e.f i = i'` is the
single complex `X[i]`: since `e.f` is injective, both complexes have `X` in degree `i`, zero
objects elsewhere and zero differentials. -/
noncomputable def restrictionSingleIso :
    ((single C c' i').obj X).restriction e ≅ (single C c i).obj X :=
  Hom.isoOfComponents
    (fun k ↦ if hk : k = i then
        singleObjXIsoOfEq c' i' X (e.f k) (by rw [hk, h]) ≪≫ (singleObjXIsoOfEq c i X k hk).symm
      else (isZero_single_obj_X c' i' X (e.f k)
          (fun hk' ↦ hk (e.injective_f (hk'.trans h.symm)))).iso
        (isZero_single_obj_X c i X k hk))
    (fun _ _ _ ↦ by simp)

/-- In degree `i`, `HomologicalComplex.restrictionSingleIso` is the identification of both terms
with `X`. -/
@[simp]
lemma restrictionSingleIso_hom_f :
    (restrictionSingleIso e X i i' h).hom.f i =
      (singleObjXIsoOfEq c' i' X (e.f i) h).hom ≫ (singleObjXSelf c i X).inv := by
  rw [restrictionSingleIso, Hom.isoOfComponents_hom_f, dite_eq_left rfl, Iso.trans_hom,
    Iso.symm_hom, singleObjXSelf]

/-- In degree `i`, the inverse of `HomologicalComplex.restrictionSingleIso` is the identification
of both terms with `X`. -/
@[simp]
lemma restrictionSingleIso_inv_f :
    (restrictionSingleIso e X i i' h).inv.f i =
      (singleObjXSelf c i X).hom ≫ (singleObjXIsoOfEq c' i' X (e.f i) h).inv := by
  rw [restrictionSingleIso, Hom.isoOfComponents_inv_f, dite_eq_left rfl, Iso.trans_inv,
    Iso.symm_inv, singleObjXSelf]

end Single

end HomologicalComplex
