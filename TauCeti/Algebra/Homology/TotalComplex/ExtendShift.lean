/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.TotalComplexShift
public import TauCeti.Algebra.Homology.Functor.Extend

/-!
# Total complexes of extended bicomplexes commute with the second shift

Let `K` be a bicomplex whose rows are integer-graded cochain complexes, with its first grading of
some shape `c`, and let `e : c.Embedding (ComplexShape.up ℤ)` be an embedding of complex shapes,
for instance `ComplexShape.embeddingUpNat` for a first grading indexed by `ℕ`. Shifting every row
of `K` by `y` and then extending the first grading along `e` gives the bicomplex
`HomologicalComplex₂.shiftFunctor₂ y` applied to `K.extend e`
(`CategoryTheory.Functor.mapHomologicalComplexExtendObjIso`), so Mathlib's
`HomologicalComplex₂.totalShift₂Iso` identifies its total complex with the shift by `y` of the
total complex of `K.extend e`. On the summand in first degree `p` this isomorphism is the
multiplication by `(-1)^(p y)` (`HomologicalComplex₂.ι_totalExtendShift₂Iso_hom_f`).

## Main definitions

* `HomologicalComplex₂.totalExtendShift₂Iso`: the isomorphism
  `Tot((K[y]).extend e) ≅ (Tot(K.extend e))[y]`.

## Main results

* `HomologicalComplex₂.ι_totalExtendShift₂Iso_hom_f`: the isomorphism on summands.
* `HomologicalComplex₂.totalExtendShift₂Iso_hom_naturality`: naturality in the bicomplex.

## References

* The signs are those of Joël Riou's Mathlib construction `HomologicalComplex₂.totalShift₂Iso`
  (`Mathlib.Algebra.Homology.TotalComplexShift`).
-/

public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  {ι : Type*} {c : ComplexShape ι} (e : c.Embedding (ComplexShape.up ℤ))
  (K L : HomologicalComplex (CochainComplex C ℤ) c) (y : ℤ)

instance [HasTotal (K.extend e) (ComplexShape.up ℤ)] :
    HasTotal ((((shiftFunctor (CochainComplex C ℤ) y).mapHomologicalComplex c).obj K).extend e)
      (ComplexShape.up ℤ) :=
  hasTotal_of_iso ((shiftFunctor _ y).mapHomologicalComplexExtendObjIso e K) _

variable [HasTotal (K.extend e) (ComplexShape.up ℤ)]

/-- **Totalization of an extended bicomplex commutes with the second shift.** Shifting the rows
of `K` by `y` and extending along `e`, the total complex is the shift by `y` of the total complex
of `K.extend e`. The shift is moved through the extension
(`CategoryTheory.Functor.mapHomologicalComplexExtendObjIso`) and then out of the total complex by
Mathlib's `HomologicalComplex₂.totalShift₂Iso`, which multiplies the summand in first degree `p` by
`(-1)^(p y)` (`HomologicalComplex₂.ι_totalExtendShift₂Iso_hom_f`). -/
def totalExtendShift₂Iso :
    total ((((shiftFunctor (CochainComplex C ℤ) y).mapHomologicalComplex c).obj K).extend e)
        (ComplexShape.up ℤ) ≅
      (total (K.extend e) (ComplexShape.up ℤ))⟦y⟧ :=
  total.mapIso ((shiftFunctor _ y).mapHomologicalComplexExtendObjIso e K).symm _ ≪≫
    totalShift₂Iso _ y

/-- `totalExtendShift₂Iso` is the total map of the inverse of
`CategoryTheory.Functor.mapHomologicalComplexExtendObjIso`, followed by
`HomologicalComplex₂.totalShift₂Iso`. -/
lemma totalExtendShift₂Iso_hom :
    (totalExtendShift₂Iso e K y).hom =
      total.map ((shiftFunctor _ y).mapHomologicalComplexExtendObjIso e K).inv _ ≫
        (totalShift₂Iso (K.extend e) y).hom :=
  (rfl)

/-- On the summand in degrees `(p, q)`, `totalExtendShift₂Iso` is the identification of the terms
of the extensions, multiplied by the sign `(-1)^(p y)`, followed by the inclusion of the summand
in degrees `(p, q')` of the total complex of `K.extend e`, where `q' = q + y`. -/
@[reassoc]
lemma ι_totalExtendShift₂Iso_hom_f (p q n : ℤ) (h : p + q = n) (q' : ℤ) (hq' : q' = q + y)
    (n' : ℤ) (hn' : n' = n + y) :
    ιTotal _ (ComplexShape.up ℤ) p q n h ≫ (totalExtendShift₂Iso e K y).hom.f n =
      (p * y).negOnePow •
        ((((shiftFunctor _ y).mapHomologicalComplexExtendObjIso e K).inv.f p).f q ≫
          (shiftFunctor₂XXIso (K.extend e) p q y q' hq').hom ≫
            ιTotal _ (ComplexShape.up ℤ) p q' n' (by dsimp; lia) ≫
              (CochainComplex.shiftFunctorObjXIso _ y n n' hn').inv) := by
  rw [totalExtendShift₂Iso_hom, HomologicalComplex.comp_f, ιTotal_map_assoc,
    ι_totalShift₂Iso_hom_f _ y p q n h q' hq' n' hn', Linear.comp_units_smul]

variable {K L} [HasTotal (L.extend e) (ComplexShape.up ℤ)]

/-- `totalExtendShift₂Iso` is natural in the bicomplex. -/
@[reassoc]
lemma totalExtendShift₂Iso_hom_naturality (g : K ⟶ L) :
    total.map (HomologicalComplex.extendMap
        (((shiftFunctor (CochainComplex C ℤ) y).mapHomologicalComplex c).map g) e) _ ≫
        (totalExtendShift₂Iso e L y).hom =
      (totalExtendShift₂Iso e K y).hom ≫
        (total.map (HomologicalComplex.extendMap g e) (ComplexShape.up ℤ))⟦y⟧' := by
  have h : HomologicalComplex.extendMap
        (((shiftFunctor (CochainComplex C ℤ) y).mapHomologicalComplex c).map g) e ≫
        ((shiftFunctor _ y).mapHomologicalComplexExtendObjIso e L).inv =
      ((shiftFunctor _ y).mapHomologicalComplexExtendObjIso e K).inv ≫
        (shiftFunctor₂ C y).map (HomologicalComplex.extendMap g e) := by
    rw [Iso.comp_inv_eq, Category.assoc,
      Functor.mapHomologicalComplexExtendObjIso_hom_naturality, Iso.inv_hom_id_assoc]
  rw [totalExtendShift₂Iso_hom, totalExtendShift₂Iso_hom, ← total.map_comp_assoc, h,
    total.map_comp, Category.assoc, totalShift₂Iso_hom_naturality, Category.assoc]

end HomologicalComplex₂
