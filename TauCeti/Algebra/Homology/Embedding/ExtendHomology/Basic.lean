/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Opcycles and extension by zero

The opcycles isomorphism of an extended complex is natural in chain maps and compatible with
`HomologicalComplex.opcyclesToCycles`. These identities require homology only in the degrees
involved, in a category with zero morphisms and a zero object. An extended chain map is an
epimorphism in homology in a degree of the image exactly when the original map is, the counterpart
for epimorphisms of Mathlib's `HomologicalComplex.quasiIsoAt_extendMap_iff`. Outside the image,
an extended complex has zero homology, so every extended chain map is an isomorphism in homology
there. In a degree of the image, taking homology commutes with extension, naturally, both for
complexes (`ComplexShape.Embedding.extendFunctorCompHomologyFunctorIso`) and on homotopy
categories (`ComplexShape.Embedding.extendHomotopyFunctorCompHomologyFunctorIso`).

Adapted from [TauCetiProject/TauCeti#10141](https://github.com/TauCetiProject/TauCeti/pull/10141).
-/

public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K L : HomologicalComplex C c} (φ : K ⟶ L) (e : c.Embedding c')

/-- The identification of the opcycles of an extended complex is natural. -/
@[reassoc (attr := simp)]
lemma extendOpcyclesIso_hom_naturality {j : ι} {j' : ι'} (hj' : e.f j = j')
    [K.HasHomology j] [L.HasHomology j] [(K.extend e).HasHomology j']
    [(L.extend e).HasHomology j'] :
    opcyclesMap (extendMap φ e) j' ≫ (L.extendOpcyclesIso e hj').hom =
      (K.extendOpcyclesIso e hj').hom ≫ opcyclesMap φ j := by
  simp [← cancel_epi ((K.extend e).pOpcycles j'), extendMap_f φ e hj']

variable (K) in
/-- The identifications of the opcycles and cycles of an extended complex are compatible with the
maps `opcyclesToCycles`. -/
-- The left-hand side does not determine the source index `i` for the simplifier.
@[reassoc]
lemma opcyclesToCycles_extendCyclesIso_hom {i j : ι} {i' j' : ι'} (hi' : e.f i = i')
    (hj' : e.f j = j') [K.HasHomology i] [K.HasHomology j] [(K.extend e).HasHomology i']
    [(K.extend e).HasHomology j'] :
    (K.extend e).opcyclesToCycles i' j' ≫ (K.extendCyclesIso e hj').hom =
      (K.extendOpcyclesIso e hi').hom ≫ K.opcyclesToCycles i j := by
  simp [← cancel_epi ((K.extend e).pOpcycles i'), ← cancel_mono (K.iCycles j),
    K.extend_d_eq e hi' hj']

variable {e} in
/-- In a degree `j'` in the image of `e`, the map induced in homology by the extension of `φ` is an
epimorphism exactly when the map induced by `φ` is in the corresponding degree `j`. -/
lemma epi_homologyMap_extendMap_iff {j : ι} {j' : ι'} (hj' : e.f j = j')
    [K.HasHomology j] [L.HasHomology j] [(K.extend e).HasHomology j']
    [(L.extend e).HasHomology j'] :
    Epi (homologyMap (extendMap φ e) j') ↔ Epi (homologyMap φ j) :=
  (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.extendHomologyIso e hj') (L.extendHomologyIso e hj'))

variable {e} in
/-- In a degree `j'` outside the image of `e`, the map induced in homology by the extension of `φ`
is an isomorphism, between zero objects. -/
lemma isIso_homologyMap_extendMap_of_forall_ne {j' : ι'} (hj' : ∀ j, e.f j ≠ j')
    [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j'] :
    IsIso (homologyMap (extendMap φ e) j') :=
  ⟨0, (K.extend_exactAt e j' hj').isZero_homology.eq_of_src _ _,
    (L.extend_exactAt e j' hj').isZero_homology.eq_of_src _ _⟩

end HomologicalComplex

namespace ComplexShape.Embedding

open HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  (C : Type*) [Category* C]

section

variable [HasZeroMorphisms C] [HasZeroObject C] [CategoryWithHomology C]

/-- In a degree `j'` of the image of `e`, the homology of the extension of a complex along `e` is
naturally the homology of the complex in the corresponding degree `j`. -/
noncomputable def extendFunctorCompHomologyFunctorIso {j : ι} {j' : ι'} (hj' : e.f j = j') :
    e.extendFunctor C ⋙ homologyFunctor C c' j' ≅ homologyFunctor C c j :=
  NatIso.ofComponents (fun K ↦ K.extendHomologyIso e hj')
    (fun φ ↦ extendHomologyIso_hom_naturality φ e hj')

@[simp]
lemma extendFunctorCompHomologyFunctorIso_hom_app {j : ι} {j' : ι'} (hj' : e.f j = j')
    (K : HomologicalComplex C c) :
    (e.extendFunctorCompHomologyFunctorIso C hj').hom.app K = (K.extendHomologyIso e hj').hom :=
  (rfl)

end

variable [Preadditive C] [HasZeroObject C] [CategoryWithHomology C] [e.IsRelIff]

/-- In a degree `j'` of the image of `e`, the homology of the extension along `e` is naturally the
homology in the corresponding degree `j`, on homotopy categories. -/
noncomputable def extendHomotopyFunctorCompHomologyFunctorIso {j : ι} {j' : ι'}
    (hj' : e.f j = j') :
    e.extendHomotopyFunctor C ⋙ HomotopyCategory.homologyFunctor C c' j' ≅
      HomotopyCategory.homologyFunctor C c j :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerLeft (e.extendFunctor C) (HomotopyCategory.homologyFunctorFactors C c' j') ≪≫
      e.extendFunctorCompHomologyFunctorIso C hj' ≪≫
      (HomotopyCategory.homologyFunctorFactors C c j).symm)

lemma extendHomotopyFunctorCompHomologyFunctorIso_hom_app_quotient_obj {j : ι} {j' : ι'}
    (hj' : e.f j = j') (K : HomologicalComplex C c) :
    (e.extendHomotopyFunctorCompHomologyFunctorIso C hj').hom.app
        ((HomotopyCategory.quotient C c).obj K) =
      (HomotopyCategory.homologyFunctorFactors C c' j').hom.app (K.extend e) ≫
        (K.extendHomologyIso e hj').hom ≫
        (HomotopyCategory.homologyFunctorFactors C c j).inv.app K := by
  (rfl)

end ComplexShape.Embedding
