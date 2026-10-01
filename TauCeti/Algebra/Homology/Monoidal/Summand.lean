/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# The monoidal structure of cochain complexes of modules on homogeneous summands

Mathlib's `HomologicalComplex.monoidalCategory` totalizes the degreewise tensor product, so every
structural map of `CochainComplex (ModuleCat R) ℤ` is assembled from maps on the homogeneous
summands `X.X p ⊗ Y.X q` of `X ⊗ Y`.  Mathlib states the component formulas for the auxiliary
constructions the monoidal structure is built from — `HomologicalComplex.mapBifunctorMap`,
`HomologicalComplex.leftUnitor'`, `HomologicalComplex.rightUnitor'` and
`HomologicalComplex.mapBifunctorAssociatorX` — but not for the whiskerings, `λ_`, `ρ_` and `α_`
themselves.  This file supplies that last step, so that a calculation on homogeneous summands
never has to unfold the monoidal structure.  The formula for `⊗ₘ` holds verbatim for homological
complexes of any shape in any monoidal preadditive category, and is stated in that generality.

## Main results

* `HomologicalComplex.ι_tensorHom`: the tensor product of two morphisms on a homogeneous summand,
  for homological complexes in any monoidal preadditive category and of any shape.
* `HomologicalComplex.tensorHom_eq_mapBifunctorMap`: `⊗ₘ` of homological complexes is the
  totalization `HomologicalComplex.mapBifunctorMap` of the two morphisms.
* `HomologicalComplex.ι_whiskerLeft` and `HomologicalComplex.ι_whiskerRight`: the two whiskerings
  on a homogeneous summand.
* `HomologicalComplex.leftUnitor_inv_f` and `HomologicalComplex.rightUnitor_inv_f`: the degreewise
  components of the inverse unitors.
* `HomologicalComplex.ι_ι_associator_hom` and `TauCeti.ι_ι_associator_inv`: the associator
  and its inverse on the summand `X.X p ⊗ Y.X q ⊗ Z.X r`, with arbitrary intermediate degrees.

The analogous formula for the differential of a tensor product is
`HomologicalComplex.ι_tensorObj_d` in `TauCeti/Algebra/Homology/Monoidal/TensorDifferential.lean`.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe v

namespace HomologicalComplex

section General

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]

/-- The tensor product of two morphisms of homological complexes, restricted to a homogeneous
summand, is the tensor product of their components.  Mathlib states this only for
`HomologicalComplex.mapBifunctorMap`, by which `⊗ₘ` is defined. -/
@[reassoc]
lemma ι_tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    [HasTensor K₁ K₂] [HasTensor L₁ L₂]
    (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    ιTensorObj K₁ K₂ i₁ i₂ j h ≫ (tensorHom f₁ f₂).f j =
      (f₁.f i₁ ⊗ₘ f₂.f i₂) ≫ ιTensorObj L₁ L₂ i₁ i₂ j h := by
  refine (ι_mapBifunctorMap _ _ _ _ _ _ _ _).trans ?_
  simp [tensorHom_def]

variable [HasZeroObject C] (c) [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- In the monoidal category of homological complexes, `⊗ₘ` is the totalization of the two
morphisms.  Mathlib defines `HomologicalComplex.monoidalCategory` this way, but states no lemma
exposing it, so `HomologicalComplex.ι_tensorHom` does not apply to `⊗ₘ` without this rewrite. -/
lemma tensorHom_eq_mapBifunctorMap {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₁ : K₁ ⟶ L₁)
    (f₂ : K₂ ⟶ L₂) :
    f₁ ⊗ₘ f₂ = mapBifunctorMap f₁ f₂ (curriedTensor C) c :=
  rfl

end General

variable {R : Type v} [CommRing R]

/-- Left whiskering in `CochainComplex (ModuleCat R) ℤ` is the totalization of the identity and
the given morphism.  Mathlib defines the monoidal structure on homological complexes through
`HomologicalComplex.mapBifunctorMap`, but states no component lemma for `◁`. -/
lemma whiskerLeft_eq_mapBifunctorMap (X : CochainComplex (ModuleCat.{v} R) ℤ)
    {Y Z : CochainComplex (ModuleCat.{v} R) ℤ} (g : Y ⟶ Z) :
    X ◁ g = mapBifunctorMap (𝟙 X) g (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) :=
  rfl

/-- Right whiskering in `CochainComplex (ModuleCat R) ℤ` is the totalization of the given
morphism and the identity; the counterpart of
`HomologicalComplex.whiskerLeft_eq_mapBifunctorMap`. -/
lemma whiskerRight_eq_mapBifunctorMap {X Y : CochainComplex (ModuleCat.{v} R) ℤ} (f : X ⟶ Y)
    (Z : CochainComplex (ModuleCat.{v} R) ℤ) :
    f ▷ Z = mapBifunctorMap f (𝟙 Z) (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) :=
  rfl

/-- Left whiskering of cochain complexes of modules, restricted to a homogeneous summand, is left
whiskering of the summand. -/
@[reassoc (attr := simp)]
lemma ι_whiskerLeft (X : CochainComplex (ModuleCat.{v} R) ℤ)
    {Y Z : CochainComplex (ModuleCat.{v} R) ℤ} (g : Y ⟶ Z) (p q j : ℤ) (h : p + q = j) :
    ιTensorObj X Y p q j h ≫ (X ◁ g).f j = (X.X p ◁ g.f q) ≫ ιTensorObj X Z p q j h := by
  rw [whiskerLeft_eq_mapBifunctorMap, ι_tensorHom, id_f, id_tensorHom]

/-- Right whiskering of cochain complexes of modules, restricted to a homogeneous summand, is
right whiskering of the summand. -/
@[reassoc (attr := simp)]
lemma ι_whiskerRight {X Y : CochainComplex (ModuleCat.{v} R) ℤ} (f : X ⟶ Y)
    (Z : CochainComplex (ModuleCat.{v} R) ℤ) (p q j : ℤ) (h : p + q = j) :
    ιTensorObj X Z p q j h ≫ (f ▷ Z).f j = (f.f p ▷ Z.X q) ≫ ιTensorObj Y Z p q j h := by
  rw [whiskerRight_eq_mapBifunctorMap, ι_tensorHom, id_f, tensorHom_id]

/-- The degreewise component of the inverse left unitor of cochain complexes of modules is the
component of the auxiliary graded isomorphism `HomologicalComplex.leftUnitor'`, whose value is
recorded by `HomologicalComplex.leftUnitor'_inv`. -/
lemma leftUnitor_inv_f (X : CochainComplex (ModuleCat.{v} R) ℤ) (j : ℤ) :
    (λ_ X).inv.f j = (leftUnitor' X).inv j := by
  dsimp only [MonoidalCategoryStruct.leftUnitor, monoidalCategoryStruct,
    monoidalCategory, leftUnitor, Iso.symm_inv]
  simp only [Hom.isoOfComponents_hom_f, Functor.mapIso_hom, Iso.symm_hom]
  rfl

/-- The degreewise component of the inverse right unitor of cochain complexes of modules is the
component of the auxiliary graded isomorphism `HomologicalComplex.rightUnitor'`, whose value is
recorded by `HomologicalComplex.rightUnitor'_inv`. -/
lemma rightUnitor_inv_f (X : CochainComplex (ModuleCat.{v} R) ℤ) (j : ℤ) :
    (ρ_ X).inv.f j = (rightUnitor' X).inv j := by
  dsimp only [MonoidalCategoryStruct.rightUnitor, monoidalCategoryStruct,
    monoidalCategory, rightUnitor, Iso.symm_inv]
  simp only [Hom.isoOfComponents_hom_f, Functor.mapIso_hom, Iso.symm_hom]
  rfl

/-- The associator of cochain complexes of modules, restricted to the summand indexed by the
degrees `p`, `q` and `r`, is the associator of the three summands. The intermediate
degrees `pq` and `qr` may be any degrees equal to `p + q` and `q + r`. -/
@[reassoc]
lemma ι_ι_associator_hom (X Y Z : CochainComplex (ModuleCat.{v} R) ℤ) (p q r pq qr j : ℤ)
    (hpq : p + q = pq) (hqr : q + r = qr) (h : pq + r = j) (h' : p + qr = j) :
    (ιTensorObj X Y p q pq hpq ▷ Z.X r) ≫
        ιTensorObj (X ⊗ Y) Z pq r j h ≫ (α_ X Y Z).hom.f j =
      (α_ (X.X p) (Y.X q) (Z.X r)).hom ≫ (X.X p ◁ ιTensorObj Y Z q r qr hqr) ≫
        ιTensorObj X (Y ⊗ Z) p qr j h' := by
  -- The totalization index of a triple tensor product is definitionally the sum of the three
  -- degrees; naming the reindexed hypothesis keeps every later term type-correct.
  have hr : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j :=
    show p + q + r = j by omega
  have e₁ : mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
      X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r j hr =
      (ιTensorObj X Y p q pq hpq ▷ Z.X r) ≫ ιTensorObj (X ⊗ Y) Z pq r j h := by
    rw [mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
      X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r pq j hpq h]
    rfl
  have e₂ : mapBifunctor₂₃.ι (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
      X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r j hr =
      (X.X p ◁ ιTensorObj Y Z q r qr hqr) ≫ ιTensorObj X (Y ⊗ Z) p qr j h' := by
    rw [mapBifunctor₂₃.ι_eq (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
      X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r qr j hqr h']
    rfl
  rw [← Category.assoc, ← e₁, ← e₂]
  -- Mathlib assembles the associator of homological complexes from
  -- `HomologicalComplex.mapBifunctorAssociatorX`, but states no component lemma for `α_`.
  have ha : (α_ X Y Z).hom.f j =
      (mapBifunctorAssociatorX (curriedAssociatorNatIso (ModuleCat.{v} R)) X Y Z
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) j).hom := rfl
  rw [ha]
  simp only [ι_mapBifunctorAssociatorX_hom, curriedAssociatorNatIso_hom_app_app_app]

end HomologicalComplex

namespace TauCeti

variable {R : Type v} [CommRing R]

/-- The inverse associator of cochain complexes of modules, restricted to a homogeneous
summand with arbitrary intermediate degrees, is the inverse associator of the three summands. -/
@[reassoc]
lemma ι_ι_associator_inv (X Y Z : CochainComplex (ModuleCat.{v} R) ℤ)
    (p q r pq qr j : ℤ) (hpq : p + q = pq) (hqr : q + r = qr) (h : pq + r = j)
    (h' : p + qr = j) :
    (X.X p ◁ HomologicalComplex.ιTensorObj Y Z q r qr hqr) ≫
        HomologicalComplex.ιTensorObj X (Y ⊗ Z) p qr j h' ≫ (α_ X Y Z).inv.f j =
      (α_ (X.X p) (Y.X q) (Z.X r)).inv ≫ (HomologicalComplex.ιTensorObj X Y p q pq hpq ▷ Z.X r) ≫
        HomologicalComplex.ιTensorObj (X ⊗ Y) Z pq r j h := by
  rw [← cancel_epi (α_ (X.X p) (Y.X q) (Z.X r)).hom, Iso.hom_inv_id_assoc,
    ← HomologicalComplex.ι_ι_associator_hom_assoc X Y Z p q r pq qr j hpq hqr h h',
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  -- `Category.comp_id` is stated for the identity of the codomain of `ιTensorObj`, which is
  -- spelled `(HomologicalComplex.tensorObj (X ⊗ Y) Z).X j` rather than `((X ⊗ Y) ⊗ Z).X j`.
  erw [Category.comp_id]

end TauCeti
