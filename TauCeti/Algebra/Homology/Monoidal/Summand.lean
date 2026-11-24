/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Basic

/-!
# The monoidal structure of homological complexes on homogeneous summands

Mathlib's `HomologicalComplex.monoidalCategory` totalizes the degreewise tensor product, so every
structural map of a monoidal category of homological complexes, such as
`CochainComplex (ModuleCat R) ℤ` or `ChainComplex C ℕ`, is assembled from maps on the homogeneous
summands `X.X p ⊗ Y.X q` of `X ⊗ Y`.  Mathlib states the component formulas for the auxiliary
constructions the monoidal structure is built from — `HomologicalComplex.mapBifunctorMap`,
`HomologicalComplex.leftUnitor'`, `HomologicalComplex.rightUnitor'` and
`HomologicalComplex.mapBifunctorAssociatorX` — but not for `⊗ₘ`, the whiskerings, `λ_`, `ρ_` and
`α_` themselves.  This file supplies that last step, so that a calculation on homogeneous summands
never has to unfold the monoidal structure.  The formulas are stated for homological complexes of
any shape `c` on an additive monoid `I` of degrees with `[DecidableEq I]` and `c.TensorSigns`, in
any preadditive monoidal category whose tensor product is additive in each variable.
`HomologicalComplex.ι_tensorHom` and
`HomologicalComplex.XIsoOfEq_hom_tensorHom_XIsoOfEq_hom_ιTensorObj` assume only that the tensor
products of complexes they involve exist.  The formulas for the monoidal structure itself assume in
addition what Mathlib's `HomologicalComplex.monoidalCategoryStruct` needs: tensor products of
graded objects with good associativity (`GradedObject.HasTensor`,
`GradedObject.HasGoodTensor₁₂Tensor` and `GradedObject.HasGoodTensorTensor₂₃`), and a zero
object, from which, with the additivity of the tensor product, follows the preservation of the
empty colimit that Mathlib also assumes.  The evaluation of `HomologicalComplex.ι_tensorHom` on
pure tensors of modules, `HomologicalComplex.ι_tensorHom_apply`, is in
`TauCeti/Algebra/Homology/ModuleCat/Tensor.lean`.  The identification of `⊗ₘ`, `◁` and `▷` with
totalizations of morphisms, on which these formulas rest, is in
`TauCeti/Algebra/Homology/Monoidal/Basic.lean`.

## Main results

* `HomologicalComplex.ι_tensorHom` and `HomologicalComplex.ι_tensorHom_f`: the tensor product of
  two morphisms on a homogeneous summand, for `HomologicalComplex.tensorHom` and for `⊗ₘ`.
* `HomologicalComplex.XIsoOfEq_hom_tensorHom_XIsoOfEq_hom_ιTensorObj`: identifying the degrees of
  the two factors of a homogeneous summand along equalities of indices.
* `HomologicalComplex.ιTensorObj_comp_XIsoOfEq_hom`: identifying the total degree of a homogeneous
  summand along an equality of indices.
* `HomologicalComplex.ι_whiskerLeft` and `HomologicalComplex.ι_whiskerRight`: the two whiskerings
  on a homogeneous summand.
* `HomologicalComplex.leftUnitor_inv_f` and `HomologicalComplex.rightUnitor_inv_f`: the degreewise
  components of the inverse unitors, through the degree-`0` summand of `𝟙_ _`.
* `HomologicalComplex.ι_leftUnitor_hom_f` and `HomologicalComplex.ι_rightUnitor_hom_f`: the
  unitors on the summands `(𝟙_ _).X 0 ⊗ X.X j` and `X.X j ⊗ (𝟙_ _).X 0`.
* `HomologicalComplex.mapBifunctor₁₂.ι_eq_whiskerRight` and
  `HomologicalComplex.mapBifunctor₂₃.ι_eq_whiskerLeft`: the inclusions of the summand
  `X.X p ⊗ Y.X q ⊗ Z.X r` into `(X ⊗ Y) ⊗ Z` and `X ⊗ (Y ⊗ Z)` via whiskered `ιTensorObj`.
* `HomologicalComplex.ι_ι_associator_hom` and `HomologicalComplex.ι_ι_associator_inv`: the
  associator and its inverse on the summand `X.X p ⊗ Y.X q ⊗ Z.X r`, with arbitrary intermediate
  degrees.

The analogous formula for the differential of a tensor product is
`HomologicalComplex.ι_tensorObj_d` in `TauCeti/Algebra/Homology/Monoidal/Tensor/Differential.lean`.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

section General

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]

/-- The tensor product of two morphisms of homological complexes, restricted to a homogeneous
summand, is the tensor product of their components.  Mathlib states this only for
`HomologicalComplex.mapBifunctorMap`, by which `⊗ₘ` is defined.  It is not `@[simp]`: its
left-hand side is already rewritten by Mathlib's simp lemma `HomologicalComplex.ι_mapBifunctorMap`,
into the composite of the two whiskerings. -/
@[reassoc]
lemma ι_tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    [HasTensor K₁ K₂] [HasTensor L₁ L₂]
    (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    ιTensorObj K₁ K₂ i₁ i₂ j h ≫ (tensorHom f₁ f₂).f j =
      (f₁.f i₁ ⊗ₘ f₂.f i₂) ≫ ιTensorObj L₁ L₂ i₁ i₂ j h := by
  refine (ι_mapBifunctorMap _ _ _ _ _ _ _ _).trans ?_
  simp [tensorHom_def]

/-- Identifying the degrees of the two factors along equalities of indices does not change the
inclusion of a summand into a tensor product of complexes. -/
@[reassoc (attr := simp)]
lemma XIsoOfEq_hom_tensorHom_XIsoOfEq_hom_ιTensorObj (K L : HomologicalComplex C c)
    [K.HasTensor L] {p p' q q' : I} (hp : p = p') (hq : q = q') (j : I) (h : p + q = j)
    (h' : p' + q' = j) :
    ((K.XIsoOfEq hp).hom ⊗ₘ (L.XIsoOfEq hq).hom) ≫ ιTensorObj K L p' q' j h' =
      ιTensorObj K L p q j h := by
  subst hp hq
  simp

/-- Identifying the degree of a summand of a tensor product along an equality of indices does not
change the inclusion of the summand. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_comp_XIsoOfEq_hom (K L : HomologicalComplex C c) [K.HasTensor L] {p q j j' : I}
    (h : p + q = j) (hj : j = j') :
    ιTensorObj K L p q j h ≫ ((tensorObj K L).XIsoOfEq hj).hom =
      ιTensorObj K L p q j' (h.trans hj) := by
  subst hj
  simp

-- Mathlib's monoidal structure assumes that tensoring preserves the empty colimit; here this
-- follows from the zero object and the additivity of the tensor product, as in
-- `TauCeti/Algebra/Homology/Monoidal/Basic.lean`.
attribute [local instance] Functor.preservesInitialObject_of_preservesZeroMorphisms

variable [HasZeroObject C] [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The tensor product `⊗ₘ` of two morphisms in the monoidal category of homological complexes,
restricted to a homogeneous summand, is the tensor product of their components.
`HomologicalComplex.ι_tensorHom` states this for `HomologicalComplex.tensorHom`, which needs only
the two tensor products involved to exist. -/
@[reassoc (attr := simp)]
lemma ι_tensorHom_f {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    ιTensorObj K₁ K₂ i₁ i₂ j h ≫ (f₁ ⊗ₘ f₂).f j =
      (f₁.f i₁ ⊗ₘ f₂.f i₂) ≫ ιTensorObj L₁ L₂ i₁ i₂ j h := by
  rw [tensorHom_eq_mapBifunctorMap]
  exact ι_tensorHom f₁ f₂ i₁ i₂ j h

/-- Left whiskering of homological complexes, restricted to a homogeneous summand, is left
whiskering of the summand. -/
@[reassoc (attr := simp)]
lemma ι_whiskerLeft (X : HomologicalComplex C c)
    {Y Z : HomologicalComplex C c} (g : Y ⟶ Z) (p q j : I) (h : p + q = j) :
    ιTensorObj X Y p q j h ≫ (X ◁ g).f j = (X.X p ◁ g.f q) ≫ ιTensorObj X Z p q j h := by
  rw [whiskerLeft_eq_mapBifunctorMap, ι_tensorHom, id_f, id_tensorHom]

/-- Right whiskering of homological complexes, restricted to a homogeneous summand, is
right whiskering of the summand. -/
@[reassoc (attr := simp)]
lemma ι_whiskerRight {X Y : HomologicalComplex C c} (f : X ⟶ Y)
    (Z : HomologicalComplex C c) (p q j : I) (h : p + q = j) :
    ιTensorObj X Z p q j h ≫ (f ▷ Z).f j = (f.f p ▷ Z.X q) ≫ ιTensorObj Y Z p q j h := by
  rw [whiskerRight_eq_mapBifunctorMap, ι_tensorHom, id_f, tensorHom_id]

/-- The degreewise component of the inverse left unitor of homological complexes: on degree `j`
it is the inverse left unitor of `X.X j`, then the identification
`𝟙_ C ≅ (𝟙_ (HomologicalComplex C c)).X 0` (the inverse of `HomologicalComplex.singleObjXSelf`)
whiskered on the right by `X.X j`, then the inclusion of the summand `(𝟙_ _).X 0 ⊗ X.X j` of
`𝟙_ _ ⊗ X`. -/
lemma leftUnitor_inv_f (X : HomologicalComplex C c) (j : I) :
    (λ_ X).inv.f j = (λ_ (X.X j)).inv ≫ ((singleObjXSelf c 0 (𝟙_ C)).inv ▷ X.X j) ≫
      ιTensorObj (𝟙_ (HomologicalComplex C c)) X 0 j j (zero_add j) := by
  -- `HomologicalComplex.leftUnitor'_inv` is stated with `tensorUnit C c`, the definition of
  -- `𝟙_ (HomologicalComplex C c)`.
  refine Eq.trans ?_ (leftUnitor'_inv X j)
  simp [MonoidalCategoryStruct.leftUnitor, leftUnitor]

/-- The degreewise component of the inverse right unitor of homological complexes: on degree `j`
it is the inverse right unitor of `X.X j`, then the identification
`𝟙_ C ≅ (𝟙_ (HomologicalComplex C c)).X 0` (the inverse of `HomologicalComplex.singleObjXSelf`)
whiskered on the left by `X.X j`, then the inclusion of the summand `X.X j ⊗ (𝟙_ _).X 0` of
`X ⊗ 𝟙_ _`. -/
lemma rightUnitor_inv_f (X : HomologicalComplex C c) (j : I) :
    (ρ_ X).inv.f j = (ρ_ (X.X j)).inv ≫ (X.X j ◁ (singleObjXSelf c 0 (𝟙_ C)).inv) ≫
      ιTensorObj X (𝟙_ (HomologicalComplex C c)) j 0 j (add_zero j) := by
  -- `HomologicalComplex.rightUnitor'_inv` is stated with `tensorUnit C c`, the definition of
  -- `𝟙_ (HomologicalComplex C c)`.
  refine Eq.trans ?_ (rightUnitor'_inv X j)
  simp [MonoidalCategoryStruct.rightUnitor, rightUnitor]

/-- The left unitor of homological complexes on the summand `(𝟙_).X 0 ⊗ X.X j` of `𝟙_ ⊗ X`: the
identification of the degree-zero term of the tensor unit with `𝟙_ C`, followed by the left
unitor of `C`. -/
@[reassoc]
lemma ι_leftUnitor_hom_f (X : HomologicalComplex C c) (j : I) :
    ιTensorObj (𝟙_ (HomologicalComplex C c)) X 0 j j (zero_add j) ≫ (λ_ X).hom.f j =
      ((singleObjXSelf c 0 (𝟙_ C)).hom ▷ X.X j) ≫ (λ_ (X.X j)).hom := by
  rw [← cancel_mono ((λ_ X).inv.f j), Category.assoc, Category.assoc, ← comp_f, Iso.hom_inv_id,
    id_f, leftUnitor_inv_f, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    Iso.hom_inv_id, id_whiskerRight, Category.id_comp]
  -- `ιTensorObj` lands in `(tensorObj 𝟙_ X).X j`, the definition of `(𝟙_ ⊗ X).X j`, so
  -- `Category.comp_id` applies only up to unfolding the monoidal tensor product.
  exact Category.comp_id _

/-- The right unitor of homological complexes on the summand `X.X j ⊗ (𝟙_).X 0` of `X ⊗ 𝟙_`: the
identification of the degree-zero term of the tensor unit with `𝟙_ C`, followed by the right
unitor of `C`. -/
@[reassoc]
lemma ι_rightUnitor_hom_f (X : HomologicalComplex C c) (j : I) :
    ιTensorObj X (𝟙_ (HomologicalComplex C c)) j 0 j (add_zero j) ≫ (ρ_ X).hom.f j =
      (X.X j ◁ (singleObjXSelf c 0 (𝟙_ C)).hom) ≫ (ρ_ (X.X j)).hom := by
  rw [← cancel_mono ((ρ_ X).inv.f j), Category.assoc, Category.assoc, ← comp_f, Iso.hom_inv_id,
    id_f, rightUnitor_inv_f, Iso.hom_inv_id_assoc, ← whiskerLeft_comp_assoc,
    Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
  -- `ιTensorObj` lands in `(tensorObj X 𝟙_).X j`, the definition of `(X ⊗ 𝟙_).X j`, so
  -- `Category.comp_id` applies only up to unfolding the monoidal tensor product.
  exact Category.comp_id _

/-- The inclusion `HomologicalComplex.mapBifunctor₁₂.ι` of the summand `X.X p ⊗ Y.X q ⊗ Z.X r`
into `(X ⊗ Y) ⊗ Z`, written with the monoidal whiskering and `HomologicalComplex.ιTensorObj`.
Mathlib's `HomologicalComplex.mapBifunctor₁₂.ι_eq` states it for the raw totalization. -/
@[reassoc]
lemma mapBifunctor₁₂.ι_eq_whiskerRight (X Y Z : HomologicalComplex C c) (p q r pq j : I)
    (hpq : p + q = pq) (h : pq + r = j) :
    mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C) X Y Z c c p q r j
        (by rw [← h, ← hpq]; rfl) =
      (ιTensorObj X Y p q pq hpq ▷ Z.X r) ≫ ιTensorObj (X ⊗ Y) Z pq r j h := by
  rw [mapBifunctor₁₂.ι_eq (curriedTensor C) (curriedTensor C) X Y Z c c p q r pq j hpq h]
  -- `(curriedTensor C).map f).app W` is `f ▷ W` and `ιMapBifunctor` is `ιTensorObj`, by definition.
  rfl

/-- The inclusion `HomologicalComplex.mapBifunctor₂₃.ι` of the summand `X.X p ⊗ Y.X q ⊗ Z.X r`
into `X ⊗ (Y ⊗ Z)`, written with the monoidal whiskering and `HomologicalComplex.ιTensorObj`.
Mathlib's `HomologicalComplex.mapBifunctor₂₃.ι_eq` states it for the raw totalization. -/
@[reassoc]
lemma mapBifunctor₂₃.ι_eq_whiskerLeft (X Y Z : HomologicalComplex C c) (p q r qr j : I)
    (hqr : q + r = qr) (h : p + qr = j) :
    mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) X Y Z c c c p q r j
        (by rw [← h, ← hqr]; exact add_assoc p q r) =
      (X.X p ◁ ιTensorObj Y Z q r qr hqr) ≫ ιTensorObj X (Y ⊗ Z) p qr j h := by
  rw [mapBifunctor₂₃.ι_eq (curriedTensor C) (curriedTensor C) X Y Z c c c p q r qr j hqr h]
  -- `(curriedTensor C).obj W).map f` is `W ◁ f` and `ιMapBifunctor` is `ιTensorObj`, by definition.
  rfl

/-- The associator of homological complexes, restricted to the summand indexed by the
degrees `p`, `q` and `r`, is the associator of the three summands. The intermediate
degrees `pq` and `qr` may be any degrees equal to `p + q` and `q + r`. -/
@[reassoc]
lemma ι_ι_associator_hom (X Y Z : HomologicalComplex C c) (p q r pq qr j : I)
    (hpq : p + q = pq) (hqr : q + r = qr) (h : pq + r = j) (h' : p + qr = j) :
    (ιTensorObj X Y p q pq hpq ▷ Z.X r) ≫
        ιTensorObj (X ⊗ Y) Z pq r j h ≫ (α_ X Y Z).hom.f j =
      (α_ (X.X p) (Y.X q) (Z.X r)).hom ≫ (X.X p ◁ ιTensorObj Y Z q r qr hqr) ≫
        ιTensorObj X (Y ⊗ Z) p qr j h' := by
  rw [← Category.assoc, ← mapBifunctor₁₂.ι_eq_whiskerRight X Y Z p q r pq j hpq h,
    ← mapBifunctor₂₃.ι_eq_whiskerLeft X Y Z p q r qr j hqr h']
  -- Mathlib assembles the associator of homological complexes from
  -- `HomologicalComplex.mapBifunctorAssociatorX`, but states no component lemma for `α_`.
  have ha : (α_ X Y Z).hom.f j =
      (mapBifunctorAssociatorX (curriedAssociatorNatIso C) X Y Z c c c j).hom := rfl
  rw [ha]
  simp only [ι_mapBifunctorAssociatorX_hom, curriedAssociatorNatIso_hom_app_app_app]

/-- The inverse associator of homological complexes, restricted to a homogeneous
summand with arbitrary intermediate degrees, is the inverse associator of the three summands. -/
@[reassoc]
lemma ι_ι_associator_inv (X Y Z : HomologicalComplex C c)
    (p q r pq qr j : I) (hpq : p + q = pq) (hqr : q + r = qr) (h : pq + r = j)
    (h' : p + qr = j) :
    (X.X p ◁ ιTensorObj Y Z q r qr hqr) ≫ ιTensorObj X (Y ⊗ Z) p qr j h' ≫ (α_ X Y Z).inv.f j =
      (α_ (X.X p) (Y.X q) (Z.X r)).inv ≫ (ιTensorObj X Y p q pq hpq ▷ Z.X r) ≫
        ιTensorObj (X ⊗ Y) Z pq r j h := by
  -- Move the degree-`j` component of `α_ X Y Z` to the right-hand side; going through
  -- `(α_ X Y Z).hom.f j ≫ (α_ X Y Z).inv.f j` instead would leave an identity whose object is
  -- spelled differently from the codomain of `ιTensorObj`.
  rw [← Hom.isoApp_inv, ← Category.assoc, Iso.comp_inv_eq, Hom.isoApp_hom]
  simp only [Category.assoc, ι_ι_associator_hom X Y Z p q r pq qr j hpq hqr h h',
    Iso.inv_hom_id_assoc]

end General

end HomologicalComplex
