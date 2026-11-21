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
public import TauCeti.Algebra.Homology.Bifunctor.Basic

/-!
# The monoidal structure of homological complexes on homogeneous summands

Mathlib's `HomologicalComplex.monoidalCategory` totalizes the degreewise tensor product, so every
structural map of a monoidal category of homological complexes, such as
`CochainComplex (ModuleCat R) ℤ` or `ChainComplex C ℕ`, is assembled from maps on the homogeneous
summands `X.X p ⊗ Y.X q` of `X ⊗ Y`.  Mathlib states the component formulas for the auxiliary
constructions the monoidal structure is built from — `HomologicalComplex.mapBifunctorMap`,
`HomologicalComplex.leftUnitor'`, `HomologicalComplex.rightUnitor'` and
`HomologicalComplex.mapBifunctorAssociatorX` — but not for the whiskerings, `λ_`, `ρ_` and `α_`
themselves.  This file supplies that last step, so that a calculation on homogeneous summands
never has to unfold the monoidal structure.  The formulas hold verbatim for homological complexes
of any shape in any monoidal preadditive category, and are stated in that generality; only their
evaluation on pure tensors, `HomologicalComplex.ι_tensorHom_apply`, is specific to modules.
The bifunctor `(curriedTensor C).map₂HomologicalComplex c c c` induced on complexes is also
identified with the curried tensor bifunctor of the monoidal structure. Its values are computed by
Mathlib's simp lemmas `CategoryTheory.Functor.map₂HomologicalComplex_obj_obj`, `_obj_map` and
`_map_app`, as `HomologicalComplex.mapBifunctor` and `HomologicalComplex.mapBifunctorMap`, of which
`HomologicalComplex.tensorObj` and `HomologicalComplex.tensorHom` are abbreviations.

## Main results

* `HomologicalComplex.ι_tensorHom`: the tensor product of two morphisms on a homogeneous summand.
* `HomologicalComplex.XIsoOfEq_hom_tensorHom_XIsoOfEq_hom_ιTensorObj`: identifying the degrees of
  the two factors of a homogeneous summand along equalities of indices.
* `HomologicalComplex.zero_tensorHom` and `HomologicalComplex.tensorHom_zero`: the tensor product
  of morphisms vanishes when either factor does.
* `HomologicalComplex.tensorHom_eq_mapBifunctorMap`: `⊗ₘ` of homological complexes is the
  totalization `HomologicalComplex.mapBifunctorMap` of the two morphisms.
* `HomologicalComplex.ι_whiskerLeft` and `HomologicalComplex.ι_whiskerRight`: the two whiskerings
  on a homogeneous summand.
* `HomologicalComplex.whiskerLeft_zero` and `HomologicalComplex.zero_whiskerRight`: whiskering the
  zero morphism gives zero, so `tensorLeft X` and `tensorRight X` preserve zero morphisms.
* `HomologicalComplex.leftUnitor_inv_f` and `HomologicalComplex.rightUnitor_inv_f`: the degreewise
  components of the inverse unitors.
* `HomologicalComplex.mapBifunctor₁₂.ι_eq_whiskerRight` and
  `HomologicalComplex.mapBifunctor₂₃.ι_eq_whiskerLeft`: the inclusions of the summand
  `X.X p ⊗ Y.X q ⊗ Z.X r` into `(X ⊗ Y) ⊗ Z` and `X ⊗ (Y ⊗ Z)` via whiskered `ιTensorObj`.
* `HomologicalComplex.ι_ι_associator_hom` and `HomologicalComplex.ι_ι_associator_inv`: the
  associator and its inverse on the summand `X.X p ⊗ Y.X q ⊗ Z.X r`, with arbitrary intermediate
  degrees.
* `HomologicalComplex.curriedTensorIsoMap₂HomologicalComplex`: natural isomorphism between
  `MonoidalCategory.curriedTensor (HomologicalComplex C c)` and
  `(MonoidalCategory.curriedTensor C).map₂HomologicalComplex c c c`; for cochain complexes the
  latter is `(MonoidalCategory.curriedTensor C).map₂CochainComplex`.

The analogous formula for the differential of a tensor product is
`HomologicalComplex.ι_tensorObj_d` in `TauCeti/Algebra/Homology/Monoidal/Tensor/Differential.lean`.
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

/-- The tensor product of homological complexes of the zero morphism with any morphism is zero. -/
lemma zero_tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₂ : K₂ ⟶ L₂)
    [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
    tensorHom (0 : K₁ ⟶ L₁) f₂ = 0 :=
  mapBifunctorMap_zero_left (curriedTensor C) c K₁ L₁ f₂

/-- The tensor product of homological complexes of any morphism with the zero morphism is zero. -/
lemma tensorHom_zero {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₁ : K₁ ⟶ L₁)
    [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
    tensorHom f₁ (0 : K₂ ⟶ L₂) = 0 :=
  mapBifunctorMap_zero_right (curriedTensor C) c f₁ K₂ L₂

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

variable [HasZeroObject C] [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₂, PreservesColimit (CategoryTheory.Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- In the monoidal category of homological complexes, `⊗ₘ` is the totalization of the two
morphisms.  Mathlib defines `HomologicalComplex.monoidalCategory` this way, but states no lemma
exposing it, so `HomologicalComplex.ι_tensorHom` does not apply to `⊗ₘ` without this rewrite. -/
lemma tensorHom_eq_mapBifunctorMap {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₁ : K₁ ⟶ L₁)
    (f₂ : K₂ ⟶ L₂) :
    f₁ ⊗ₘ f₂ = mapBifunctorMap f₁ f₂ (curriedTensor C) c :=
  rfl

/-- Left whiskering of homological complexes is the totalization of the identity and
the given morphism.  Mathlib defines the monoidal structure on homological complexes through
`HomologicalComplex.mapBifunctorMap`, but states no component lemma for `◁`. -/
lemma whiskerLeft_eq_mapBifunctorMap (X : HomologicalComplex C c) {Y Z : HomologicalComplex C c}
    (g : Y ⟶ Z) :
    X ◁ g = mapBifunctorMap (𝟙 X) g (curriedTensor C) c :=
  rfl

/-- Right whiskering of homological complexes is the totalization of the given
morphism and the identity; the counterpart of
`HomologicalComplex.whiskerLeft_eq_mapBifunctorMap`. -/
lemma whiskerRight_eq_mapBifunctorMap {X Y : HomologicalComplex C c} (f : X ⟶ Y)
    (Z : HomologicalComplex C c) :
    f ▷ Z = mapBifunctorMap f (𝟙 Z) (curriedTensor C) c :=
  rfl

/-- Left whiskering of homological complexes by the zero morphism is zero.  Homological complexes
carry no `MonoidalPreadditive` instance, so `MonoidalPreadditive.whiskerLeft_zero` does not
apply. -/
@[simp]
lemma whiskerLeft_zero (X : HomologicalComplex C c) {Y Z : HomologicalComplex C c} :
    X ◁ (0 : Y ⟶ Z) = 0 :=
  tensorHom_zero _

/-- Right whiskering of homological complexes by the zero morphism is zero; the counterpart of
`HomologicalComplex.whiskerLeft_zero`. -/
@[simp]
lemma zero_whiskerRight {X Y : HomologicalComplex C c} (Z : HomologicalComplex C c) :
    (0 : X ⟶ Y) ▷ Z = 0 :=
  zero_tensorHom _

section

variable [∀ X₁, PreservesColimit (CategoryTheory.Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- Left tensoring with a homological complex preserves zero morphisms. -/
instance (X : HomologicalComplex C c) : (tensorLeft X).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ whiskerLeft_zero X⟩

/-- Right tensoring with a homological complex preserves zero morphisms. -/
instance (X : HomologicalComplex C c) : (tensorRight X).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ zero_whiskerRight X⟩

variable (C c) in
/-- The curried tensor bifunctor of the totalized monoidal structure on `HomologicalComplex C c`
is naturally isomorphic to `(curriedTensor C).map₂HomologicalComplex c c c`. -/
noncomputable def curriedTensorIsoMap₂HomologicalComplex :
    curriedTensor (HomologicalComplex C c) ≅ (curriedTensor C).map₂HomologicalComplex c c c :=
  NatIso.ofComponents
    (fun K ↦ NatIso.ofComponents (fun L ↦ Iso.refl (K ⊗ L))
      (fun g ↦ by simp [whiskerLeft_eq_mapBifunctorMap]))
    (fun f ↦ by ext L; simp [whiskerRight_eq_mapBifunctorMap])

/-- Evaluating the forward direction of `curriedTensorIsoMap₂HomologicalComplex` on complexes `K`
and `L` is the identity on `K ⊗ L`. -/
@[simp]
lemma curriedTensorIsoMap₂HomologicalComplex_hom_app_app (K L : HomologicalComplex C c) :
    ((curriedTensorIsoMap₂HomologicalComplex C c).hom.app K).app L = 𝟙 (K ⊗ L) := by
  simp [curriedTensorIsoMap₂HomologicalComplex]

/-- Evaluating the inverse direction of `curriedTensorIsoMap₂HomologicalComplex` on complexes `K`
and `L` is the identity on `K ⊗ L`. -/
@[simp]
lemma curriedTensorIsoMap₂HomologicalComplex_inv_app_app (K L : HomologicalComplex C c) :
    ((curriedTensorIsoMap₂HomologicalComplex C c).inv.app K).app L = 𝟙 (K ⊗ L) := by
  simp [curriedTensorIsoMap₂HomologicalComplex]

end

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

/-- The degreewise component of the inverse left unitor of homological complexes is the
component of the auxiliary graded isomorphism `HomologicalComplex.leftUnitor'`, whose value is
recorded by `HomologicalComplex.leftUnitor'_inv`. -/
lemma leftUnitor_inv_f (X : HomologicalComplex C c) (j : I) :
    (λ_ X).inv.f j = (leftUnitor' X).inv j := by
  simp [MonoidalCategoryStruct.leftUnitor, leftUnitor]

/-- The degreewise component of the inverse right unitor of homological complexes is the
component of the auxiliary graded isomorphism `HomologicalComplex.rightUnitor'`, whose value is
recorded by `HomologicalComplex.rightUnitor'_inv`. -/
lemma rightUnitor_inv_f (X : HomologicalComplex C c) (j : I) :
    (ρ_ X).inv.f j = (rightUnitor' X).inv j := by
  simp [MonoidalCategoryStruct.rightUnitor, rightUnitor]

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

section ComplexesOfModules

variable {R : Type v} [CommRing R]
variable {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]

/-- The tensor product of two morphisms of homological complexes of modules on a pure tensor in a
homogeneous summand: the tensor product of the components. -/
lemma ι_tensorHom_apply {K₁ K₂ L₁ L₂ : HomologicalComplex (ModuleCat.{v} R) c} (f₁ : K₁ ⟶ L₁)
    (f₂ : K₂ ⟶ L₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] (i₁ i₂ j : I) (h : i₁ + i₂ = j)
    (a : K₁.X i₁) (b : K₂.X i₂) :
    (tensorHom f₁ f₂).f j ((ιTensorObj K₁ K₂ i₁ i₂ j h).hom (a ⊗ₜ[R] b)) =
      (ιTensorObj L₁ L₂ i₁ i₂ j h).hom (f₁.f i₁ a ⊗ₜ[R] f₂.f i₂ b) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ι_tensorHom f₁ f₂ i₁ i₂ j h)) (a ⊗ₜ[R] b)

end ComplexesOfModules

end HomologicalComplex
