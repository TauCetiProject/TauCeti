/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import TauCeti.Algebra.Homology.Bifunctor.Basic

/-!
# The tensor product of morphisms of homological complexes

Mathlib's `HomologicalComplex.monoidalCategory` (in `Mathlib.Algebra.Homology.Monoidal`) defines
`⊗ₘ`, `◁` and `▷` on homological complexes as the totalizations
`HomologicalComplex.mapBifunctorMap` of the degreewise tensor product, but states no lemma
exposing these definitions.  This file records them, together with the vanishing of the tensor
product of morphisms when either factor is zero.  The formulas on homogeneous summands built from
them are in `TauCeti/Algebra/Homology/Monoidal/Summand.lean`.

Since `MonoidalCategory.curriedTensor (HomologicalComplex C c)` sends `K` and `L` to
`HomologicalComplex.mapBifunctor K L (curriedTensor C) c` and acts on morphisms by
`HomologicalComplex.mapBifunctorMap`, it is definitionally equal to Mathlib's
`(curriedTensor C).map₂HomologicalComplex c c c` (for `c = ComplexShape.up ℤ`, the abbreviation
`(curriedTensor C).map₂CochainComplex`), so `Iso.refl` compares the two.

Mathlib's monoidal structure assumes that tensoring with an object on either side preserves the
empty colimit.  When `C` has a zero object and tensoring is additive in each variable, this
follows from `CategoryTheory.Functor.preservesInitialObject_of_preservesZeroMorphisms`, which is
made a local instance here, so the statements below do not assume it.

## Main results

* `HomologicalComplex.zero_tensorHom` and `HomologicalComplex.tensorHom_zero`: the tensor product
  of morphisms vanishes when either factor does.
* `HomologicalComplex.tensorHom_eq_mapBifunctorMap`: `⊗ₘ` of homological complexes is the
  totalization `HomologicalComplex.mapBifunctorMap` of the two morphisms.
* `HomologicalComplex.whiskerLeft_eq_mapBifunctorMap` and
  `HomologicalComplex.whiskerRight_eq_mapBifunctorMap`: the same for the two whiskerings.
* `HomologicalComplex.whiskerLeft_zero` and `HomologicalComplex.zero_whiskerRight`: whiskering the
  zero morphism gives zero, so `tensorLeft X` and `tensorRight X` preserve zero morphisms.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]

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

attribute [local instance] Functor.preservesInitialObject_of_preservesZeroMorphisms

variable [HasZeroObject C] [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- In the monoidal category of homological complexes, `⊗ₘ` is the totalization of the two
morphisms.  Mathlib defines `HomologicalComplex.monoidalCategory` this way, but states no lemma
exposing it. -/
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

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- Left tensoring with a homological complex preserves zero morphisms. -/
instance (X : HomologicalComplex C c) : (tensorLeft X).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ whiskerLeft_zero X⟩

/-- Right tensoring with a homological complex preserves zero morphisms. -/
instance (X : HomologicalComplex C c) : (tensorRight X).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ zero_whiskerRight X⟩

end HomologicalComplex
