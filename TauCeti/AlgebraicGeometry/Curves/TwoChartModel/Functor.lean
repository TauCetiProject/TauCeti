/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Category
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.AlgHom
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Curve

/-!
# The contravariant two-chart model functor

The two-chart construction associates a regular proper curve to an algebraic function field.
Choosing a transcendental parameter once for each object turns this construction into a
functor `(FunctionFieldCat k)ᵒᵖ ⥤ Over (Spec k)`. Every image morphism is dominant, and its
pullback on function fields is the original embedding. In particular the functor is faithful.

`FunctionFieldCat.modelFunctionFieldEquiv` identifies the function field of each model with
the field it models. The computation rule `modelFunctionFieldEquiv_functionFieldMap` expresses
the compatibility of this identification with every morphism of the category.

This packages the existing `twoChartModel.homOfAlgHom`, including its identity and composition
laws. The extension of a field embedding to a scheme morphism is the valuative-criterion
construction in that module.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter I, Section 6, Proposition 6.8.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Appendix B.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.FunctionFieldCat

universe u

variable {k : Type u} [Field k]

noncomputable section

/-- A transcendental parameter for the two-chart model. It is chosen once per object, and is
not part of the data defining an object of the category. -/
def modelParameter (F : FunctionFieldCat.{u, u} k) : F :=
  F.isFunctionField.exists_transcendental.choose

/-- The parameter chosen for the model is transcendental over the base field. -/
theorem transcendental_modelParameter (F : FunctionFieldCat.{u, u} k) :
    Transcendental k (modelParameter F) :=
  F.isFunctionField.exists_transcendental.choose_spec

/-- A regular proper model of the function field, constructed using a chosen transcendental
parameter. The choice is shared by all morphisms involving this object. -/
abbrev model (F : FunctionFieldCat.{u, u} k) : Scheme.{u} :=
  TauCeti.AlgebraicGeometry.twoChartModel F.isFunctionField
    (transcendental_modelParameter F).ne_zero

/-- The model is a proper integral curve over `k`. -/
instance (F : FunctionFieldCat.{u, u} k) : (model F).IsCurveOver k :=
  TauCeti.AlgebraicGeometry.twoChartModel.isCurveOver (hF := F.isFunctionField)
    (transcendental_modelParameter F)

/-- Every local ring of the model is a valuation ring. At a closed point it is a discrete
valuation ring; at the generic point it is the function field. -/
instance (F : FunctionFieldCat.{u, u} k) (p : model F) :
    ValuationRing ((model F).presheaf.stalk p) :=
  TauCeti.AlgebraicGeometry.twoChartModel.valuationRing_stalk
    (transcendental_modelParameter F) p

/-- The canonical identification of the function field of the chosen two-chart model with
the original function field. -/
def modelFunctionFieldEquiv (F : FunctionFieldCat.{u, u} k) :
    (model F).functionField ≃ₐ[k] F :=
  TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv (hF := F.isFunctionField)
    (transcendental_modelParameter F)

/-- The contravariant two-chart model functor. Its morphisms are dominant morphisms over `k`.
Its codomain is the over category of schemes; properness and regularity of its objects are
provided by the instances on `model`. -/
-- The object computation is exposed because the function-field comparison has a dependent
-- type: the stalks of the functor's underlying scheme must compute to those of `model`.
@[expose] def modelFunctor (k : Type u) [Field k] :
    (FunctionFieldCat.{u, u} k)ᵒᵖ ⥤ Over (Spec (.of k)) where
  obj F := (model F.unop).asOver (Spec (.of k))
  map {F G} f := (TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom
    G.unop.isFunctionField F.unop.isFunctionField (transcendental_modelParameter G.unop).ne_zero
    (transcendental_modelParameter F.unop).ne_zero (transcendental_modelParameter G.unop)
    (transcendental_modelParameter F.unop) (ConcreteCategory.hom f.unop)).asOver (Spec (.of k))
  map_id F := by
    apply Over.OverMorphism.ext
    exact TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom_id
      F.unop.isFunctionField (transcendental_modelParameter F.unop).ne_zero
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact (TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom_comp ..).symm

/-- The scheme underlying the functor's value is the chosen model. -/
@[simp] theorem modelFunctor_obj_left (F : (FunctionFieldCat.{u, u} k)ᵒᵖ) :
    ((modelFunctor k).obj F).left = model F.unop := (rfl)

/-- The underlying scheme of each functor value is a proper integral curve. -/
instance (F : (FunctionFieldCat.{u, u} k)ᵒᵖ) :
    ((modelFunctor k).obj F).left.IsCurveOver k :=
  inferInstanceAs ((model F.unop).IsCurveOver k)

/-- Every morphism produced by the model functor is dominant. -/
instance {F G : (FunctionFieldCat.{u, u} k)ᵒᵖ} (f : F ⟶ G) :
    IsDominant ((modelFunctor k).map f).left :=
  inferInstanceAs (IsDominant (TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom
    G.unop.isFunctionField F.unop.isFunctionField (transcendental_modelParameter G.unop).ne_zero
    (transcendental_modelParameter F.unop).ne_zero (transcendental_modelParameter G.unop)
    (transcendental_modelParameter F.unop) (ConcreteCategory.hom f.unop)))

/-- Under the identifications of the model function fields, pullback along a functor image is
the original field embedding. -/
@[simp] theorem modelFunctionFieldEquiv_functionFieldMap
    {F G : (FunctionFieldCat.{u, u} k)ᵒᵖ} (f : F ⟶ G) (z : G.unop) :
    modelFunctionFieldEquiv F.unop (((modelFunctor k).map f).left.functionFieldMap
      ((modelFunctionFieldEquiv G.unop).symm z)) = f.unop z :=
  TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv_functionFieldMap_homOfAlgHom
    G.unop.isFunctionField F.unop.isFunctionField (transcendental_modelParameter G.unop).ne_zero
    (transcendental_modelParameter F.unop).ne_zero (ConcreteCategory.hom f.unop) z

/-- Distinct embeddings induce distinct morphisms of models. -/
instance : (modelFunctor k).Faithful where
  map_injective {F G} f g h := by
    apply Quiver.Hom.unop_inj
    apply ConcreteCategory.hom_ext
    intro z
    have hfield : ((modelFunctor k).map f).left.functionFieldMap =
        ((modelFunctor k).map g).left.functionFieldMap := by
      congr 1
      exact congrArg Over.Hom.left h
    rw [← modelFunctionFieldEquiv_functionFieldMap f z,
      ← modelFunctionFieldEquiv_functionFieldMap g z, hfield]

end

end TauCeti.FunctionFieldCat
