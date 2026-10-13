/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Category
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Classification

/-!
# Regular proper curves are anti-equivalent to algebraic function fields

Let `k` be a field. This file proves that the function-field functor
`X ↦ k(X)` from regular proper curves over `k` (with dominant `k`-morphisms) to algebraic
function fields of one variable over `k` (with `k`-embeddings) is an anti-equivalence of
categories. Its inverse is the **model functor**: a function field `F` goes to its two-chart
model, the normalization of the projective line in `F` glued from the normalizations of `k[x]`
and `k[x⁻¹]` for a transcendental `x ∈ F` chosen once and for all, and a `k`-embedding
`φ : F → F'` goes to the unique dominant `k`-morphism of models whose pullback of rational functions
is `φ` (`TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom`).

The two natural isomorphisms are the ones already constructed object by object:

* the function field of the model of `F` is `F`
  (`TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv`), naturally in `F` because the
  pullback along `homOfAlgHom φ` is `φ`;
* a regular proper curve `X` is the model of its function field
  (`AlgebraicGeometry.Scheme.isoTwoChartModel`), naturally in `X` because a dominant
  `k`-morphism into a separated scheme is determined by its pullback of rational functions.

## Main definitions

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.twoChartModelFunctor`: the model functor
  `F ↦ twoChartModel F`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.twoChartModelFunctorCompFunctionFieldFunctorIso`:
  the function field of the model of `F` is `F`, naturally in `F`.
* `RegularProperCurveCat.idIsoFunctionFieldFunctorCompTwoChartModelFunctor`: a regular proper
  curve is the model of its function field, naturally in the curve.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.equivFunctionFieldCat`: **the anti-equivalence**
  `RegularProperCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ`, with functor the function-field functor,
  inverse the model functor, and the two natural isomorphisms above as counit and unit.

## Main results

* the instances `(functionFieldFunctor k).IsEquivalence` and
  `(twoChartModelFunctor k).IsEquivalence`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Corollary I.6.12.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford GTM 6, 2002, Section 7.3.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

public section

open CategoryTheory Opposite _root_.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace RegularProperCurveCat

variable {k : Type u} [Field k]

/-- The transcendental function of `F` from which the model of `F` is built. -/
private noncomputable def modelGenerator (F : FunctionFieldCat k) : F :=
  F.isFunctionField.exists_transcendental.choose

private theorem transcendental_modelGenerator (F : FunctionFieldCat k) :
    Transcendental k (modelGenerator F) :=
  F.isFunctionField.exists_transcendental.choose_spec

private theorem modelGenerator_ne_zero (F : FunctionFieldCat k) : modelGenerator F ≠ 0 :=
  (transcendental_modelGenerator F).ne_zero

/-- The two-chart model of `F`, built from the chosen transcendental function, as a regular proper
curve over `k`. -/
private noncomputable abbrev modelObj (F : FunctionFieldCat k) : RegularProperCurveCat k where
  toScheme := twoChartModel F.isFunctionField (modelGenerator_ne_zero F)
  isCurveOver := twoChartModel.isCurveOver (transcendental_modelGenerator F)
  isDiscreteValuationRing_stalk :=
    twoChartModel.isDiscreteValuationRing_stalk (transcendental_modelGenerator F)

/-- The identification of the function field of the model of `F` with `F`. -/
private noncomputable abbrev modelEquiv (F : FunctionFieldCat k) :
    (twoChartModel F.isFunctionField (modelGenerator_ne_zero F)).functionField ≃ₐ[k] F :=
  twoChartModel.functionFieldEquiv (transcendental_modelGenerator F)

/-- The morphism of models induced by a `k`-embedding of function fields. -/
private noncomputable abbrev modelHom {F G : FunctionFieldCat k} (φ : F ⟶ G) :
    modelObj G ⟶ modelObj F :=
  ⟨twoChartModel.homOfAlgHom F.isFunctionField G.isFunctionField (modelGenerator_ne_zero F)
    (modelGenerator_ne_zero G) (transcendental_modelGenerator F) (transcendental_modelGenerator G)
    φ.hom⟩

variable (k) in
/-- **The model functor**: the contravariant functor from algebraic function fields over `k` to
regular proper curves over `k` sending `F` to its two-chart model (the normalization of the
projective line in `F`) and a `k`-embedding `φ : F → F'` to the unique dominant `k`-morphism of
models whose pullback of rational functions is `φ`. -/
noncomputable def twoChartModelFunctor : (FunctionFieldCat k)ᵒᵖ ⥤ RegularProperCurveCat k where
  obj F := modelObj F.unop
  map φ := modelHom φ.unop
  map_id F := by
    ext1
    exact twoChartModel.homOfAlgHom_id ..
  map_comp φ ψ := by
    ext1
    exact (twoChartModel.homOfAlgHom_comp ..).symm

/-- The pullback of rational functions along the morphism of models induced by `φ : G → F` is
`φ`, read through the identifications of the function fields of the models with `G` and `F`. -/
private lemma functionFieldMap_modelHom {F G : FunctionFieldCat k} (φ : F ⟶ G) (z : F) :
    (modelHom φ).hom.functionFieldMap ((modelEquiv F).symm z) = (modelEquiv G).symm (φ.hom z) := by
  refine (modelEquiv G).injective ?_
  rw [AlgEquiv.apply_symm_apply]
  exact twoChartModel.functionFieldEquiv_functionFieldMap_homOfAlgHom ..

/-- The function field of the model of `F` is `F`. -/
private noncomputable def modelFunctionFieldIso (F : (FunctionFieldCat k)ᵒᵖ) :
    (twoChartModelFunctor k ⋙ functionFieldFunctor k).obj F ≅ F :=
  (FunctionFieldCat.isoMk (modelEquiv F.unop).symm).op

variable (k) in
/-- The function field of the model of `F` is `F`, naturally in `F`. -/
noncomputable def twoChartModelFunctorCompFunctionFieldFunctorIso :
    twoChartModelFunctor k ⋙ functionFieldFunctor k ≅ 𝟭 (FunctionFieldCat k)ᵒᵖ :=
  NatIso.ofComponents modelFunctionFieldIso fun φ ↦
    Quiver.Hom.unop_inj <| FunctionFieldCat.hom_ext <| AlgHom.ext fun z ↦
      -- Unfolding the functors, composition in the opposite category and `isoMk`, the two sides
      -- are the two sides of `functionFieldMap_modelHom`.
      (Scheme.Hom.functionFieldAlgHom_apply k _ _).trans (functionFieldMap_modelHom φ.unop z)

/-- The function field of a regular proper curve, as an object of `FunctionFieldCat k`. -/
private noncomputable abbrev functionFieldObj (X : RegularProperCurveCat k) : FunctionFieldCat k :=
  .of X.toScheme.functionField Scheme.IsCurveOver.isFunctionField

/-- A regular proper curve `X` is the model of its function field. -/
private noncomputable def isoModel (X : RegularProperCurveCat k) :
    X ≅ modelObj (functionFieldObj X) :=
  isoMk (X.toScheme.isoTwoChartModel (modelGenerator_ne_zero (functionFieldObj X))
    (transcendental_modelGenerator (functionFieldObj X)))

/-- The isomorphism `isoModel` is natural: for a dominant `k`-morphism `f : X ⟶ Y`, it intertwines
`f` with the morphism of models induced by the pullback of rational functions along `f`. -/
private lemma isoModel_hom_naturality {X Y : RegularProperCurveCat k} (f : X ⟶ Y) :
    f.hom ≫ (isoModel Y).hom.hom = (isoModel X).hom.hom ≫
      (modelHom (FunctionFieldCat.ofHom (f.hom.functionFieldAlgHom k) :
        functionFieldObj Y ⟶ functionFieldObj X)).hom := by
  have := twoChartModel.isProper (hF := (functionFieldObj Y).isFunctionField)
    (hx := modelGenerator_ne_zero _) (transcendental_modelGenerator _)
  refine Scheme.Hom.ext_of_functionFieldMap_eq (Spec (.of k)) ?_
  ext a
  obtain ⟨z, rfl⟩ := (modelEquiv (functionFieldObj Y)).symm.surjective a
  rw [Scheme.Hom.functionFieldMap_comp, Scheme.Hom.functionFieldMap_comp, CommRingCat.comp_apply,
    CommRingCat.comp_apply, functionFieldMap_modelHom]
  simp only [isoModel, isoMk_hom_hom, FunctionFieldCat.hom_ofHom,
    Scheme.Hom.functionFieldAlgHom_apply]
  exact (congrArg f.hom.functionFieldMap.hom (Scheme.functionFieldMap_isoTwoChartModel_hom
    Y.toScheme _ _ z)).trans (Scheme.functionFieldMap_isoTwoChartModel_hom X.toScheme _ _ _).symm

variable (k) in
/-- A regular proper curve is the model of its function field, naturally in the curve. -/
noncomputable def idIsoFunctionFieldFunctorCompTwoChartModelFunctor :
    𝟭 (RegularProperCurveCat k) ≅ functionFieldFunctor k ⋙ twoChartModelFunctor k :=
  NatIso.ofComponents isoModel fun f ↦ hom_ext (isoModel_hom_naturality f)

variable (k) in
/-- **The anti-equivalence between regular proper curves and algebraic function fields** over a
field `k`: the function-field functor `X ↦ k(X)` is an equivalence
`RegularProperCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ` with inverse the model functor
`F ↦ twoChartModel F`. -/
noncomputable def equivFunctionFieldCat : RegularProperCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ where
  functor := functionFieldFunctor k
  inverse := twoChartModelFunctor k
  unitIso := idIsoFunctionFieldFunctorCompTwoChartModelFunctor k
  counitIso := twoChartModelFunctorCompFunctionFieldFunctorIso k
  functor_unitIso_comp X := Quiver.Hom.unop_inj <| FunctionFieldCat.hom_ext <| AlgHom.ext fun z ↦
    -- Unfolding the functors, the unit and the counit, the left side is the pullback of rational
    -- functions along `X ≅ twoChartModel k(X)`, applied to the element of the function field of the
    -- model corresponding to `z`.
    (Scheme.Hom.functionFieldAlgHom_apply k _ _).trans
      (Scheme.functionFieldMap_isoTwoChartModel_hom X.toScheme _ _ z)

@[simp]
lemma equivFunctionFieldCat_functor :
    (equivFunctionFieldCat k).functor = functionFieldFunctor k :=
  (rfl)

@[simp]
lemma equivFunctionFieldCat_inverse :
    (equivFunctionFieldCat k).inverse = twoChartModelFunctor k :=
  (rfl)

instance : (functionFieldFunctor k).IsEquivalence :=
  (equivFunctionFieldCat k).isEquivalence_functor

instance : (twoChartModelFunctor k).IsEquivalence :=
  (equivFunctionFieldCat k).isEquivalence_inverse

end RegularProperCurveCat

end TauCeti.AlgebraicGeometry
