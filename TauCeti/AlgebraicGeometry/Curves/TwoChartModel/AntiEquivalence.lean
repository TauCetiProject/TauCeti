/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Category
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Classification
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.ProjectiveEmbedding

/-!
# Regular proper and projective curves are anti-equivalent to algebraic function fields

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

Every regular proper curve is projective
(`AlgebraicGeometry.Scheme.isProjectiveOver_of_isCurveOver`), so the regular projective curves, a
full subcategory of the regular proper curves, are all of them. The anti-equivalence therefore also
holds with regular projective curves on the geometric side, as in Hartshorne's Corollary I.6.12.

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
* `TauCeti.AlgebraicGeometry.RegularProjectiveCurveCat.equivRegularProperCurveCat`: regarding a
  regular projective curve as a regular proper curve is an equivalence of categories.
* `TauCeti.AlgebraicGeometry.RegularProjectiveCurveCat.equivFunctionFieldCat`: **the
  anti-equivalence** `RegularProjectiveCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ` between regular
  projective curves and algebraic function fields.

## Main results

* the instances `(functionFieldFunctor k).IsEquivalence`,
  `(twoChartModelFunctor k).IsEquivalence` and
  `(RegularProjectiveCurveCat.toRegularProperCurveCat k).IsEquivalence`.

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
noncomputable def modelGenerator (F : FunctionFieldCat k) : F :=
  F.isFunctionField.exists_transcendental.choose

/-- The function `modelGenerator F` is transcendental over `k`. -/
theorem transcendental_modelGenerator (F : FunctionFieldCat k) :
    Transcendental k (modelGenerator F) :=
  F.isFunctionField.exists_transcendental.choose_spec

/-- The function `modelGenerator F` is nonzero. -/
theorem modelGenerator_ne_zero (F : FunctionFieldCat k) : modelGenerator F ≠ 0 :=
  (transcendental_modelGenerator F).ne_zero

/-! The private abbreviations `modelObj` and `modelHom` below are the object and morphism parts
of `twoChartModelFunctor`, whose `obj` and `map` fields are the same terms, so the two agree by
`rfl`. The unit, the counit and their naturality proofs go through these abbreviations because
they are reducible: instance search sees the `k`-algebra and over-`k` instances of
`twoChartModel` through them, but does not unfold the fields of the functor. Being private, they
cannot appear in the exposed body of `twoChartModelFunctor` itself. -/

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
@[expose] noncomputable def twoChartModelFunctor :
    (FunctionFieldCat k)ᵒᵖ ⥤ RegularProperCurveCat k where
  obj F :=
    { toScheme := twoChartModel F.unop.isFunctionField (modelGenerator_ne_zero F.unop)
      isCurveOver := twoChartModel.isCurveOver (transcendental_modelGenerator F.unop)
      isDiscreteValuationRing_stalk :=
        twoChartModel.isDiscreteValuationRing_stalk (transcendental_modelGenerator F.unop) }
  map φ :=
    ⟨twoChartModel.homOfAlgHom _ _ (modelGenerator_ne_zero _) (modelGenerator_ne_zero _)
      (transcendental_modelGenerator _) (transcendental_modelGenerator _) φ.unop.hom⟩
  map_id F := by
    ext1
    exact twoChartModel.homOfAlgHom_id ..
  map_comp φ ψ := by
    ext1
    exact (twoChartModel.homOfAlgHom_comp ..).symm

/-- The model functor sends `F` to the two-chart model of `F` built from `modelGenerator F`. -/
@[simp]
lemma twoChartModelFunctor_obj_toScheme (F : (FunctionFieldCat k)ᵒᵖ) :
    ((twoChartModelFunctor k).obj F).toScheme =
      twoChartModel F.unop.isFunctionField (modelGenerator_ne_zero F.unop) :=
  (rfl)

/-- The model functor sends a `k`-embedding `φ` to the morphism of two-chart models induced
by `φ`. -/
lemma twoChartModelFunctor_map_hom {F G : (FunctionFieldCat k)ᵒᵖ} (φ : F ⟶ G) :
    ((twoChartModelFunctor k).map φ).hom =
      twoChartModel.homOfAlgHom G.unop.isFunctionField F.unop.isFunctionField
        (modelGenerator_ne_zero G.unop) (modelGenerator_ne_zero F.unop)
        (transcendental_modelGenerator G.unop) (transcendental_modelGenerator F.unop) φ.unop.hom :=
  (rfl)

/-- The pullback of rational functions along the morphism of models induced by `φ : G → F` is
`φ`, read through the identifications of the function fields of the models with `G` and `F`. -/
@[simp]
lemma functionFieldEquiv_functionFieldMap_twoChartModelFunctor_map
    {F G : (FunctionFieldCat k)ᵒᵖ} (φ : F ⟶ G) (z : G.unop) :
    twoChartModel.functionFieldEquiv (transcendental_modelGenerator F.unop)
      (((twoChartModelFunctor k).map φ).hom.functionFieldMap
        ((twoChartModel.functionFieldEquiv (transcendental_modelGenerator G.unop)).symm z)) =
      φ.unop.hom z :=
  twoChartModel.functionFieldEquiv_functionFieldMap_homOfAlgHom ..

/-- `functionFieldEquiv_functionFieldMap_twoChartModelFunctor_map`, stated for `modelHom`, the
reducible form in which instance search finds the instances needed to rewrite with it. -/
private lemma functionFieldMap_modelHom {F G : FunctionFieldCat k} (φ : F ⟶ G) (z : F) :
    (modelHom φ).hom.functionFieldMap ((modelEquiv F).symm z) = (modelEquiv G).symm (φ.hom z) :=
  (AlgEquiv.eq_symm_apply _).mpr
    (functionFieldEquiv_functionFieldMap_twoChartModelFunctor_map φ.op z)

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

/-- The component at `F` of the natural isomorphism
`twoChartModelFunctorCompFunctionFieldFunctorIso` is the identification of `F` with the function
field of its model. -/
@[simp]
lemma twoChartModelFunctorCompFunctionFieldFunctorIso_hom_app (F : (FunctionFieldCat k)ᵒᵖ) :
    (twoChartModelFunctorCompFunctionFieldFunctorIso k).hom.app F =
      (FunctionFieldCat.ofHom
        (twoChartModel.functionFieldEquiv (hx := modelGenerator_ne_zero F.unop)
          (transcendental_modelGenerator F.unop)).symm.toAlgHom :
        ((𝟭 (FunctionFieldCat k)ᵒᵖ).obj F).unop ⟶
          ((twoChartModelFunctor k ⋙ functionFieldFunctor k).obj F).unop).op :=
  (rfl)

/-- The inverse component at `F` of the natural isomorphism
`twoChartModelFunctorCompFunctionFieldFunctorIso` is the identification of the function field of
the model of `F` with `F`. -/
@[simp]
lemma twoChartModelFunctorCompFunctionFieldFunctorIso_inv_app (F : (FunctionFieldCat k)ᵒᵖ) :
    (twoChartModelFunctorCompFunctionFieldFunctorIso k).inv.app F =
      (FunctionFieldCat.ofHom
        (twoChartModel.functionFieldEquiv (hx := modelGenerator_ne_zero F.unop)
          (transcendental_modelGenerator F.unop)).toAlgHom :
        ((twoChartModelFunctor k ⋙ functionFieldFunctor k).obj F).unop ⟶
          ((𝟭 (FunctionFieldCat k)ᵒᵖ).obj F).unop).op :=
  (rfl)

/-- The function field of a regular proper curve, as an object of `FunctionFieldCat k`. This is
`((functionFieldFunctor k).obj X).unop` by `rfl`, in the reducible form that instance search needs
to find the over-`k` instances of the model of `X`. -/
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

/-- The component at `X` of the natural isomorphism
`idIsoFunctionFieldFunctorCompTwoChartModelFunctor` is the isomorphism of `X` with the two-chart
model of its function field. -/
@[simp]
lemma idIsoFunctionFieldFunctorCompTwoChartModelFunctor_hom_app_hom (X : RegularProperCurveCat k) :
    ((idIsoFunctionFieldFunctorCompTwoChartModelFunctor k).hom.app X).hom =
      (X.toScheme.isoTwoChartModel
        (modelGenerator_ne_zero (.of X.toScheme.functionField Scheme.IsCurveOver.isFunctionField))
        (transcendental_modelGenerator
          (.of X.toScheme.functionField Scheme.IsCurveOver.isFunctionField))).hom :=
  (rfl)

/-- The inverse component at `X` of the natural isomorphism
`idIsoFunctionFieldFunctorCompTwoChartModelFunctor` is the isomorphism of the two-chart model of
the function field of `X` with `X`. -/
@[simp]
lemma idIsoFunctionFieldFunctorCompTwoChartModelFunctor_inv_app_hom (X : RegularProperCurveCat k) :
    ((idIsoFunctionFieldFunctorCompTwoChartModelFunctor k).inv.app X).hom =
      (X.toScheme.isoTwoChartModel
        (modelGenerator_ne_zero (.of X.toScheme.functionField Scheme.IsCurveOver.isFunctionField))
        (transcendental_modelGenerator
          (.of X.toScheme.functionField Scheme.IsCurveOver.isFunctionField))).inv :=
  (rfl)

/-- The triangle law for the unit `idIsoFunctionFieldFunctorCompTwoChartModelFunctor` and the
counit `twoChartModelFunctorCompFunctionFieldFunctorIso`. -/
lemma functionFieldFunctor_map_unit_comp_counit (X : RegularProperCurveCat k) :
    (functionFieldFunctor k).map ((idIsoFunctionFieldFunctorCompTwoChartModelFunctor k).hom.app X) ≫
      (twoChartModelFunctorCompFunctionFieldFunctorIso k).hom.app ((functionFieldFunctor k).obj X) =
      𝟙 ((functionFieldFunctor k).obj X) :=
  Quiver.Hom.unop_inj <| FunctionFieldCat.hom_ext <| AlgHom.ext fun z ↦
    -- Unfolding the functors, the unit and the counit, the left side is the pullback of rational
    -- functions along `X ≅ twoChartModel k(X)`, applied to the element of the function field of the
    -- model corresponding to `z`.
    (Scheme.Hom.functionFieldAlgHom_apply k _ _).trans
      (Scheme.functionFieldMap_isoTwoChartModel_hom X.toScheme _ _ z)

variable (k) in
/-- **The anti-equivalence between regular proper curves and algebraic function fields** over a
field `k`: the function-field functor `X ↦ k(X)` is an equivalence
`RegularProperCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ` with inverse the model functor
`F ↦ twoChartModel F`. -/
@[expose] noncomputable def equivFunctionFieldCat :
    RegularProperCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ where
  functor := functionFieldFunctor k
  inverse := twoChartModelFunctor k
  unitIso := idIsoFunctionFieldFunctorCompTwoChartModelFunctor k
  counitIso := twoChartModelFunctorCompFunctionFieldFunctorIso k
  functor_unitIso_comp := functionFieldFunctor_map_unit_comp_counit

@[simp]
lemma equivFunctionFieldCat_functor :
    (equivFunctionFieldCat k).functor = functionFieldFunctor k :=
  (rfl)

@[simp]
lemma equivFunctionFieldCat_inverse :
    (equivFunctionFieldCat k).inverse = twoChartModelFunctor k :=
  (rfl)

@[simp]
lemma equivFunctionFieldCat_unitIso :
    (equivFunctionFieldCat k).unitIso = idIsoFunctionFieldFunctorCompTwoChartModelFunctor k :=
  (rfl)

@[simp]
lemma equivFunctionFieldCat_counitIso :
    (equivFunctionFieldCat k).counitIso = twoChartModelFunctorCompFunctionFieldFunctorIso k :=
  (rfl)

instance : (functionFieldFunctor k).IsEquivalence :=
  (equivFunctionFieldCat k).isEquivalence_functor

instance : (twoChartModelFunctor k).IsEquivalence :=
  (equivFunctionFieldCat k).isEquivalence_inverse

end RegularProperCurveCat

namespace RegularProjectiveCurveCat

variable {k : Type u} [Field k]

/-- A regular proper curve, as a regular projective curve: it is projective over `k` by
`AlgebraicGeometry.Scheme.isProjectiveOver_of_isCurveOver`. -/
@[expose] noncomputable def ofRegularProperCurveCat (X : RegularProperCurveCat k) :
    RegularProjectiveCurveCat k where
  toScheme := X.toScheme
  topologicalKrullDim_eq_one := Scheme.IsCurveOver.topologicalKrullDim_eq_one k

@[simp]
lemma ofRegularProperCurveCat_toScheme (X : RegularProperCurveCat k) :
    (ofRegularProperCurveCat X).toScheme = X.toScheme :=
  (rfl)

variable (k) in
/-- **Regular projective curves are regular proper curves**: regarding a regular projective curve
as a regular proper curve is an equivalence of categories, because every regular proper curve is
projective. -/
@[expose] noncomputable def equivRegularProperCurveCat :
    RegularProjectiveCurveCat k ≌ RegularProperCurveCat k where
  functor := toRegularProperCurveCat k
  inverse :=
    { obj := ofRegularProperCurveCat
      map f := InducedCategory.homMk f }
  -- Both round trips keep the underlying scheme and morphism, and the remaining fields are
  -- propositions or the same instances, so both composites are the identity functors up to
  -- structure eta.
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
lemma equivRegularProperCurveCat_functor :
    (equivRegularProperCurveCat k).functor = toRegularProperCurveCat k :=
  (rfl)

@[simp]
lemma equivRegularProperCurveCat_inverse_obj (X : RegularProperCurveCat k) :
    (equivRegularProperCurveCat k).inverse.obj X = ofRegularProperCurveCat X :=
  (rfl)

@[simp]
lemma equivRegularProperCurveCat_inverse_map_hom {X Y : RegularProperCurveCat k} (f : X ⟶ Y) :
    ((equivRegularProperCurveCat k).inverse.map f).hom = f :=
  (rfl)

@[simp]
lemma equivRegularProperCurveCat_unitIso : (equivRegularProperCurveCat k).unitIso = Iso.refl _ :=
  (rfl)

@[simp]
lemma equivRegularProperCurveCat_counitIso :
    (equivRegularProperCurveCat k).counitIso = Iso.refl _ :=
  (rfl)

instance : (toRegularProperCurveCat k).IsEquivalence :=
  (equivRegularProperCurveCat k).isEquivalence_functor

variable (k) in
/-- **The anti-equivalence between regular projective curves and algebraic function fields** over
a field `k`: the functor sending a regular projective curve `X` to its function field `k(X)` and a
dominant `k`-morphism to the pullback of rational functions along it is an equivalence
`RegularProjectiveCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ`. Its inverse sends a function field to its
two-chart model, the normalization of the projective line in it. -/
@[expose] noncomputable def equivFunctionFieldCat :
    RegularProjectiveCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ :=
  (equivRegularProperCurveCat k).trans (RegularProperCurveCat.equivFunctionFieldCat k)

/-- The anti-equivalence sends a regular projective curve to its function field. -/
@[simp]
lemma equivFunctionFieldCat_functor_obj (X : RegularProjectiveCurveCat k) :
    (equivFunctionFieldCat k).functor.obj X =
      op (.of X.toScheme.functionField Scheme.IsCurveOver.isFunctionField) :=
  (rfl)

/-- The anti-equivalence sends a dominant `k`-morphism to the pullback of rational functions
along it. -/
@[simp]
lemma equivFunctionFieldCat_functor_map_unop_hom {X Y : RegularProjectiveCurveCat k}
    (f : X ⟶ Y) :
    ((equivFunctionFieldCat k).functor.map f).unop.hom = f.hom.hom.functionFieldAlgHom k :=
  (rfl)

/-- The inverse of the anti-equivalence sends a function field `F` to the two-chart model of `F`
built from `modelGenerator F`. -/
@[simp]
lemma equivFunctionFieldCat_inverse_obj_toScheme (F : (FunctionFieldCat k)ᵒᵖ) :
    ((equivFunctionFieldCat k).inverse.obj F).toScheme =
      twoChartModel F.unop.isFunctionField
        (RegularProperCurveCat.modelGenerator_ne_zero F.unop) :=
  (rfl)

/-- The inverse of the anti-equivalence sends a `k`-embedding of function fields to the induced
dominant `k`-morphism of two-chart models. -/
@[simp]
lemma equivFunctionFieldCat_inverse_map_hom {F G : (FunctionFieldCat k)ᵒᵖ} (φ : F ⟶ G) :
    ((equivFunctionFieldCat k).inverse.map φ).hom =
      (RegularProperCurveCat.twoChartModelFunctor k).map φ :=
  (rfl)

/-- The unit of the anti-equivalence at `X` is the isomorphism of `X` with the two-chart model of
its function field. -/
@[simp]
lemma equivFunctionFieldCat_unitIso_hom_app_hom (X : RegularProjectiveCurveCat k) :
    ((equivFunctionFieldCat k).unitIso.hom.app X).hom =
      (RegularProperCurveCat.idIsoFunctionFieldFunctorCompTwoChartModelFunctor k).hom.app
        ((toRegularProperCurveCat k).obj X) := by
  dsimp only [equivFunctionFieldCat]
  rw [Equivalence.trans_unitIso, Iso.trans_hom, NatTrans.comp_app, InducedCategory.comp_hom]
  simp only [Functor.id_obj, Equivalence.trans_functor, Equivalence.trans_inverse, Functor.comp_obj,
    equivRegularProperCurveCat_unitIso, Iso.refl_hom, NatTrans.id_app,
    RegularProperCurveCat.equivFunctionFieldCat_unitIso, Functor.isoWhiskerRight_trans,
    Iso.trans_assoc, Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app, CategoryTheory.Functor.map_id,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.comp_id, Category.id_comp,
    equivRegularProperCurveCat_inverse_map_hom]
  exact Category.id_comp _

/-- The inverse of the unit of the anti-equivalence at `X` is the isomorphism of the two-chart
model of the function field of `X` with `X`. -/
@[simp]
lemma equivFunctionFieldCat_unitIso_inv_app_hom (X : RegularProjectiveCurveCat k) :
    ((equivFunctionFieldCat k).unitIso.inv.app X).hom =
      (RegularProperCurveCat.idIsoFunctionFieldFunctorCompTwoChartModelFunctor k).inv.app
        ((toRegularProperCurveCat k).obj X) := by
  dsimp only [equivFunctionFieldCat]
  rw [Equivalence.trans_unitIso, Iso.trans_inv, NatTrans.comp_app, InducedCategory.comp_hom]
  simp only [Equivalence.trans_functor, Equivalence.trans_inverse, Functor.comp_obj, Functor.id_obj,
    RegularProperCurveCat.equivFunctionFieldCat_unitIso, Functor.isoWhiskerRight_trans,
    Iso.trans_assoc, Iso.trans_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv, Category.assoc,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, CategoryTheory.Functor.map_id, Functor.rightUnitor_hom_app,
    Category.comp_id, Category.id_comp, equivRegularProperCurveCat_inverse_map_hom,
    equivRegularProperCurveCat_unitIso, Iso.refl_inv, NatTrans.id_app]
  exact Category.comp_id _

/-- The counit of the anti-equivalence at `F` identifies the function field of the two-chart model
of `F` with `F`. -/
@[simp]
lemma equivFunctionFieldCat_counitIso_hom_app (F : (FunctionFieldCat k)ᵒᵖ) :
    (equivFunctionFieldCat k).counitIso.hom.app F =
      (RegularProperCurveCat.twoChartModelFunctorCompFunctionFieldFunctorIso k).hom.app F := by
  dsimp only [equivFunctionFieldCat]
  rw [Equivalence.trans_counitIso, Iso.trans_hom, NatTrans.comp_app, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  -- The two sides have the same type only up to structure eta for the two-chart model, so `simp`
  -- cannot rewrite the goal; the remaining factors are identities, removed one at a time.
  refine (Category.id_comp _).trans ((congrArg (· ≫ _) ?_).trans (Category.id_comp _))
  refine (congrArg _ ?_).trans (CategoryTheory.Functor.map_id _ _)
  rfl

/-- The inverse of the counit of the anti-equivalence at `F` identifies `F` with the function
field of the two-chart model of `F`. -/
@[simp]
lemma equivFunctionFieldCat_counitIso_inv_app (F : (FunctionFieldCat k)ᵒᵖ) :
    (equivFunctionFieldCat k).counitIso.inv.app F =
      (RegularProperCurveCat.twoChartModelFunctorCompFunctionFieldFunctorIso k).inv.app F :=
  Iso.inv_ext (f := (equivFunctionFieldCat k).counitIso.app F) <|
    (congrArg (· ≫ _) (equivFunctionFieldCat_counitIso_hom_app F)).trans <|
      (RegularProperCurveCat.twoChartModelFunctorCompFunctionFieldFunctorIso k).hom_inv_id_app F

end RegularProjectiveCurveCat

end TauCeti.AlgebraicGeometry
