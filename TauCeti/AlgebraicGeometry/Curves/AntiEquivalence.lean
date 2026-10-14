/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Classification
public import TauCeti.FieldTheory.FunctionField.Category

/-!
# Regular proper curves and their function fields

Let `k` be a field. This file defines the category `RegularProperCurve k` of regular proper curves
over `k`: integral schemes, proper and of dimension one over `k`, whose local rings at the
codimension-one points are discrete valuation rings, with the dominant `k`-morphisms as morphisms.
It proves that **taking the function field is an anti-equivalence**

`RegularProperCurve k ≌ (FunctionFieldCat k)ᵒᵖ`

onto the category of algebraic function fields of one variable over `k` with `k`-embeddings.

* The functor sends a curve `X` to its function field `k(X)` and a dominant `k`-morphism
  `f : X ⟶ Y` to the pullback of rational functions `f^* : k(Y) → k(X)`.
* It is faithful: a dominant morphism into a separated scheme is determined at the generic point.
* It is full: the local rings of `X` are valuation rings and `Y` is proper over `k`, so for a
  `k`-embedding `φ : k(Y) → k(X)` the morphism `Spec k(X) ⟶ Y` through `Spec φ` and the generic
  point of `Y` extends to a `k`-morphism `X ⟶ Y` (`RegularProperCurve.homOfAlgHom`), whose pullback
  of rational functions is `φ`.
* It is essentially surjective: a function field `F` is the function field of the normalization of
  the projective line in `F`, glued from the normalizations of `k[x]` and `k[x⁻¹]` in `F` for a
  transcendental `x ∈ F` (`RegularProperCurve.twoChartModel`).

Every regular proper curve is moreover isomorphic to the two-chart model of its own function field
(`AlgebraicGeometry.Scheme.isoTwoChartModel`), which is the object half of the equivalence made
explicit.

## Main definitions

* `TauCeti.AlgebraicGeometry.RegularProperCurve k`: the category of regular proper curves over `k`
  with dominant `k`-morphisms.
* `TauCeti.AlgebraicGeometry.RegularProperCurve.functionFieldFunctor`: the function field functor
  `RegularProperCurve k ⥤ (FunctionFieldCat k)ᵒᵖ`.
* `TauCeti.AlgebraicGeometry.RegularProperCurve.homOfAlgHom`: the morphism of curves induced by a
  `k`-embedding of function fields.
* `TauCeti.AlgebraicGeometry.RegularProperCurve.twoChartModel`: the two-chart model of a function
  field, as a regular proper curve.
* `TauCeti.AlgebraicGeometry.RegularProperCurve.functionFieldEquivalence`: **the anti-equivalence**
  `RegularProperCurve k ≌ (FunctionFieldCat k)ᵒᵖ`.

## Main results

* `TauCeti.AlgebraicGeometry.RegularProperCurve.functionFieldAlgHom_homOfAlgHom` and
  `TauCeti.AlgebraicGeometry.RegularProperCurve.homOfAlgHom_functionFieldAlgHom`: dominant
  `k`-morphisms `X ⟶ Y` correspond bijectively to `k`-embeddings `k(Y) → k(X)`.
* the instance `(RegularProperCurve.functionFieldFunctor k).IsEquivalence`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Corollary I.6.12 (over an
  algebraically closed field).
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford Graduate Texts in Mathematics 6,
  Oxford University Press, 2002, Section 7.3 (over an arbitrary field).
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

public section

open CategoryTheory Opposite _root_.AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

variable (k : Type u) [Field k]

/-- **A regular proper curve over `k`**: an integral scheme, proper and of dimension one over `k`
(`AlgebraicGeometry.Scheme.IsCurveOver`), whose local rings at the codimension-one points are
discrete valuation rings. The morphisms of the category `RegularProperCurve k` are the dominant
`k`-morphisms. -/
structure RegularProperCurve where
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  [over : toScheme.Over (Spec (.of k))]
  [isCurveOver : toScheme.IsCurveOver k]
  [isDiscreteValuationRing_stalk : ∀ y : CodimensionOnePoint toScheme,
    IsDiscreteValuationRing (toScheme.presheaf.stalk (y : toScheme))]

namespace RegularProperCurve

attribute [instance] over isCurveOver isDiscreteValuationRing_stalk

variable {k}

/-- The type of morphisms in `RegularProperCurve k`: the dominant morphisms of schemes over `k`. -/
@[ext]
structure Hom (X Y : RegularProperCurve k) where
  mk ::
  /-- The underlying morphism of schemes. -/
  hom : X.toScheme ⟶ Y.toScheme
  [isOver : hom.IsOver (Spec (.of k))]
  [isDominant : IsDominant hom]

attribute [instance] Hom.isOver Hom.isDominant

instance : Category (RegularProperCurve k) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 X.toScheme⟩
  comp f g := ⟨f.hom ≫ g.hom⟩

variable {X Y Z : RegularProperCurve k}

@[simp]
theorem hom_id : Hom.hom (𝟙 X) = 𝟙 X.toScheme :=
  (rfl)

@[simp]
theorem hom_comp (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  (rfl)

@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-! ### The function field functor -/

/-- The function field `k(X)` of a regular proper curve `X`, as an object of
`FunctionFieldCat k`. -/
@[expose] noncomputable def functionField (X : RegularProperCurve k) : FunctionFieldCat.{u, u} k :=
  .of X.toScheme.functionField Scheme.IsCurveOver.isFunctionField

@[simp]
theorem coe_functionField (X : RegularProperCurve k) :
    (X.functionField : Type u) = X.toScheme.functionField :=
  (rfl)

variable (k) in
/-- **The function field functor** `RegularProperCurve k ⥤ (FunctionFieldCat k)ᵒᵖ`: a curve `X`
goes to its function field `k(X)`, and a dominant `k`-morphism `f : X ⟶ Y` to the pullback of
rational functions `f^* : k(Y) → k(X)`. It is an equivalence
(`RegularProperCurve.functionFieldEquivalence`). -/
@[expose] noncomputable def functionFieldFunctor :
    RegularProperCurve k ⥤ (FunctionFieldCat.{u, u} k)ᵒᵖ where
  obj X := op X.functionField
  map {X Y} f := (FunctionFieldCat.ofHom (F := Y.functionField) (F' := X.functionField)
    (f.hom.functionFieldAlgHom k)).op
  map_id X := Quiver.Hom.unop_inj (FunctionFieldCat.hom_ext
    (Scheme.Hom.functionFieldAlgHom_id k (Y := X.toScheme)))
  map_comp f g := Quiver.Hom.unop_inj (FunctionFieldCat.hom_ext
    (Scheme.Hom.functionFieldAlgHom_comp k f.hom g.hom))

@[simp]
theorem functionFieldFunctor_obj (X : RegularProperCurve k) :
    (functionFieldFunctor k).obj X = op X.functionField :=
  (rfl)

@[simp]
theorem hom_unop_functionFieldFunctor_map (f : X ⟶ Y) :
    ((functionFieldFunctor k).map f).unop.hom = f.hom.functionFieldAlgHom k :=
  (rfl)

/-! ### Morphisms from embeddings of function fields -/

/-- **The morphism of regular proper curves induced by a `k`-embedding** `φ : k(Y) → k(X)` of
function fields: the unique dominant `k`-morphism `X ⟶ Y` whose pullback of rational functions is
`φ` (`functionFieldAlgHom_homOfAlgHom`, `homOfAlgHom_functionFieldAlgHom`). -/
noncomputable def homOfAlgHom (φ : Y.toScheme.functionField →ₐ[k] X.toScheme.functionField) :
    X ⟶ Y :=
  haveI hX := Scheme.IsCurveOver.valuationRing_stalk k X.toScheme
  haveI hφ := Scheme.specMap_comp_fromSpecStalk_genericPoint_comp_over k
    (CommRingCat.ofHom φ.toRingHom) φ.commutes
  { hom := Scheme.homOfFunctionField hX _ hφ
    isOver := Scheme.isOver_homOfFunctionField hX _ hφ
    isDominant := Scheme.Hom.isDominant_of_SpecMap_fromSpecStalk _ _
      (Scheme.fromSpecStalk_homOfFunctionField hX _ hφ).symm }

/-- **The pullback of rational functions along `homOfAlgHom φ` is `φ`.** -/
@[simp]
theorem functionFieldAlgHom_homOfAlgHom
    (φ : Y.toScheme.functionField →ₐ[k] X.toScheme.functionField) :
    (homOfAlgHom φ).hom.functionFieldAlgHom k = φ := by
  have hX := Scheme.IsCurveOver.valuationRing_stalk k X.toScheme
  have h := ((Scheme.Hom.eq_functionFieldMap_iff (homOfAlgHom φ).hom
    (CommRingCat.ofHom φ.toRingHom)).mpr
    (Scheme.fromSpecStalk_homOfFunctionField hX _ _).symm).symm
  refine AlgHom.toRingHom_injective ?_
  rw [Scheme.Hom.coe_functionFieldAlgHom, h]
  -- `rw [CommRingCat.hom_ofHom]` fails here: the ring structure of the field `k(X)` is only
  -- defeq to that of the `CommRingCat` object `k(X)` at default transparency, so the lemma is
  -- applied with `exact`.
  exact CommRingCat.hom_ofHom _

/-- **A dominant `k`-morphism is induced by its pullback of rational functions**: `f : X ⟶ Y` is
`homOfAlgHom` of `f^* : k(Y) → k(X)`. -/
@[simp]
theorem homOfAlgHom_functionFieldAlgHom (f : X ⟶ Y) :
    homOfAlgHom (f.hom.functionFieldAlgHom k) = f := by
  refine hom_ext (Scheme.Hom.ext_of_functionFieldMap_eq (Spec (.of k)) ?_)
  ext z
  have h := DFunLike.congr_fun (functionFieldAlgHom_homOfAlgHom (f.hom.functionFieldAlgHom k)) z
  rwa [Scheme.Hom.functionFieldAlgHom_apply, Scheme.Hom.functionFieldAlgHom_apply] at h

/-- A dominant `k`-morphism of regular proper curves is determined by its pullback of rational
functions. -/
theorem functionFieldAlgHom_injective :
    Function.Injective fun f : X ⟶ Y ↦ f.hom.functionFieldAlgHom k := fun f g h ↦ by
  rw [← homOfAlgHom_functionFieldAlgHom f, ← homOfAlgHom_functionFieldAlgHom g]
  exact congrArg homOfAlgHom h

instance : (functionFieldFunctor k).Faithful where
  map_injective h := functionFieldAlgHom_injective congr(($h).unop.hom)

instance : (functionFieldFunctor k).Full where
  map_surjective φ :=
    ⟨homOfAlgHom φ.unop.hom, Quiver.Hom.unop_inj
      (FunctionFieldCat.hom_ext (functionFieldAlgHom_homOfAlgHom φ.unop.hom))⟩

/-! ### The two-chart model and essential surjectivity -/

/-- **The two-chart model of a function field** `F / k`, glued from the normalizations of `k[x]` and
`k[x⁻¹]` in `F` for `x ∈ F` transcendental over `k`, as a regular proper curve. Its function field
is `F` (`TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv`). -/
noncomputable def twoChartModel {F : Type u} [Field F] [Algebra k F] (hF : IsFunctionField k F)
    {x : F} (hxt : Transcendental k x) : RegularProperCurve k where
  toScheme := AlgebraicGeometry.twoChartModel hF hxt.ne_zero
  isCurveOver := twoChartModel.isCurveOver hxt
  isDiscreteValuationRing_stalk := twoChartModel.isDiscreteValuationRing_stalk hxt

@[simp]
theorem toScheme_twoChartModel {F : Type u} [Field F] [Algebra k F] (hF : IsFunctionField k F)
    {x : F} (hxt : Transcendental k x) :
    (twoChartModel hF hxt).toScheme = AlgebraicGeometry.twoChartModel hF hxt.ne_zero :=
  (rfl)

instance : (functionFieldFunctor k).EssSurj where
  mem_essImage F := by
    obtain ⟨x, hxt⟩ := F.unop.isFunctionField.exists_transcendental
    exact ⟨twoChartModel F.unop.isFunctionField hxt,
      ⟨(FunctionFieldCat.isoMk (F := F.unop) (F' := (twoChartModel _ hxt).functionField)
        (AlgebraicGeometry.twoChartModel.functionFieldEquiv hxt).symm).op⟩⟩

instance : (functionFieldFunctor k).IsEquivalence where

variable (k) in
/-- **The anti-equivalence between regular proper curves and function fields**: taking the function
field is an equivalence `RegularProperCurve k ≌ (FunctionFieldCat k)ᵒᵖ` from regular proper
curves over `k` with dominant `k`-morphisms to algebraic function fields of one variable over `k`
with `k`-embeddings, reversing the direction of morphisms. -/
noncomputable def functionFieldEquivalence :
    RegularProperCurve k ≌ (FunctionFieldCat.{u, u} k)ᵒᵖ :=
  (functionFieldFunctor k).asEquivalence

@[simp]
theorem functionFieldEquivalence_functor :
    (functionFieldEquivalence k).functor = functionFieldFunctor k :=
  (rfl)

end RegularProperCurve

end TauCeti.AlgebraicGeometry
