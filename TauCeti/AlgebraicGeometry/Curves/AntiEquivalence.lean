/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Classification
public import TauCeti.AlgebraicGeometry.Curves.Category

/-!
# Regular proper curves and their function fields

Let `k` be a field. This file uses the category `RegularProperCurveCat k` of regular proper curves
over `k`: integral schemes, proper and of dimension one over `k`, whose local rings at the
codimension-one points are discrete valuation rings, with the dominant `k`-morphisms as morphisms.
It proves that **taking the function field is an anti-equivalence**

`RegularProperCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ`

onto the category of algebraic function fields of one variable over `k` with `k`-embeddings.

* The functor sends a curve `X` to its function field `k(X)` and a dominant `k`-morphism
  `f : X ⟶ Y` to the pullback of rational functions `f^* : k(Y) → k(X)`.
* It is faithful: a dominant morphism into a separated scheme is determined at the generic point.
* It is full: the local rings of `X` are valuation rings and `Y` is proper over `k`, so for a
  `k`-embedding `φ : k(Y) → k(X)` the morphism `Spec k(X) ⟶ Y` through `Spec φ` and the generic
  point of `Y` extends to a `k`-morphism `X ⟶ Y` (`RegularProperCurveCat.homOfAlgHom`), whose
  pullback of rational functions is `φ`.
* It is essentially surjective: a function field `F` is the function field of the normalization of
  the projective line in `F`, glued from the normalizations of `k[x]` and `k[x⁻¹]` in `F` for a
  transcendental `x ∈ F` (`RegularProperCurveCat.twoChartModel`).

Every regular proper curve is moreover isomorphic to the two-chart model of its own function field
(`AlgebraicGeometry.Scheme.isoTwoChartModel`), which is the object half of the equivalence made
explicit.

## Main definitions

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat k`: regular proper curves over `k` with
  dominant `k`-morphisms.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.functionFieldFunctor`: the function field functor
  `RegularProperCurveCat k ⥤ (FunctionFieldCat k)ᵒᵖ`.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.homOfAlgHom`: the morphism of curves induced by a
  `k`-embedding of function fields.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.twoChartModel`: the two-chart model of a function
  field, as a regular proper curve.
* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.functionFieldEquivalence`: the anti-equivalence
  `RegularProperCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ`.

## Main results

* `TauCeti.AlgebraicGeometry.RegularProperCurveCat.functionFieldAlgHom_homOfAlgHom` and
  `TauCeti.AlgebraicGeometry.RegularProperCurveCat.homOfAlgHom_functionFieldAlgHom`: dominant
  `k`-morphisms `X ⟶ Y` correspond bijectively to `k`-embeddings `k(Y) → k(X)`.
* the instance `(RegularProperCurveCat.functionFieldFunctor k).IsEquivalence`.

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

namespace RegularProperCurveCat

variable {k}
variable {X Y Z : RegularProperCurveCat k}

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
  ext x
  rw [Scheme.Hom.functionFieldAlgHom_apply]
  exact congr($h x)

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
    {x : F} (hxt : Transcendental k x) : RegularProperCurveCat k where
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
      ⟨(FunctionFieldCat.isoMk
        (F := F.unop) (G := ((functionFieldFunctor k).obj (twoChartModel _ hxt)).unop)
        (AlgebraicGeometry.twoChartModel.functionFieldEquiv hxt).symm).op⟩⟩

instance : (functionFieldFunctor k).IsEquivalence where

variable (k) in
/-- **The anti-equivalence between regular proper curves and function fields**: taking the function
field is an equivalence `RegularProperCurveCat k ≌ (FunctionFieldCat k)ᵒᵖ` from regular proper
curves over `k` with dominant `k`-morphisms to algebraic function fields of one variable over `k`
with `k`-embeddings, reversing the direction of morphisms. -/
noncomputable def functionFieldEquivalence :
    RegularProperCurveCat k ≌ (FunctionFieldCat.{u} k)ᵒᵖ :=
  (functionFieldFunctor k).asEquivalence

@[simp]
theorem functionFieldEquivalence_functor :
    (functionFieldEquivalence k).functor = functionFieldFunctor k :=
  (rfl)

end RegularProperCurveCat

end TauCeti.AlgebraicGeometry
