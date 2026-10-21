/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.AlgHom
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Map
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Proper

/-!
# Morphisms of two-chart models are embeddings of function fields

Let `F / k` and `F' / k` be algebraic function fields, and `x ∈ F`, `x' ∈ F'` transcendental over
`k`. The two-chart models `X = twoChartModel hF hx` and `X' = twoChartModel hF' hx'` are regular
proper curves over `k` with function fields `F` and `F'`. This file proves that the dominant
`k`-morphisms `X' ⟶ X` are exactly the `k`-embeddings `F → F'`, with no compatibility between `x`
and `x'` required.

Every `k`-embedding `φ : F →ₐ[k] F'` gives a `k`-morphism `Spec F' ⟶ X` from the generic point of
`X'`, through the generic point of `X`. The local rings of `X'` are valuation rings
(`TauCeti.AlgebraicGeometry.twoChartModel.valuationRing_stalk`) and `X` is proper over `k`, so this
morphism extends uniquely to a `k`-morphism `homOfAlgHom φ : X' ⟶ X`
(`AlgebraicGeometry.Scheme.homOfFunctionFieldAlgHom`). Its pullback of rational functions is `φ`,
and since `X` is separated, a dominant `k`-morphism is determined by its pullback of rational
functions: the construction is a bijection, and it is functorial. In particular a `k`-isomorphism
`F ≃ F'` gives an isomorphism of the models, so **the two-chart model does not depend on the
choice of the transcendental function**: `twoChartModel hF hx ≅ twoChartModel hF hy` for any two
transcendental `x, y ∈ F`. When the embedding carries `x` to `x'`, the morphism is the one glued
from the chart maps (`TauCeti.AlgebraicGeometry.twoChartModel.map`).

This is the morphism half of the anti-equivalence between function fields of one variable and
regular projective curves.

## Main definitions

* `TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom`: the morphism of two-chart models induced
  by a `k`-embedding of function fields.
* `TauCeti.AlgebraicGeometry.twoChartModel.isoOfAlgEquiv`: the isomorphism of two-chart models
  induced by a `k`-isomorphism of function fields.

## Main results

* the instances `(homOfAlgHom …).IsOver (Spec k)` and `IsDominant (homOfAlgHom …)`.
* `TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv_functionFieldMap_homOfAlgHom`: the
  pullback of rational functions along `homOfAlgHom φ` is `φ`.
* `TauCeti.AlgebraicGeometry.twoChartModel.eq_homOfAlgHom_iff`: a dominant `k`-morphism is
  `homOfAlgHom φ` exactly when its pullback of rational functions is `φ`.
* `TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom_id` and
  `TauCeti.AlgebraicGeometry.twoChartModel.homOfAlgHom_comp`: functoriality.
* `TauCeti.AlgebraicGeometry.twoChartModel.map_eq_homOfAlgHom`: the morphism glued from the chart
  maps is `homOfAlgHom` of the algebra map.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition I.6.8 and
  Corollary I.6.12.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F F' : Type u} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  (hF : IsFunctionField k F) (hF' : IsFunctionField k F') {x : F} (hx : x ≠ 0) {x' : F'}
  (hx' : x' ≠ 0) {hxt : Transcendental k x} {hx't : Transcendental k x'}

variable {hF hF' hx hx'} in
/-- The `k`-algebra map `k(X) → k(X')` of function fields corresponding to `φ : F →ₐ[k] F'`
under the identifications `k(X) ≃ F` and `k(X') ≃ F'`. -/
private noncomputable def functionFieldAlgHom (hxt : Transcendental k x)
    (hx't : Transcendental k x') (φ : F →ₐ[k] F') :
    (twoChartModel hF hx).functionField →ₐ[k] (twoChartModel hF' hx').functionField :=
  ((functionFieldEquiv hx't).symm.toAlgHom.comp φ).comp (functionFieldEquiv hxt).toAlgHom

/-- **The morphism of two-chart models induced by a `k`-embedding `φ : F →ₐ[k] F'`** of function
fields, for transcendental `x ∈ F` and `x' ∈ F'`: the unique dominant `k`-morphism
`twoChartModel hF' hx' ⟶ twoChartModel hF hx` whose pullback of rational functions is `φ`
(`eq_homOfAlgHom_iff`). No relation between `x` and `x'` is required. -/
noncomputable def homOfAlgHom (hxt : Transcendental k x) (hx't : Transcendental k x')
    (φ : F →ₐ[k] F') : twoChartModel hF' hx' ⟶ twoChartModel hF hx :=
  have := isProper (hF := hF) (hx := hx) hxt
  Scheme.homOfFunctionFieldAlgHom (valuationRing_stalk hx't) (functionFieldAlgHom hxt hx't φ)

variable (φ : F →ₐ[k] F')

/-- `homOfAlgHom φ` is a morphism over `k`. -/
instance : (homOfAlgHom hF hF' hx hx' hxt hx't φ).IsOver (Spec (.of k)) := by
  have := isProper (hF := hF) (hx := hx) hxt
  rw [homOfAlgHom]
  infer_instance

/-- `homOfAlgHom φ` is dominant: it sends the generic point to the generic point. -/
instance : IsDominant (homOfAlgHom hF hF' hx hx' hxt hx't φ) := by
  have := isProper (hF := hF) (hx := hx) hxt
  rw [homOfAlgHom]
  infer_instance

/-- The pullback of rational functions along `homOfAlgHom φ` is the map of function fields given by
`φ`. -/
private theorem functionFieldMap_homOfAlgHom :
    (homOfAlgHom hF hF' hx hx' hxt hx't φ).functionFieldMap =
      CommRingCat.ofHom (functionFieldAlgHom hxt hx't φ).toRingHom := by
  have := isProper (hF := hF) (hx := hx) hxt
  exact Scheme.functionFieldMap_homOfFunctionFieldAlgHom ..

/-- **The pullback of rational functions along `homOfAlgHom φ` is `φ`**: under the identifications
`k(X) ≃ F` and `k(X') ≃ F'` of the function fields of the two models, the pullback along
`homOfAlgHom φ : X' ⟶ X` is `φ`. -/
@[simp]
theorem functionFieldEquiv_functionFieldMap_homOfAlgHom (z : F) :
    functionFieldEquiv hx't ((homOfAlgHom hF hF' hx hx' hxt hx't φ).functionFieldMap
      ((functionFieldEquiv hxt).symm z)) = φ z := by
  rw [functionFieldMap_homOfAlgHom]
  simp [functionFieldAlgHom]

/-- **A dominant morphism of two-chart models is determined by its pullback of rational
functions**: a dominant `k`-morphism `f : X' ⟶ X` is `homOfAlgHom φ` exactly when, under the
identifications `k(X) ≃ F` and `k(X') ≃ F'`, its pullback of rational functions is `φ`. -/
theorem eq_homOfAlgHom_iff (f : twoChartModel hF' hx' ⟶ twoChartModel hF hx)
    [f.IsOver (Spec (.of k))] [IsDominant f] :
    f = homOfAlgHom hF hF' hx hx' hxt hx't φ ↔
      ∀ z, functionFieldEquiv hx't (f.functionFieldMap ((functionFieldEquiv hxt).symm z)) =
        φ z := by
  have := isProper (hF := hF) (hx := hx) hxt
  rw [homOfAlgHom, Scheme.eq_homOfFunctionFieldAlgHom_iff]
  refine ⟨fun h z ↦ by simp [h, functionFieldAlgHom], fun h a ↦ ?_⟩
  obtain ⟨z, rfl⟩ := (functionFieldEquiv hxt).symm.surjective a
  refine (functionFieldEquiv hx't).injective ?_
  simp [h, functionFieldAlgHom]

/-! ### Functoriality -/

variable {hF hx} in
/-- The identity of `F` induces the identity of `k(X)`. -/
private theorem functionFieldAlgHom_id :
    functionFieldAlgHom (hF := hF) (hF' := hF) (hx := hx) (hx' := hx) hxt hxt (AlgHom.id k F) =
      AlgHom.id k _ := by
  ext a
  simp [functionFieldAlgHom]

/-- The identity of `F` induces the identity of `twoChartModel hF hx`. -/
@[simp]
theorem homOfAlgHom_id : homOfAlgHom hF hF hx hx hxt hxt (AlgHom.id k F) = 𝟙 _ := by
  have := isProper (hF := hF) (hx := hx) hxt
  rw [homOfAlgHom, functionFieldAlgHom_id, Scheme.homOfFunctionFieldAlgHom_id]

variable {F'' : Type u} [Field F''] [Algebra k F''] (hF'' : IsFunctionField k F'') {x'' : F''}
  (hx'' : x'' ≠ 0) {hx''t : Transcendental k x''}

variable {hF hF' hF'' hx hx' hx''} in
/-- `k`-embeddings `F → F' → F''` induce the composite maps of function fields. -/
private theorem functionFieldAlgHom_comp (φ' : F' →ₐ[k] F'') :
    (functionFieldAlgHom (hF := hF') (hF' := hF'') (hx := hx') (hx' := hx'') hx't hx''t φ').comp
        (functionFieldAlgHom (hF := hF) (hF' := hF') (hx := hx) (hx' := hx') hxt hx't φ) =
      functionFieldAlgHom hxt hx''t (φ'.comp φ) := by
  ext a
  simp [functionFieldAlgHom]

/-- `k`-embeddings `F → F' → F''` induce the composite of the morphisms of two-chart models. -/
@[reassoc]
theorem homOfAlgHom_comp (φ' : F' →ₐ[k] F'') :
    homOfAlgHom hF' hF'' hx' hx'' hx't hx''t φ' ≫ homOfAlgHom hF hF' hx hx' hxt hx't φ =
      homOfAlgHom hF hF'' hx hx'' hxt hx''t (φ'.comp φ) := by
  have := isProper (hF := hF) (hx := hx) hxt
  have := isProper (hF := hF') (hx := hx') hx't
  rw [homOfAlgHom, homOfAlgHom, homOfAlgHom, Scheme.homOfFunctionFieldAlgHom_comp,
    functionFieldAlgHom_comp]

/-- **The isomorphism of two-chart models induced by a `k`-isomorphism `e : F ≃ₐ[k] F'`** of
function fields, for transcendental `x ∈ F` and `x' ∈ F'`. For `F' = F` and `e` the identity, this
says that the two-chart model does not depend on the choice of the transcendental function. -/
noncomputable def isoOfAlgEquiv (e : F ≃ₐ[k] F') :
    twoChartModel hF' hx' ≅ twoChartModel hF hx :=
  have := isProper (hF := hF) (hx := hx) hxt
  have := isProper (hF := hF') (hx := hx') hx't
  Scheme.isoOfFunctionFieldAlgEquiv (valuationRing_stalk hx't) (valuationRing_stalk hxt)
    (((functionFieldEquiv hxt).trans e).trans (functionFieldEquiv hx't).symm)

variable {hF hF' hx hx'} in
/-- For a `k`-isomorphism `e`, the map of function fields is the composite of the
identifications `k(X) ≃ F` and `k(X') ≃ F'` with `e`. -/
private theorem functionFieldAlgHom_algEquiv (e : F ≃ₐ[k] F') :
    functionFieldAlgHom (hF := hF) (hF' := hF') (hx := hx) (hx' := hx') hxt hx't e =
      (((functionFieldEquiv hxt).trans e).trans (functionFieldEquiv hx't).symm).toAlgHom := by
  ext a
  simp [functionFieldAlgHom]

variable {hF hF' hx hx'} in
/-- For a `k`-isomorphism `e`, the map of function fields given by `e.symm` is the inverse of the
one given by `e`. -/
private theorem functionFieldAlgHom_algEquiv_symm (e : F ≃ₐ[k] F') :
    functionFieldAlgHom (hF := hF') (hF' := hF) (hx := hx') (hx' := hx) hx't hxt e.symm =
      (((functionFieldEquiv hxt).trans e).trans (functionFieldEquiv hx't).symm).symm.toAlgHom := by
  ext a
  simp [functionFieldAlgHom]

/-- The forward morphism of `isoOfAlgEquiv e` is the morphism induced by `e`. -/
@[simp]
theorem isoOfAlgEquiv_hom (e : F ≃ₐ[k] F') :
    (isoOfAlgEquiv hF hF' hx hx' e (hxt := hxt) (hx't := hx't)).hom =
      homOfAlgHom hF hF' hx hx' hxt hx't e := by
  have := isProper (hF := hF) (hx := hx) hxt
  have := isProper (hF := hF') (hx := hx') hx't
  rw [isoOfAlgEquiv, Scheme.isoOfFunctionFieldAlgEquiv_hom, homOfAlgHom,
    functionFieldAlgHom_algEquiv]

/-- The inverse morphism of `isoOfAlgEquiv e` is the morphism induced by `e.symm`. -/
@[simp]
theorem isoOfAlgEquiv_inv (e : F ≃ₐ[k] F') :
    (isoOfAlgEquiv hF hF' hx hx' e (hxt := hxt) (hx't := hx't)).inv =
      homOfAlgHom hF' hF hx' hx hx't hxt e.symm := by
  have := isProper (hF := hF) (hx := hx) hxt
  have := isProper (hF := hF') (hx := hx') hx't
  rw [isoOfAlgEquiv, Scheme.isoOfFunctionFieldAlgEquiv_inv, homOfAlgHom,
    functionFieldAlgHom_algEquiv_symm]

/-! ### Comparison with the morphism glued from the chart maps -/

/-- **The morphism glued from the chart maps is `homOfAlgHom` of the algebra map**: for an integral
extension `F' / F` carrying `x` to `x'`, the morphism `map` of two-chart models is the morphism
induced by the `k`-embedding `F → F'`. -/
theorem map_eq_homOfAlgHom [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    (h : algebraMap F F' x = x') :
    map hF hF' hx hx' h = homOfAlgHom hF hF' hx hx' hxt hx't (IsScalarTower.toAlgHom k F F') :=
  (eq_homOfAlgHom_iff hF hF' hx hx' _ _).mpr fun z ↦
    functionFieldEquiv_functionFieldMap_map hF hF' hx hx' h hxt z

end TauCeti.AlgebraicGeometry.twoChartModel
