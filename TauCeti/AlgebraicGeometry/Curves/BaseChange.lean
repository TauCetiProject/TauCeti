/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Geometrically.FunctionField
public import TauCeti.AlgebraicGeometry.RationalPoint.BaseChange

/-!
# Base change of proper curves over a field

This file proves base-change stability for `AlgebraicGeometry.Scheme.IsCurveOver` and constructs
the closed-fibre bijection over an algebraically closed base field:

* `AlgebraicGeometry.Scheme.IsCurveOver.of_isPullback`: base change of a geometrically integral
  curve along an arbitrary field extension `L / k` is a curve over `L`.
* `AlgebraicGeometry.Scheme.Hom.curveFiberEquivOfIsAlgClosed`,
  `AlgebraicGeometry.Scheme.Hom.curveFiberEquivOfIsAlgClosed_coe`: non-generic fibre bijection
  along `gX` for a dominant morphism of curves over an algebraically closed field `k`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **Base change of a geometrically integral curve.** If `X` is a geometrically integral curve
over `k`, its pullback `X'` along an arbitrary field extension `L / k` (algebraic or
transcendental, separable or not) is a curve over `L`. -/
theorem IsCurveOver.of_isPullback {k L : Type u} [Field k] [Field L] [Algebra k L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of k))] [X'.Over (Spec (.of L))]
    [X.IsCurveOver k] [GeometricallyIntegral (X ↘ Spec (.of k))] {gX : X' ⟶ X}
    (HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    X'.IsCurveOver L := by
  have hInt : IsIntegral X' := GeometricallyIntegral.geometrically_isIntegral _ _ _ HX
  have hProp : IsProper (X' ↘ Spec (.of L)) := MorphismProperty.of_isPullback HX inferInstance
  have hDom : IsDominant gX := TauCeti.isDominant_of_isPullback_spec HX
  let _ : Algebra X.functionField X'.functionField := gX.functionFieldMap.hom.toAlgebra
  let _ : Algebra k X'.functionField :=
    ((algebraMap L X'.functionField).comp (algebraMap k L)).toAlgebra
  have : IsScalarTower k L X'.functionField := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k X.functionField X'.functionField := .of_algebraMap_eq fun c ↦
    (TauCeti.AlgebraicGeometry.functionFieldMap_baseChange_algebraMap HX c).symm
  exact isCurveOver_iff.mpr ⟨hInt, hProp,
    (TauCeti.AlgebraicGeometry.isFunctionField_functionField_iff L).mp <|
      (IsCurveOver.isFunctionField (k := k) (X := X)).of_constantCompositum_eq_top_of_linearDisjoint
        (TauCeti.AlgebraicGeometry.linearDisjoint_functionField_of_isPullback HX)
        (TauCeti.AlgebraicGeometry.constantCompositum_functionField_eq_top_of_isPullback HX)⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

section AlgClosed

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsCurveOver k] [Y.IsCurveOver k] [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
  {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
  [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))]
  [IsAlgClosed k] [IsDominant f] (Hf : IsPullback gX f' f gY)
  (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k L))))

include Hf HY

/-- **Closed-fibre comparison for dominant morphisms of curves over an algebraically closed field.**
If `f : X ⟶ Y` is a dominant `k`-morphism of curves over an algebraically closed field `k` and
`f' : X' ⟶ Y'` is its pullback along an arbitrary field extension `L / k`, then for every point
`y' : Y'` with `gY y' ≠ genericPoint Y`, projection along `gX` defines a bijection
`{x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'}`. -/
noncomputable def curveFiberEquivOfIsAlgClosed (y' : Y') (hy : gY y' ≠ genericPoint Y) :
    {x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'} :=
  fiberEquivOfIsAlgClosed Hf HY y'
    (Scheme.IsCurveOver.isClosed_singleton_of_ne_genericPoint (k := k) hy)
    fun _ hx ↦ Scheme.IsCurveOver.isClosed_singleton_of_map_ne_genericPoint (k := k) f (hx ▸ hy)

/-- `curveFiberEquivOfIsAlgClosed` acts on underlying points via the projection `gX`. -/
@[simp]
theorem curveFiberEquivOfIsAlgClosed_coe (y' : Y') (hy : gY y' ≠ genericPoint Y)
    (x' : {x' : X' // f' x' = y'}) :
    (curveFiberEquivOfIsAlgClosed Hf HY y' hy x').val = gX x'.val :=
  fiberEquivOfIsAlgClosed_coe Hf HY y' _ _ x'

end AlgClosed

end AlgebraicGeometry.Scheme.Hom
