/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.Field
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Geometrically.FunctionField
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationIdx.Pullback

/-!
# Base change of proper curves and pointwise ramification comparison

This file specializes base change of function fields and pointwise ramification indices to proper
curves over a field `k` (`AlgebraicGeometry.Scheme.IsCurveOver`):

* `AlgebraicGeometry.Scheme.IsCurveOver.isClosed_singleton_of_ne_genericPoint`: non-generic points
  of a curve are closed.
* `AlgebraicGeometry.Scheme.IsCurveOver.of_isPullback`: base change of a geometrically integral
  curve along an arbitrary field extension `L / k` is a curve over `L`.
* `AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_genericPoint_of_isSeparable`,
  `AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_genericPoint_of_charZero`: generic
  formal unramifiedness for separable (in particular characteristic-zero) dominant curve morphisms.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_isPullback_of_isCurveOver`,
  `ramificationIdxAt_eq_of_isPullback_of_isCurveOver_of_formallyUnramified_genericPoint`:
  pointwise ramification invariance at every point of a pulled-back curve cover.
* `AlgebraicGeometry.Scheme.Hom.curveFiberEquivOfIsAlgClosed`,
  `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_curveFiberEquivOfIsAlgClosed`: non-generic fibre
  bijection over an algebraically closed field preserving `ramificationIdxAt`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Every point of a curve over `k` other than the generic point is closed. -/
theorem IsCurveOver.isClosed_singleton_of_ne_genericPoint {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsCurveOver k] {x : X}
    (hx : x ≠ genericPoint X) : IsClosed {x} :=
  have : IsNoetherian X := IsCurveOver.isNoetherian k X
  TauCeti.isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one
    (IsCurveOver.coheight_le_one (k := k))
    ((TauCeti.AlgebraicGeometry.Scheme.coheight_eq_one_iff_ne_genericPoint
      (IsCurveOver.topologicalKrullDim_eq_one k).le).mpr hx)

/-- **Base change of a geometrically integral curve.** If `X` is a geometrically integral curve
over `k`, its pullback `X'` along an arbitrary field extension `L / k` (algebraic or
transcendental, separable or not) is a curve over `L`. -/
theorem IsCurveOver.of_isPullback {k L : Type u} [Field k] [Field L] [Algebra k L]
    {X X' : Scheme.{u}} [X.Over (Spec (.of k))] [X'.Over (Spec (.of L))]
    [X.IsCurveOver k] [GeometricallyIntegral (X ↘ Spec (.of k))] {gX : X' ⟶ X}
    (HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    X'.IsCurveOver L := by
  have hInt : IsIntegral X' := TauCeti.AlgebraicGeometry.isIntegral_of_isPullback_spec HX
  have hProp : IsProper (X' ↘ Spec (.of L)) := MorphismProperty.of_isPullback HX inferInstance
  have hDom : IsDominant gX := TauCeti.AlgebraicGeometry.isDominant_of_isPullback_spec HX
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

/-- A dominant morphism of integral schemes whose induced function-field extension is separable is
formally unramified at the generic point of the source. -/
theorem formallyUnramified_stalkMap_genericPoint_of_isSeparable {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (hsep : letI := f.functionFieldMap.hom.toAlgebra;
      Algebra.IsSeparable Y.functionField X.functionField) :
    (f.stalkMap (genericPoint X)).hom.FormallyUnramified := by
  let _ : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
  let e : Y.presheaf.stalk (genericPoint Y) ≅ Y.presheaf.stalk (f (genericPoint X)) :=
    ⟨Y.presheaf.stalkSpecializes (specializes_of_eq f.genericPoint_eq_of_isDominant),
      Y.presheaf.stalkSpecializes (specializes_of_eq f.genericPoint_eq_of_isDominant.symm),
      by simp, by simp⟩
  have heq : e.hom ≫ f.stalkMap (genericPoint X) = f.functionFieldMap := by
    rw [f.eq_functionFieldMap_iff, Spec.map_comp_assoc, SpecMap_stalkSpecializes_fromSpecStalk,
      SpecMap_stalkMap_fromSpecStalk]
  have : IsIso e.hom := e.isIso_hom
  refine (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso
    e.hom (f.stalkMap (genericPoint X))).mp ?_
  rw [← CommRingCat.hom_comp, heq]
  exact Algebra.FormallyUnramified.of_isSeparable Y.functionField X.functionField

/-- A dominant `k`-morphism of curves over a characteristic-zero field is formally unramified at the
generic point of the source. -/
theorem formallyUnramified_stalkMap_genericPoint_of_charZero {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X.IsCurveOver k] [Y.IsCurveOver k] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f] :
    (f.stalkMap (genericPoint X)).hom.FormallyUnramified := by
  let _ : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
  have : IsScalarTower k Y.functionField X.functionField :=
    .of_algebraMap_eq fun c ↦ (f.functionFieldMap_algebraMap k c).symm
  have : CharZero Y.functionField :=
    charZero_of_injective_algebraMap (algebraMap k Y.functionField).injective
  have : Algebra.IsAlgebraic Y.functionField X.functionField :=
    (Scheme.IsCurveOver.isFunctionField (k := k) (X := Y)).isAlgebraic_of_isFunctionField
      (Scheme.IsCurveOver.isFunctionField (k := k) (X := X))
  exact formallyUnramified_stalkMap_genericPoint_of_isSeparable f inferInstance

section CurvePullback

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsCurveOver k] [Y.IsCurveOver k] [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
  {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
  [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))]

/-- **Pointwise ramification invariance for curve covers over a perfect field.** Let `f : X ⟶ Y` be
a `k`-morphism of curves over a perfect field `k` that is formally unramified at the generic point
of `X`, and let `f' : X' ⟶ Y'` be its pullback along an arbitrary field extension `L / k`. Then
`f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x')` at **every** point `x' : X'`. -/
theorem ramificationIdxAt_eq_of_isPullback_of_isCurveOver_of_formallyUnramified_genericPoint
    [PerfectField k] (hfu : (f.stalkMap (genericPoint X)).hom.FormallyUnramified)
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (x' : X') :
    f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x') := by
  have hcompP : IsProper (f ≫ (Y ↘ Spec (.of k))) := by rw [comp_over]; infer_instance
  have hprop : IsProper f := IsProper.of_comp f (Y ↘ Spec (.of k))
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback Hf inferInstance
  by_cases hgen : gX x' = genericPoint X
  · have hfu' := formallyUnramified_stalkMap_of_isPullback Hf x' (hgen ▸ hfu)
    rw [hgen, f'.ramificationIdxAt_eq_one_of_notMem_ramificationLocus
      (by simpa [mem_ramificationLocus_iff] using hfu'),
      f.ramificationIdxAt_eq_one_of_notMem_ramificationLocus
      (by simpa [mem_ramificationLocus_iff] using hfu)]
  · have hxcl := Scheme.IsCurveOver.isClosed_singleton_of_ne_genericPoint (k := k) hgen
    exact ramificationIdxAt_eq_of_isPullback_of_isClosed Hf HY hxcl
      (by simpa only [Set.image_singleton] using f.isClosedMap _ hxcl)

/-- **Characteristic-zero pointwise ramification invariance for curve covers.** Let `f : X ⟶ Y` be
a dominant `k`-morphism of curves over a characteristic-zero field `k`, and let `f' : X' ⟶ Y'` be
its pullback along an arbitrary field extension `L / k` (algebraic or transcendental). Then
`f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x')` at **every** point `x' : X'`. -/
theorem ramificationIdxAt_eq_of_isPullback_of_isCurveOver [CharZero k] [IsDominant f]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (x' : X') :
    f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x') :=
  ramificationIdxAt_eq_of_isPullback_of_isCurveOver_of_formallyUnramified_genericPoint
    (formallyUnramified_stalkMap_genericPoint_of_charZero (k := k) f) Hf HY x'

section AlgClosed

variable [IsAlgClosed k] [IsDominant f] (Hf : IsPullback gX f' f gY)
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
    fun _ hx ↦ Scheme.IsCurveOver.isClosed_singleton_of_ne_genericPoint (k := k) fun hgen ↦
      hy (hx ▸ hgen ▸ f.genericPoint_eq_of_isDominant)

/-- `curveFiberEquivOfIsAlgClosed` acts on underlying points via the projection `gX`. -/
@[simp]
theorem curveFiberEquivOfIsAlgClosed_coe (y' : Y') (hy : gY y' ≠ genericPoint Y)
    (x' : {x' : X' // f' x' = y'}) :
    (curveFiberEquivOfIsAlgClosed Hf HY y' hy x').val = gX x'.val :=
  fiberEquivOfIsAlgClosed_coe Hf HY y' _ _ x'

/-- `curveFiberEquivOfIsAlgClosed` preserves `ramificationIdxAt` in arbitrary characteristic. -/
theorem ramificationIdxAt_curveFiberEquivOfIsAlgClosed (y' : Y') (hy : gY y' ≠ genericPoint Y)
    (x' : {x' : X' // f' x' = y'}) :
    f'.ramificationIdxAt x'.val =
      f.ramificationIdxAt (curveFiberEquivOfIsAlgClosed Hf HY y' hy x').val :=
  ramificationIdxAt_fiberEquivOfIsAlgClosed Hf HY y' _ _ x'

end AlgClosed

end CurvePullback

end AlgebraicGeometry.Scheme.Hom
