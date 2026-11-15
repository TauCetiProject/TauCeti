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

This file specializes the base-change theory of function fields and pointwise ramification indices
to proper curves over a field `k` (`AlgebraicGeometry.Scheme.IsCurveOver`):

* `AlgebraicGeometry.Scheme.IsCurveOver.isClosed_singleton_of_ne_genericPoint`: every non-generic
  point of a curve over `k` is closed.
* `AlgebraicGeometry.Scheme.IsCurveOver.of_isPullback`: the base change of a geometrically integral
  curve over `k` along an arbitrary field extension `L / k` (algebraic or transcendental, separable
  or not) is a curve over `L`.
* `AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_genericPoint_of_isSeparable` and
  `AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_genericPoint_of_charZero`: a dominant
  `k`-morphism of curves whose function-field extension is separable (automatic in characteristic
  zero) is formally unramified at the generic point.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_isPullback_of_isCurveOver`: for any dominant
  `k`-morphism `f : X ⟶ Y` of curves over a characteristic-zero field `k` pulled back along an
  arbitrary field extension `L / k` to `f' : X' ⟶ Y'`, `f'.ramificationIdxAt x' =
  f.ramificationIdxAt (gX x')` at **every** point `x' : X'` (both closed points and points mapping
  to the generic point when `L / k` is transcendental).
* `AlgebraicGeometry.Scheme.Hom.curveFiberEquivOfIsAlgClosed` and
  `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_curveFiberEquivOfIsAlgClosed`: over an
  algebraically closed field `k`, base change along `L / k` identifies every non-generic fibre of a
  dominant morphism of curves `{x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'}` compatibly with
  `ramificationIdxAt`, in arbitrary characteristic.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Every point of a curve over `k` other than the generic point is closed. -/
theorem IsCurveOver.isClosed_singleton_of_ne_genericPoint {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsCurveOver k] {x : X}
    (hx : x ≠ genericPoint X) : IsClosed {x} := by
  have : IsNoetherian X := IsCurveOver.isNoetherian k X
  exact TauCeti.isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one
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
  have : IsScalarTower k X.functionField X'.functionField :=
    .of_algebraMap_eq fun c ↦
      (TauCeti.AlgebraicGeometry.functionFieldMap_baseChange_algebraMap HX c).symm
  have hFF : TauCeti.IsFunctionField L X'.functionField :=
    (IsCurveOver.isFunctionField (k := k) (X := X)).of_constantCompositum_eq_top_of_linearDisjoint
      (TauCeti.AlgebraicGeometry.linearDisjoint_functionField_of_isPullback HX)
      (TauCeti.AlgebraicGeometry.constantCompositum_functionField_eq_top_of_isPullback HX)
  exact isCurveOver_iff.mpr
    ⟨hInt, hProp, (TauCeti.AlgebraicGeometry.isFunctionField_functionField_iff L).mp hFF⟩

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
  have hfmap : f.functionFieldMap.hom.FormallyUnramified :=
    Algebra.FormallyUnramified.of_isSeparable Y.functionField X.functionField
  let e : Y.presheaf.stalk (genericPoint Y) ≅ Y.presheaf.stalk (f (genericPoint X)) :=
    ⟨Y.presheaf.stalkSpecializes (specializes_of_eq f.genericPoint_eq_of_isDominant),
      Y.presheaf.stalkSpecializes (specializes_of_eq f.genericPoint_eq_of_isDominant.symm),
      by simp, by simp⟩
  have heq : e.hom ≫ f.stalkMap (genericPoint X) = f.functionFieldMap := by
    rw [f.eq_functionFieldMap_iff, Spec.map_comp_assoc, SpecMap_stalkSpecializes_fromSpecStalk,
      SpecMap_stalkMap_fromSpecStalk]
  have hcomp : ((f.stalkMap (genericPoint X)).hom.comp e.hom.hom).FormallyUnramified := by
    rw [← CommRingCat.hom_comp, heq]
    exact hfmap
  have : IsIso e.hom := e.isIso_hom
  exact (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso
    e.hom (f.stalkMap (genericPoint X))).mp hcomp

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

/-- **Pointwise ramification invariance for curve covers over a perfect field.** Let `f : X ⟶ Y` be
a `k`-morphism of curves over a perfect field `k` that is formally unramified at the generic point
of `X`, and let `f' : X' ⟶ Y'` be its pullback along an arbitrary field extension `L / k`. Then
`f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x')` at **every** point `x' : X'`. -/
theorem ramificationIdxAt_eq_of_isPullback_of_isCurveOver_of_formallyUnramified_genericPoint
    {k L : Type u} [Field k] [PerfectField k] [Field L] [Algebra k L]
    {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X.IsCurveOver k] [Y.IsCurveOver k] [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))]
    (hfu : (f.stalkMap (genericPoint X)).hom.FormallyUnramified)
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (x' : X') :
    f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x') := by
  have hcompP : IsProper (f ≫ (Y ↘ Spec (.of k))) := by rw [comp_over]; infer_instance
  have hprop : IsProper f := IsProper.of_comp f (Y ↘ Spec (.of k))
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback Hf inferInstance
  by_cases hgen : gX x' = genericPoint X
  · have hfu' : (f'.stalkMap x').hom.FormallyUnramified :=
      formallyUnramified_stalkMap_of_isPullback Hf x' (hgen ▸ hfu)
    rw [hgen, f'.ramificationIdxAt_eq_one_of_notMem_ramificationLocus
      (by simpa [mem_ramificationLocus_iff] using hfu'),
      f.ramificationIdxAt_eq_one_of_notMem_ramificationLocus
      (by simpa [mem_ramificationLocus_iff] using hfu)]
  · have hxcl : IsClosed {gX x'} :=
      Scheme.IsCurveOver.isClosed_singleton_of_ne_genericPoint (k := k) hgen
    have hycl : IsClosed {f (gX x')} := by
      simpa only [Set.image_singleton] using f.isClosedMap _ hxcl
    exact ramificationIdxAt_eq_of_isPullback_of_isClosed Hf HY hxcl hycl

/-- **Characteristic-zero pointwise ramification invariance for curve covers.** Let `f : X ⟶ Y` be
a dominant `k`-morphism of curves over a characteristic-zero field `k`, and let `f' : X' ⟶ Y'` be
its pullback along an arbitrary field extension `L / k` (algebraic or transcendental). Then
`f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x')` at **every** point `x' : X'`. -/
theorem ramificationIdxAt_eq_of_isPullback_of_isCurveOver
    {k L : Type u} [Field k] [CharZero k] [Field L] [Algebra k L]
    {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X.IsCurveOver k] [Y.IsCurveOver k] [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))] [IsDominant f]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (x' : X') :
    f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x') :=
  ramificationIdxAt_eq_of_isPullback_of_isCurveOver_of_formallyUnramified_genericPoint
    (formallyUnramified_stalkMap_genericPoint_of_charZero (k := k) f) Hf HY x'

/-- **Closed-fibre comparison for dominant morphisms of curves over an algebraically closed field.**
If `f : X ⟶ Y` is a dominant `k`-morphism of curves over an algebraically closed field `k` and
`f' : X' ⟶ Y'` is its pullback along an arbitrary field extension `L / k`, then for every point
`y' : Y'` with `gY y' ≠ genericPoint Y`, projection along `gX` defines a bijection
`{x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'}`. -/
noncomputable def curveFiberEquivOfIsAlgClosed {k L : Type u} [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [X.IsCurveOver k] [Y.IsCurveOver k]
    [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))] [IsDominant f]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (y' : Y') (hy : gY y' ≠ genericPoint Y) :
    {x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'} :=
  fiberEquivOfIsAlgClosed Hf HY y'
    (Scheme.IsCurveOver.isClosed_singleton_of_ne_genericPoint (k := k) hy)
    fun _ hx ↦ Scheme.IsCurveOver.isClosed_singleton_of_ne_genericPoint (k := k) fun hgen ↦
      hy (hx ▸ hgen ▸ f.genericPoint_eq_of_isDominant)

/-- `curveFiberEquivOfIsAlgClosed` acts on underlying points via the projection `gX`. -/
@[simp]
theorem curveFiberEquivOfIsAlgClosed_coe {k L : Type u} [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [X.IsCurveOver k] [Y.IsCurveOver k]
    [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))] [IsDominant f]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (y' : Y') (hy : gY y' ≠ genericPoint Y) (x' : {x' : X' // f' x' = y'}) :
    (curveFiberEquivOfIsAlgClosed Hf HY y' hy x').1 = gX x'.1 := by
  unfold curveFiberEquivOfIsAlgClosed
  exact fiberEquivOfIsAlgClosed_coe Hf HY y' _ _ x'

/-- `curveFiberEquivOfIsAlgClosed` preserves `ramificationIdxAt` in arbitrary characteristic. -/
theorem ramificationIdxAt_curveFiberEquivOfIsAlgClosed {k L : Type u} [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [X.IsCurveOver k] [Y.IsCurveOver k]
    [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))] [IsDominant f]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (y' : Y') (hy : gY y' ≠ genericPoint Y) (x' : {x' : X' // f' x' = y'}) :
    f'.ramificationIdxAt x'.1 =
      f.ramificationIdxAt (curveFiberEquivOfIsAlgClosed Hf HY y' hy x').1 := by
  unfold curveFiberEquivOfIsAlgClosed
  exact ramificationIdxAt_fiberEquivOfIsAlgClosed Hf HY y' _ _ x'

end AlgebraicGeometry.Scheme.Hom
