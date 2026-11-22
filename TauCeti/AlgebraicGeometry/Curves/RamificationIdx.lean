/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationIdx.Locus
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationIdx.Pullback

/-!
# Generic unramifiedness and pointwise ramification comparison for curves

This file specializes generic formal unramifiedness and pointwise ramification invariance to
proper curves over a field `k` (`AlgebraicGeometry.Scheme.IsCurveOver`):

* `AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_genericPoint_of_charZero`: generic
  formal unramifiedness for characteristic-zero dominant curve morphisms.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_isPullback_of_isCurveOver`,
  `ramificationIdxAt_eq_of_isPullback_of_isCurveOver_of_formallyUnramified_genericPoint`:
  pointwise ramification invariance at every point of a pulled-back curve cover.
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_curveFiberEquivOfIsAlgClosed`: preservation of
  `ramificationIdxAt` under `curveFiberEquivOfIsAlgClosed`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

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
  · have hxcl := TauCeti.AlgebraicGeometry.Scheme.isClosed_singleton_of_ne_genericPoint
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le hgen
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

/-- `curveFiberEquivOfIsAlgClosed` preserves `ramificationIdxAt` in arbitrary characteristic. -/
theorem ramificationIdxAt_curveFiberEquivOfIsAlgClosed [IsAlgClosed k] [IsDominant f]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (y' : Y') (hy : gY y' ≠ genericPoint Y) (x' : {x' : X' // f' x' = y'}) :
    f'.ramificationIdxAt x'.val =
      f.ramificationIdxAt (curveFiberEquivOfIsAlgClosed Hf HY y' hy x').val := by
  have hycl := TauCeti.AlgebraicGeometry.Scheme.isClosed_singleton_of_ne_genericPoint
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le hy
  have hfib : ∀ x : X, f x = gY y' → IsClosed {x} := fun _ hx ↦
    TauCeti.AlgebraicGeometry.Scheme.isClosed_singleton_of_ne_genericPoint
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le fun hgen ↦
        hy (hx ▸ hgen ▸ f.genericPoint_eq_of_isDominant)
  simpa only [fiberEquivOfIsAlgClosed_coe, curveFiberEquivOfIsAlgClosed_coe] using
    ramificationIdxAt_fiberEquivOfIsAlgClosed Hf HY y' hycl hfib x'

end CurvePullback

end AlgebraicGeometry.Scheme.Hom
