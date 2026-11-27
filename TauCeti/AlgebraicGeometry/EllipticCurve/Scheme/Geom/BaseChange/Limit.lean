/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Spreading out points of an elliptic curve

Let `S = lim Dⱼ` be the limit of a cofiltered diagram of quasi-compact quasi-separated schemes with
affine transition maps, and let `E` be an elliptic curve over a member `Dᵢ`. Every `S`-point of the
base change `E_S` is the base change of a `Dⱼ`-point of the base change `E_{Dⱼ}`, for some `j ⟶ i`.
This is the descent of morphisms to a scheme locally of finite presentation (Stacks 01ZC), applied
to the composite `S ⟶ E_S ⟶ E`. The base change of points is taken along the pullback square
formed by the canonical map `E.baseChangeMap` (`EllipticCurveGeom.isPullback_baseChangeMap`).

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_pointsPullback_baseChangeMap_eq`: points
  spread out along cofiltered limits.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Troisième partie, §8.
* The Stacks Project, [Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC).
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c) {i : I}
  (E : EllipticCurveGeom (D.obj i))

include hc in
/-- **Spreading out points.** Let `S = lim Dⱼ` be a cofiltered limit of quasi-compact
quasi-separated schemes with affine transition maps, and let `E` be an elliptic curve over a member
`Dᵢ`. Every `S`-point of the base change `E_S` of `E` is, for some `j ⟶ i`, the base change of a
`Dⱼ`-point of the base change `E_{Dⱼ}`. -/
theorem exists_pointsPullback_baseChangeMap_eq
    (P : 𝟙_ (Over c.pt) ⟶ Over.mk (E.baseChange (c.π.app i)).structureMap) :
    ∃ (j : I) (g : j ⟶ i) (Q : 𝟙_ (Over (D.obj j)) ⟶ Over.mk (E.baseChange (D.map g)).structureMap),
      pointsPullback (E.isPullback_baseChangeMap (c.π.app j) (c.w g))
        (E.zero_baseChangeMap _ _) Q = P := by
  have hg := E.isPullback_baseChange (c.π.app i)
  -- The `S`-point of `E_S` is a morphism `a : S ⟶ E` over `Dᵢ`, which descends to some `Dⱼ`.
  set a := P.left ≫ (E.baseChangeIso (c.π.app i)).hom ≫ pullback.fst _ _
  have ha : a ≫ E.structureMap = c.π.app i := by
    simp [a, hg.w]
  have {j k : Over i} (f : j ⟶ k) : IsAffineHom ((Over.forget i ⋙ D).map f) :=
    inferInstanceAs (IsAffineHom (D.map f.left))
  have (j : Over i) : CompactSpace ((Over.forget i ⋙ D).obj j) :=
    inferInstanceAs (CompactSpace (D.obj j.left))
  have (j : Over i) : QuasiSeparatedSpace ((Over.forget i ⋙ D).obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  have : Smooth E.structureMap := SmoothOfRelativeDimension.smooth 1 _
  let q : Over.forget i ⋙ D ⟶ (Functor.const _).obj (D.obj i) :=
    { app j := D.map j.hom
      naturality j k f := by simp [← D.map_comp] }
  obtain ⟨j, b, hb, hb'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (Over.forget i ⋙ D) q E.structureMap _
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc) a
    (by ext j; exact (c.w j.hom).trans ha.symm)
  have hj := E.isPullback_baseChange (D.map j.hom)
  refine ⟨j.left, j.hom, (pointsBaseChangeEquiv hj (by simp)).symm (Over.homMk b hb'), ?_⟩
  refine ((eq_pointsPullback_iff _ _).mpr ?_).symm
  apply hj.hom_ext
  · simpa [a] using hb.symm
  · simp

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
