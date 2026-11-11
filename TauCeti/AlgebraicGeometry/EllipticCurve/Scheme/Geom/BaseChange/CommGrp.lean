/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Hom

/-!
# Base change of the commutative group scheme of an elliptic curve

The canonical group law on a base-changed elliptic curve agrees with the pullback of its
original group law. The comparison below packages this agreement as an isomorphism of
commutative group schemes. This allows constructions on group schemes, such as relative
Frobenius, to take values in the canonical elliptic base change.

The compatibility proof generalizes
`WeierstrassCurve.isMonHom_projModelOverBaseChangeIso_hom`. That proof adapts AINTLIB's
`isMonHom_modelBaseChangeIso` (Apache-2.0, github.com/CBirkbeck/AINTLIB, revision
`c3415f32a313e19ace43e05479aeaa0d56ca287a`,
`projects/ModularCurves/ModularCurves/EllipticCurve/AffineSectionSpecPoints.lean`).
Here the curve and base are arbitrary schemes, and the addition comparison is supplied by
`EllipticCurveGeom.addition_baseChangeIso_hom_fst`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S T : Scheme.{u}} (E : EllipticCurveGeom S) (f : T ⟶ S)

/-- The base-change comparison on the underlying schemes over the new base. -/
noncomputable def baseChangeOverIso :
    Over.mk (E.baseChange f).structureMap ≅ (Over.pullback f).obj (Over.mk E.structureMap) :=
  Over.isoMk (E.baseChangeIso f) (E.baseChangeIso_hom_snd f)

/-- The comparison over the base has the usual underlying base-change isomorphism. -/
@[simp]
theorem baseChangeOverIso_hom_left :
    (E.baseChangeOverIso f).hom.left = (E.baseChangeIso f).hom := (rfl)

/-- The inverse comparison over the base has the usual underlying inverse isomorphism. -/
@[simp]
theorem baseChangeOverIso_inv_left :
    (E.baseChangeOverIso f).inv.left = (E.baseChangeIso f).inv := (rfl)

/-- The canonical group law on the elliptic base change is the pulled-back group law. -/
instance isMonHom_baseChangeOverIso_hom : IsMonHom (E.baseChangeOverIso f).hom where
  one_hom := by
    ext1
    apply pullback.hom_ext <;> simp
  mul_hom := by
    ext1
    apply pullback.hom_ext
    · have h : ((E.baseChangeOverIso f).hom ⊗ₘ (E.baseChangeOverIso f).hom).left ≫
          (Functor.LaxMonoidal.μ (Over.pullback f)
            (Over.mk E.structureMap) (Over.mk E.structureMap)).left ≫ pullback.fst _ _ =
          pullback.map _ _ _ _ ((E.baseChangeIso f).hom ≫ pullback.fst _ _)
            ((E.baseChangeIso f).hom ≫ pullback.fst _ _) f
            (E.isPullback_baseChange f).w.symm (E.isPullback_baseChange f).w.symm := by
        apply pullback.hom_ext <;> simp [Over.tensorHom_left]
      simp only [Functor.obj.μ_def, Over.comp_left, Category.assoc, Over.pullback_map_left,
        pullback.lift_fst]
      rw [reassoc_of% h]
      simp
    · simp [Over.tensorHom_left, pullback.condition]

/-- The commutative group scheme of an elliptic base change is canonically isomorphic to the
pullback of the original commutative group scheme. -/
noncomputable def baseChangeCommGrpIso :
    (E.baseChange f).toCommGrp ≅ (Over.pullback f).mapCommGrp.obj E.toCommGrp :=
  CommGrp.mkIso' (E.baseChangeOverIso f)

/-- The group-scheme comparison has the usual underlying base-change isomorphism. -/
@[simp]
theorem baseChangeCommGrpIso_hom_left :
    (E.baseChangeCommGrpIso f).hom.hom.hom.hom.left = (E.baseChangeIso f).hom := (rfl)

/-- The inverse group-scheme comparison has the usual underlying inverse isomorphism. -/
@[simp]
theorem baseChangeCommGrpIso_inv_left :
    (E.baseChangeCommGrpIso f).inv.hom.hom.hom.left = (E.baseChangeIso f).inv := (rfl)

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
