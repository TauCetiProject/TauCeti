/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth

/-!
# The elliptic curve of a Weierstrass equation

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`. Its projective model
`W.projModel`, with structure morphism `W.projModelOver` and zero section `[0 : 1 : 0]`, is smooth
of relative dimension one and proper over `Spec R`, and it is its own pointed Weierstrass chart
over the whole base. It is therefore an elliptic curve over `Spec R` in the sense of
`EllipticCurveGeom`: `W.toEllipticCurveGeom`. By definition, every elliptic curve over a scheme is,
Zariski-locally on the base, isomorphic to one of these.

The total space of `toEllipticCurveGeom W` is identified with `W.projModel` by
`toEllipticCurveGeomIso`, compatibly with the structure morphisms and the zero sections. Base change
along `Spec φ : Spec R' ⟶ Spec R` for a ring homomorphism `φ : R →+* R'` corresponds to extending
the coefficients of `W` along `φ`: the total space of `(toEllipticCurveGeom W).baseChange (Spec φ)`
is identified with `(W.map φ).projModel` by `toEllipticCurveGeomBaseChangeIso`, again compatibly
with the structure morphisms and the zero sections, and with the projections to `W.projModel`.

## Main definitions

* `WeierstrassCurve.toEllipticCurveGeom W`: the projective model of an elliptic Weierstrass curve
  `W` over `R`, as an elliptic curve over `Spec R`.
* `WeierstrassCurve.toEllipticCurveGeomIso W`: the identification of the total space of
  `toEllipticCurveGeom W` with `W.projModel`.
* `WeierstrassCurve.toEllipticCurveGeomBaseChangeIso W φ`: the identification of the total space of
  the base change of `toEllipticCurveGeom W` along `Spec φ` with `(W.map φ).projModel`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-! ### The projective model as an elliptic curve -/

/-- The **elliptic curve over `Spec R` of an elliptic Weierstrass curve** `W` over `R`: the
projective model `W.projModel`, with structure morphism `W.projModelOver` and zero section the
point `[0 : 1 : 0]` (`W.projModelZero`). Its pointed Weierstrass atlas consists of a single chart
over the whole base, whose isomorphism with the projective model is the identity. The total space
is identified with `W.projModel` by `toEllipticCurveGeomIso`. -/
noncomputable def toEllipticCurveGeom : EllipticCurveGeom (Spec (.of R)) where
  carrier := W.projModel
  structureMap := W.projModelOver
  zero := W.projModelZero
  zero_comp := W.projModelZero_projModelOver
  smooth := inferInstance
  proper := inferInstance
  localModel := ⟨{
    index := PUnit
    chart _ := {
      base := Spec (.of R)
      baseMap := 𝟙 _
      baseMap_open := inferInstance
      ring := .of R
      baseIso := Iso.refl _
      equation := W
      equation_elliptic := inferInstance
      pullbackCarrier := W.projModel
      toTotal := 𝟙 _
      toBase := W.projModelOver
      isPullback := .of_id_fst
      modelIso := Iso.refl _
      modelIso_over := by simp
      pulledZero := W.projModelZero
      pulledZero_toBase := W.projModelZero_projModelOver
      pulledZero_toTotal := by simp
      modelIso_zero := by simp }
    covers s := ⟨PUnit.unit, s, rfl⟩ }⟩

/-- The isomorphism identifying the total space of `toEllipticCurveGeom W` with the projective model
`W.projModel`. Under it, the structure morphism of `toEllipticCurveGeom W` is `W.projModelOver`
(`toEllipticCurveGeomIso_hom_projModelOver`) and its zero section is `W.projModelZero`
(`zero_toEllipticCurveGeomIso_hom`). -/
noncomputable def toEllipticCurveGeomIso : (toEllipticCurveGeom W).carrier ≅ W.projModel :=
  Iso.refl _

/-- Under `toEllipticCurveGeomIso`, the structure morphism of `toEllipticCurveGeom W` is
`W.projModelOver`. -/
@[reassoc (attr := simp)]
theorem toEllipticCurveGeomIso_hom_projModelOver :
    (toEllipticCurveGeomIso W).hom ≫ W.projModelOver = (toEllipticCurveGeom W).structureMap := by
  simp [toEllipticCurveGeomIso, toEllipticCurveGeom]

/-- Under `toEllipticCurveGeomIso`, the zero section of `toEllipticCurveGeom W` is the zero section
`[0 : 1 : 0]` of the projective model. -/
@[reassoc (attr := simp)]
theorem zero_toEllipticCurveGeomIso_hom :
    (toEllipticCurveGeom W).zero ≫ (toEllipticCurveGeomIso W).hom = W.projModelZero := by
  simp [toEllipticCurveGeomIso, toEllipticCurveGeom]

/-! ### Base change along a ring homomorphism -/

variable {R' : Type u} [CommRing R'] (φ : R →+* R')

-- The projective model of `W.map φ` is a pullback of the structure morphism of
-- `toEllipticCurveGeom W` along `Spec φ`.
private theorem isPullback_projModelBaseChange_comp_toEllipticCurveGeomIso_inv :
    IsPullback (W.projModelBaseChange φ ≫ (toEllipticCurveGeomIso W).inv) (W.map φ).projModelOver
      (toEllipticCurveGeom W).structureMap (Spec.map (CommRingCat.ofHom φ)) :=
  (W.isPullback_projModelBaseChange φ).of_iso (.refl _) (toEllipticCurveGeomIso W).symm (.refl _)
    (.refl _) (by simp) (by simp) (by simp [Iso.eq_inv_comp]) (by simp)

/-- The isomorphism identifying the total space of the base change of `toEllipticCurveGeom W` along
`Spec φ : Spec R' ⟶ Spec R` with the projective model of `W.map φ`. Under it, the structure
morphism of the base change is `(W.map φ).projModelOver`
(`toEllipticCurveGeomBaseChangeIso_hom_projModelOver`), its zero section is
`(W.map φ).projModelZero` (`zero_toEllipticCurveGeomBaseChangeIso_hom`), and its projection to
`toEllipticCurveGeom W` is the base change morphism `W.projModelBaseChange φ`
(`toEllipticCurveGeomBaseChangeIso_hom_projModelBaseChange`). -/
noncomputable def toEllipticCurveGeomBaseChangeIso :
    ((toEllipticCurveGeom W).baseChange (Spec.map (CommRingCat.ofHom φ))).carrier ≅
      (W.map φ).projModel :=
  ((toEllipticCurveGeom W).isPullback_baseChange _).isoIsPullback _ _
    (isPullback_projModelBaseChange_comp_toEllipticCurveGeomIso_inv W φ)

/-- Under `toEllipticCurveGeomBaseChangeIso`, the structure morphism of the base change of
`toEllipticCurveGeom W` along `Spec φ` is `(W.map φ).projModelOver`. -/
@[reassoc (attr := simp)]
theorem toEllipticCurveGeomBaseChangeIso_hom_projModelOver :
    (toEllipticCurveGeomBaseChangeIso W φ).hom ≫ (W.map φ).projModelOver =
      ((toEllipticCurveGeom W).baseChange (Spec.map (CommRingCat.ofHom φ))).structureMap :=
  IsPullback.isoIsPullback_hom_snd ..

/-- Under `toEllipticCurveGeomBaseChangeIso` and `toEllipticCurveGeomIso`, the projection from the
base change of `toEllipticCurveGeom W` along `Spec φ` to `toEllipticCurveGeom W` is the base change
morphism `W.projModelBaseChange φ : (W.map φ).projModel ⟶ W.projModel`. -/
@[reassoc (attr := simp)]
theorem toEllipticCurveGeomBaseChangeIso_hom_projModelBaseChange :
    (toEllipticCurveGeomBaseChangeIso W φ).hom ≫ W.projModelBaseChange φ =
      ((toEllipticCurveGeom W).baseChangeIso _).hom ≫ pullback.fst _ _ ≫
        (toEllipticCurveGeomIso W).hom := by
  rw [← cancel_mono (toEllipticCurveGeomIso W).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact IsPullback.isoIsPullback_hom_fst ..

/-- Under `toEllipticCurveGeomBaseChangeIso`, the zero section of the base change of
`toEllipticCurveGeom W` along `Spec φ` is the zero section `[0 : 1 : 0]` of the projective model of
`W.map φ`. -/
@[reassoc (attr := simp)]
theorem zero_toEllipticCurveGeomBaseChangeIso_hom :
    ((toEllipticCurveGeom W).baseChange (Spec.map (CommRingCat.ofHom φ))).zero ≫
      (toEllipticCurveGeomBaseChangeIso W φ).hom = (W.map φ).projModelZero := by
  apply (W.isPullback_projModelBaseChange φ).hom_ext <;> simp

end WeierstrassCurve
