/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.GroupLaw
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

The group law of the elliptic curve `toEllipticCurveGeom W`, glued from the Bosma–Lenstra addition
morphisms of its local Weierstrass equations, is the group law of the projective model of `W`
itself: `toEllipticCurveGeomIso` is an isomorphism of group schemes over `Spec R`
(`isMonHom_toEllipticCurveGeomOverIso_hom`).

## Main definitions

* `WeierstrassCurve.toEllipticCurveGeom W`: the projective model of an elliptic Weierstrass curve
  `W` over `R`, as an elliptic curve over `Spec R`.
* `WeierstrassCurve.toEllipticCurveGeomIso W`: the identification of the total space of
  `toEllipticCurveGeom W` with `W.projModel`.
* `WeierstrassCurve.toEllipticCurveGeomOverIso W`: the same identification, as an isomorphism of
  objects of `Over (Spec R)`.
* `WeierstrassCurve.toEllipticCurveGeomBaseChangeIso W φ`: the identification of the total space of
  the base change of `toEllipticCurveGeom W` along `Spec φ` with `(W.map φ).projModel`.

## Main results

* `WeierstrassCurve.addition_toEllipticCurveGeomIso_hom` and
  `WeierstrassCurve.neg_toEllipticCurveGeomIso_hom`: the addition and negation morphisms of
  `toEllipticCurveGeom W` are those of the projective model of `W`.
* `WeierstrassCurve.isMonHom_toEllipticCurveGeomOverIso_hom`: `toEllipticCurveGeomOverIso W` is an
  isomorphism of group schemes over `Spec R`.

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

/-! ### The group law -/

/-- The identification `toEllipticCurveGeomIso` of the total space of `toEllipticCurveGeom W` with
the projective model `W.projModel`, as an isomorphism of objects of `Over (Spec R)`. It is an
isomorphism of group schemes over `Spec R`, for the group law `EllipticCurveGeom.grpObj` of
`toEllipticCurveGeom W` and the group law `grpObjProjModel` of the projective model
(`isMonHom_toEllipticCurveGeomOverIso_hom`). -/
noncomputable def toEllipticCurveGeomOverIso :
    Over.mk (toEllipticCurveGeom W).structureMap ≅ Over.mk W.projModelOver :=
  Over.isoMk (toEllipticCurveGeomIso W)

/-- On total spaces, `toEllipticCurveGeomOverIso` is `toEllipticCurveGeomIso`. -/
@[simp]
theorem toEllipticCurveGeomOverIso_hom_left :
    (toEllipticCurveGeomOverIso W).hom.left = (toEllipticCurveGeomIso W).hom :=
  (rfl)

/-- On total spaces, the inverse of `toEllipticCurveGeomOverIso` is that of
`toEllipticCurveGeomIso`. -/
@[simp]
theorem toEllipticCurveGeomOverIso_inv_left :
    (toEllipticCurveGeomOverIso W).inv.left = (toEllipticCurveGeomIso W).inv :=
  (rfl)

-- The pointed Weierstrass chart of `toEllipticCurveGeom W` over the whole base `Spec R`, whose
-- inclusion into the curve is the identity and whose isomorphism with the projective model of its
-- equation `W` is `toEllipticCurveGeomIso W`.
private noncomputable def chart :
    PointedWeierstrassChart (toEllipticCurveGeom W).structureMap (toEllipticCurveGeom W).zero where
  base := Spec (.of R)
  baseMap := 𝟙 _
  baseMap_open := inferInstance
  ring := .of R
  baseIso := Iso.refl _
  equation := W
  equation_elliptic := inferInstance
  pullbackCarrier := (toEllipticCurveGeom W).carrier
  toTotal := 𝟙 _
  toBase := (toEllipticCurveGeom W).structureMap
  isPullback := .of_id_fst
  modelIso := toEllipticCurveGeomIso W
  modelIso_over := by simp
  pulledZero := (toEllipticCurveGeom W).zero
  pulledZero_toBase := by simp
  pulledZero_toTotal := by simp
  modelIso_zero := by simp

/-- Under `toEllipticCurveGeomIso`, the addition morphism of `toEllipticCurveGeom W` is the
Bosma–Lenstra addition morphism of `W`. -/
@[reassoc (attr := simp)]
theorem addition_toEllipticCurveGeomIso_hom :
    (toEllipticCurveGeom W).addition ≫ (toEllipticCurveGeomIso W).hom =
      pullback.map _ _ _ _ (toEllipticCurveGeomIso W).hom (toEllipticCurveGeomIso W).hom (𝟙 _)
        (by simp) (by simp) ≫ W.additionMorphism := by
  -- on the chart `chart W` over the whole base, whose inclusion into the curve is the identity,
  -- the addition morphism is the addition of `W` transported along `toEllipticCurveGeomIso W`
  have h := (toEllipticCurveGeom W).pullbackMap_addition (chart W)
  have h2 := (chart W).addition_modelIso_hom
  dsimp only [chart] at h h2
  simp only [pullback.map_id, Category.id_comp, Category.comp_id, Iso.refl_hom] at h h2
  rw [h]
  exact h2

/-- Under `toEllipticCurveGeomIso`, the negation morphism of `toEllipticCurveGeom W` is the
negation morphism of the projective model of `W`. -/
@[reassoc (attr := simp)]
theorem neg_toEllipticCurveGeomIso_hom :
    (toEllipticCurveGeom W).neg ≫ (toEllipticCurveGeomIso W).hom =
      (toEllipticCurveGeomIso W).hom ≫ W.projModelNeg := by
  -- on the chart `chart W` over the whole base, whose inclusion into the curve is the identity,
  -- the negation morphism is the negation of `W` transported along `toEllipticCurveGeomIso W`
  have h := (toEllipticCurveGeom W).toTotal_neg (chart W)
  have h2 := (chart W).neg_modelIso_hom
  dsimp only [chart] at h h2
  simp only [Category.id_comp, Category.comp_id] at h h2
  rw [h]
  exact h2

/-- **The projective model of `W` is the group scheme `toEllipticCurveGeom W`**: the identification
`toEllipticCurveGeomOverIso` is a homomorphism from the group law `EllipticCurveGeom.grpObj` of the
elliptic curve `toEllipticCurveGeom W` to the group law `grpObjProjModel` of the projective
model. -/
instance isMonHom_toEllipticCurveGeomOverIso_hom : IsMonHom (toEllipticCurveGeomOverIso W).hom where
  one_hom := by
    ext1
    simp
  mul_hom := by
    ext1
    simp [Over.tensorHom_left]

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
