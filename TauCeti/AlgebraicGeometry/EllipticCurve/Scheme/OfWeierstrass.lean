/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.GroupLaw
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.JInvariant
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth

/-!
# The elliptic curve of a Weierstrass equation

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`. Its projective model
`W.projModel`, with structure morphism `W.projModelOver` and zero section `[0 : 1 : 0]`, is smooth
of relative dimension one and proper over `Spec R`, and it is its own pointed Weierstrass chart
over the whole base. It is therefore an elliptic curve over `Spec R` in the sense of
`EllipticCurveGeom`: `W.toEllipticCurveGeom`. By definition, every elliptic curve over a scheme is,
Zariski-locally on the base, isomorphic to one of these. Over a local ring, the only open
neighbourhood of the closed point is the whole spectrum, so every elliptic curve over a local ring
is globally isomorphic to one of these (`exists_iso_toEllipticCurveGeom`).

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
* `WeierstrassCurve.j_toEllipticCurveGeom`: the `j`-invariant of `toEllipticCurveGeom W` is the
  `j`-invariant `W.j` of the equation.
* `WeierstrassCurve.isPullback_toEllipticCurveGeomIso_hom_projModelBaseChange`: the elliptic curve
  of `W.map φ` is a base change of that of `W` along `Spec φ`, through the base change morphism of
  projective models.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_iso_toEllipticCurveGeom`: every elliptic curve
  over a local ring `R` is isomorphic, over `Spec R` and compatibly with the zero sections, to
  `toEllipticCurveGeom W` for an elliptic Weierstrass curve `W` over `R`.

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

/-- Under `(toEllipticCurveGeomIso W).inv`, the structure morphism is `W.projModelOver`. -/
@[reassoc (attr := simp)]
theorem toEllipticCurveGeomIso_inv_structureMap :
    (toEllipticCurveGeomIso W).inv ≫ (toEllipticCurveGeom W).structureMap = W.projModelOver :=
  (Iso.inv_comp_eq _).mpr (toEllipticCurveGeomIso_hom_projModelOver W).symm

/-- Under `(toEllipticCurveGeomIso W).inv`, `W.projModelZero` maps to
`(toEllipticCurveGeom W).zero`. -/
@[reassoc (attr := simp)]
theorem projModelZero_toEllipticCurveGeomIso_inv :
    W.projModelZero ≫ (toEllipticCurveGeomIso W).inv = (toEllipticCurveGeom W).zero :=
  (Iso.comp_inv_eq _).mpr (zero_toEllipticCurveGeomIso_hom W).symm

/-- A section missing zero everywhere maps under `(toEllipticCurveGeomIso W).hom` to one missing
`W.projModelZero` everywhere. -/
theorem comp_toEllipticCurveGeomIso_hom_ne_projModelZero
    {P : Spec (.of R) ⟶ (toEllipticCurveGeom W).carrier}
    (hP₀ : ∀ s, P s ≠ (toEllipticCurveGeom W).zero s) (s : Spec (.of R)) :
    (P ≫ (toEllipticCurveGeomIso W).hom) s ≠ W.projModelZero s := fun hs ↦ hP₀ s <| by
  have h1 := congrArg (toEllipticCurveGeomIso W).inv hs
  rwa [← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← Scheme.Hom.comp_apply, projModelZero_toEllipticCurveGeomIso_inv] at h1

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

/-- The tautological pointed Weierstrass chart of `toEllipticCurveGeom W` over `Spec R`. -/
noncomputable abbrev toEllipticCurveGeomChart :
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

/-- On `toEllipticCurveGeomChart W`, `modelPoint hP = P ≫ (toEllipticCurveGeomIso W).hom`. -/
theorem toEllipticCurveGeomChart_modelPoint {P : Spec (.of R) ⟶ (toEllipticCurveGeom W).carrier}
    (hP : P ≫ (toEllipticCurveGeom W).structureMap = 𝟙 _) :
    (toEllipticCurveGeomChart W).modelPoint hP = P ≫ (toEllipticCurveGeomIso W).hom :=
  (toEllipticCurveGeomChart W).isPullback_modelIso_inv_toTotal.hom_ext
    (by rw [PointedWeierstrassChart.modelPoint_modelIso_inv_toTotal]
        simp [toEllipticCurveGeomChart])
    (by rw [PointedWeierstrassChart.modelPoint_projModelOver, Category.assoc,
          toEllipticCurveGeomIso_hom_projModelOver, hP])

/-- Under `toEllipticCurveGeomIso`, the addition morphism of `toEllipticCurveGeom W` is the
Bosma–Lenstra addition morphism of `W`. -/
@[reassoc (attr := simp)]
theorem addition_toEllipticCurveGeomIso_hom :
    (toEllipticCurveGeom W).addition ≫ (toEllipticCurveGeomIso W).hom =
      pullback.map _ _ _ _ (toEllipticCurveGeomIso W).hom (toEllipticCurveGeomIso W).hom (𝟙 _)
        (by simp) (by simp) ≫ W.additionMorphism := by
  -- on the chart `chart W` over the whole base, whose inclusion into the curve is the identity,
  -- the addition morphism is the addition of `W` transported along `toEllipticCurveGeomIso W`
  have h := (toEllipticCurveGeom W).pullbackMap_addition (toEllipticCurveGeomChart W)
  have h2 := (toEllipticCurveGeomChart W).addition_modelIso_hom
  dsimp only [toEllipticCurveGeomChart] at h h2
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
  have h := (toEllipticCurveGeom W).toTotal_neg (toEllipticCurveGeomChart W)
  have h2 := (toEllipticCurveGeomChart W).neg_modelIso_hom
  dsimp only [toEllipticCurveGeomChart] at h h2
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

/-! ### The `j`-invariant -/

/-- **The `j`-invariant of a Weierstrass model.** The `j`-invariant of the elliptic curve
`toEllipticCurveGeom W` over `Spec R` is the `j`-invariant `W.j` of the equation, as a global
function on `Spec R`. -/
@[simp]
theorem j_toEllipticCurveGeom :
    (toEllipticCurveGeom W).j = (Scheme.ΓSpecIso (.of R)).inv W.j := by
  have h : Scheme.Hom.appTop (𝟙 (Spec (.of R))) (toEllipticCurveGeom W).j =
      Scheme.Hom.appTop (Iso.refl (Spec (.of R))).hom ((Scheme.ΓSpecIso (.of R)).inv W.j) :=
    (toEllipticCurveGeom W).baseMap_appTop_j (toEllipticCurveGeomChart W)
  simpa using h

/-! ### Base change along a ring homomorphism -/

variable {R' : Type u} [CommRing R'] (φ : R →+* R')

-- The projective model of `W.map φ` is a pullback of the structure morphism of
-- `toEllipticCurveGeom W` along `Spec φ`.
private theorem isPullback_projModelBaseChange_comp_toEllipticCurveGeomIso_inv :
    IsPullback (W.projModelBaseChange φ ≫ (toEllipticCurveGeomIso W).inv) (W.map φ).projModelOver
      (toEllipticCurveGeom W).structureMap (Spec.map (CommRingCat.ofHom φ)) :=
  (W.isPullback_projModelBaseChange φ).of_iso (.refl _) (toEllipticCurveGeomIso W).symm (.refl _)
    (.refl _) (by simp) (by simp) (by simp) (by simp)

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

/-- **The elliptic curve of `W.map φ` is a base change of that of `W`.** The base change morphism
`W.projModelBaseChange φ`, read on the total spaces of `toEllipticCurveGeom (W.map φ)` and
`toEllipticCurveGeom W`, forms a pullback square with the two structure morphisms and
`Spec φ : Spec R' ⟶ Spec R`. -/
theorem isPullback_toEllipticCurveGeomIso_hom_projModelBaseChange :
    IsPullback ((toEllipticCurveGeomIso (W.map φ)).hom ≫ W.projModelBaseChange φ ≫
        (toEllipticCurveGeomIso W).inv) (toEllipticCurveGeom (W.map φ)).structureMap
      (toEllipticCurveGeom W).structureMap (Spec.map (CommRingCat.ofHom φ)) :=
  (isPullback_projModelBaseChange_comp_toEllipticCurveGeomIso_inv W φ).of_iso
    (toEllipticCurveGeomIso _).symm (.refl _) (.refl _) (.refl _) (by simp)
    (by simp) (by simp) (by simp)

/-- The base change morphism from `toEllipticCurveGeom (W.map φ)` to `toEllipticCurveGeom W`
carries the zero section of the former to that of the latter. -/
@[reassoc]
theorem zero_toEllipticCurveGeomIso_hom_projModelBaseChange :
    (toEllipticCurveGeom (W.map φ)).zero ≫ (toEllipticCurveGeomIso (W.map φ)).hom ≫
        W.projModelBaseChange φ ≫ (toEllipticCurveGeomIso W).inv =
      Spec.map (CommRingCat.ofHom φ) ≫ (toEllipticCurveGeom W).zero := by
  rw [← cancel_mono (toEllipticCurveGeomIso W).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_toEllipticCurveGeomIso_hom,
    zero_toEllipticCurveGeomIso_hom_assoc, projModelZero_projModelBaseChange]

end WeierstrassCurve

/-! ### Elliptic curves over a local ring -/

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {R : Type u} [CommRing R] [IsLocalRing R] (E : EllipticCurveGeom (Spec (.of R)))

/-- **An elliptic curve over a local ring is the projective model of a Weierstrass equation.** For
an elliptic curve `E` over `Spec R`, with `R` a local ring, there are an elliptic Weierstrass curve
`W` over `R` and an isomorphism of the total space of `toEllipticCurveGeom W` with that of `E` over
`Spec R`, carrying the zero section `[0 : 1 : 0]` to the zero section of `E`. -/
theorem exists_iso_toEllipticCurveGeom :
    ∃ (W : WeierstrassCurve R) (_ : W.IsElliptic)
      (e : W.toEllipticCurveGeom.carrier ≅ E.carrier),
      e.hom ≫ E.structureMap = W.toEllipticCurveGeom.structureMap ∧
        W.toEllipticCurveGeom.zero ≫ e.hom = E.zero := by
  obtain ⟨A⟩ := E.localModel
  obtain ⟨i, x, hx⟩ := A.covers (IsLocalRing.closedPoint R)
  let c := A.chart i
  -- the base of a chart through the closed point of `Spec R` is an open neighbourhood of the closed
  -- point, hence all of `Spec R`, and the chart is all of `E`
  have : IsIso c.baseMap := (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨inferInstance, ⟨fun s ↦ ((IsLocalRing.specializes_closedPoint s).mem_open
      c.baseMap.isOpenEmbedding.isOpen_range ⟨x, hx⟩)⟩⟩
  have : IsIso c.toTotal := c.isPullback.isIso_fst_of_isIso
  -- the coefficient ring of the chart is identified with `R` by `ψ`, and `W` is the equation of
  -- the chart with its coefficients moved along `ψ`
  let ψ : c.ring ⟶ .of R := Spec.preimage (inv (c.baseIso.inv ≫ c.baseMap))
  have hψ : Spec.map ψ = inv (c.baseIso.inv ≫ c.baseMap) := Spec.map_preimage _
  have : IsIso (c.equation.projModelBaseChange ψ.hom) := by
    have := c.equation.isPullback_projModelBaseChange ψ.hom
    rw [CommRingCat.ofHom_hom, hψ] at this
    exact this.isIso_fst_of_isIso
  refine ⟨c.equation.map ψ.hom, inferInstance,
    asIso ((WeierstrassCurve.toEllipticCurveGeomIso _).hom ≫
      c.equation.projModelBaseChange ψ.hom ≫ c.modelIso.inv ≫ c.toTotal), ?_, ?_⟩
  · have h : c.modelIso.inv ≫ c.toBase = c.equation.projModelOver ≫ c.baseIso.inv := by
      rw [Iso.inv_comp_eq, c.modelIso_over_assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [asIso_hom, Category.assoc, c.isPullback.w, reassoc_of% h]
    rw [(c.equation.isPullback_projModelBaseChange ψ.hom).w_assoc]
    simp [hψ]
  · have h : c.equation.projModelZero ≫ c.modelIso.inv = c.baseIso.inv ≫ c.pulledZero := by
      rw [Iso.comp_inv_eq, Category.assoc, c.modelIso_zero, Iso.inv_hom_id_assoc]
    simp [WeierstrassCurve.projModelZero_projModelBaseChange_assoc, reassoc_of% h, hψ]

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
