/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange

/-!
# Elliptic curves over a scheme

An elliptic curve over a scheme `S` is recorded here as a geometric object: a smooth proper morphism
`X ⟶ S` of relative dimension one with a section, which Zariski-locally on `S` is the projective
Weierstrass model `WeierstrassCurve.projModel` of an elliptic Weierstrass curve, compatibly with the
structure morphisms and with the zero section `[0 : 1 : 0]`.

The local-model condition is given in two forms. A pointed Weierstrass chart of `π : X ⟶ S`
pointed by `zero : S ⟶ X` consists of an open immersion `base ⟶ S` from a scheme isomorphic to
`Spec R`, an elliptic Weierstrass curve `W` over `R`, a pullback square of `π` along the open
immersion, and an isomorphism of its apex with `projModel W` over `Spec R` carrying the section
induced by `zero` to the zero section; a pointed Weierstrass atlas is a family of charts whose
images cover `S`. The predicate `IsLocallyWeierstrass` states the condition pointwise instead, on
affine opens `U` of `S` with Weierstrass curves over `Γ(S, U)` and the chosen pullback of `π` along
`U ⟶ S`. The two forms agree: `nonempty_pointedWeierstrassAtlas_iff`.

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart π zero`: a pointed Weierstrass chart of `π`
  with section `zero`.
* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.ofAffineOpen`: the pointed Weierstrass chart
  on an affine open of the base given by the data of the local-model condition there.
* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.restrict c V`: the restriction of a chart to
  an affine open `V` of its base, with equation the coefficient extension of the equation of `c`
  to `Γ(base, V)`; its base is included in that of `c` by `restrictι`.
* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.pullbackCarrierMap`: the morphism between the
  restrictions of the curve to the bases of two charts induced by a morphism of bases over `S`, a
  base change square (`isPullback_pullbackCarrierMap`); `projModelMap` is the same morphism between
  the projective models of the equations of the two charts.
* `TauCeti.AlgebraicGeometry.PointedWeierstrassAtlas π zero`: a family of pointed Weierstrass
  charts whose images cover the base.
* `TauCeti.AlgebraicGeometry.IsLocallyWeierstrass π zero hzero`: every point of the base has an
  affine open neighbourhood over which `π` is the projective model of an elliptic Weierstrass
  curve, compatibly with the section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom S`: an elliptic curve over `S`, a smooth proper
  morphism of relative dimension one with a section admitting a pointed Weierstrass atlas.

## Main results

* `TauCeti.AlgebraicGeometry.isLocallyWeierstrass_iff`: the local-model condition in terms of
  affine opens, Weierstrass curves and isomorphisms with projective models.
* `TauCeti.AlgebraicGeometry.PointedWeierstrassAtlas.isLocallyWeierstrass`: a pointed Weierstrass
  atlas gives the local-model condition.
* `TauCeti.AlgebraicGeometry.nonempty_pointedWeierstrassAtlas_iff`: a pointed Weierstrass atlas
  exists if and only if the local-model condition holds.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isLocallyWeierstrass`: an elliptic curve over `S`
  satisfies the local-model condition.

## Implementation notes

The coefficient ring of a chart is only isomorphic to the ring of sections over the image of its
base. Comparing a chart with the local-model condition therefore moves its Weierstrass curve along
a ring isomorphism `φ` with `WeierstrassCurve.map`, and identifies `projModel (W.map φ)` with
`projModel W` by `WeierstrassCurve.projModelMapIso`, the base change morphism along `φ`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.

## Provenance

`IsLocallyWeierstrass` and `EllipticCurveGeom` are adapted from AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/Basic.lean`, declarations
`ModularCurves.LocallyWeierstrass` and `ModularCurves.EllipticCurveGeom`. Here the projective model
is `WeierstrassCurve.projModel`, and the local model of `EllipticCurveGeom` is a nonempty pointed
Weierstrass atlas, which is equivalent to `IsLocallyWeierstrass` by
`nonempty_pointedWeierstrassAtlas_iff`.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-! ### Pointed Weierstrass charts and atlases -/

/-- A **pointed Weierstrass chart** of a morphism `π : X ⟶ S` pointed by `zero : S ⟶ X`: an open
immersion `baseMap : base ⟶ S` from a scheme `base ≅ Spec ring`, an elliptic Weierstrass curve
`equation` over `ring`, a pullback square of `π` along `baseMap` with apex `pullbackCarrier`, and an
isomorphism `modelIso` of `pullbackCarrier` with the projective model of `equation`, lying over
`Spec ring` and carrying the section `pulledZero` induced by `zero` to the zero section
`[0 : 1 : 0]`. A chart presents `X` over the open subscheme of `S` that is the image of `baseMap`,
and its fields make `zero` a section of `π` over that image. -/
structure PointedWeierstrassChart {S X : Scheme.{u}} (π : X ⟶ S) (zero : S ⟶ X) where
  /-- The base of the chart. -/
  base : Scheme.{u}
  /-- The inclusion of the base of the chart into `S`. -/
  baseMap : base ⟶ S
  /-- The base of the chart is an open subscheme of `S`. -/
  baseMap_open : IsOpenImmersion baseMap
  /-- The coefficient ring of the chart. -/
  ring : CommRingCat.{u}
  /-- An isomorphism of the base of the chart with the spectrum of its coefficient ring. -/
  baseIso : base ≅ Spec ring
  /-- The Weierstrass equation of the chart. -/
  equation : WeierstrassCurve ring
  /-- The Weierstrass equation of the chart is elliptic. -/
  equation_elliptic : equation.IsElliptic
  /-- The restriction of `X` to the base of the chart. -/
  pullbackCarrier : Scheme.{u}
  /-- The inclusion of the restriction into `X`, the base change of `baseMap` along `π`. -/
  toTotal : pullbackCarrier ⟶ X
  /-- The structure morphism of the restriction. -/
  toBase : pullbackCarrier ⟶ base
  /-- The restriction is the pullback of `π` along `baseMap`. -/
  isPullback : IsPullback toTotal toBase π baseMap
  /-- An isomorphism of the restriction with the projective model of the equation. -/
  modelIso : pullbackCarrier ≅ equation.projModel
  /-- The isomorphism with the projective model lies over `Spec ring`. -/
  modelIso_over : modelIso.hom ≫ equation.projModelOver = toBase ≫ baseIso.hom
  /-- The section of the restriction induced by `zero`. -/
  pulledZero : base ⟶ pullbackCarrier
  /-- `pulledZero` is a section of the structure morphism of the restriction. -/
  pulledZero_toBase : pulledZero ≫ toBase = 𝟙 base
  /-- `pulledZero` lifts the restriction `baseMap ≫ zero` of `zero` along `toTotal`. -/
  pulledZero_toTotal : pulledZero ≫ toTotal = baseMap ≫ zero
  /-- The isomorphism with the projective model carries `pulledZero` to the zero section. -/
  modelIso_zero : pulledZero ≫ modelIso.hom = baseIso.hom ≫ equation.projModelZero

attribute [instance] PointedWeierstrassChart.baseMap_open PointedWeierstrassChart.equation_elliptic

attribute [reassoc (attr := simp)] PointedWeierstrassChart.modelIso_over
  PointedWeierstrassChart.pulledZero_toBase PointedWeierstrassChart.pulledZero_toTotal
  PointedWeierstrassChart.modelIso_zero

/-- A **pointed Weierstrass atlas** of a morphism `π : X ⟶ S` pointed by `zero : S ⟶ X`: a family
of pointed Weierstrass charts whose images cover `S`. The images are open, so an atlas exhibits `π`
Zariski-locally on `S` as the projective model of an elliptic Weierstrass curve with `zero` as its
zero section. -/
structure PointedWeierstrassAtlas {S X : Scheme.{u}} (π : X ⟶ S) (zero : S ⟶ X) where
  /-- The index type of the charts. -/
  index : Type u
  /-- The charts. -/
  chart : index → PointedWeierstrassChart π zero
  /-- The images of the charts cover `S`. -/
  covers : ∀ s : S, ∃ i : index, ∃ x : (chart i).base, (chart i).baseMap.base x = s

/-- **The local-model condition** for a morphism `π : X ⟶ S` with a section `zero`: every point of
`S` has an affine open neighbourhood `U` with an elliptic Weierstrass curve `W` over `Γ(S, U)` and
an isomorphism of the restriction `pullback π U.ι` of `X` to `U` with the projective model of `W`,
lying over `U ≅ Spec Γ(S, U)` and carrying the section induced by `zero` to the zero section of the
model. It holds if and only if a `PointedWeierstrassAtlas` exists:
`nonempty_pointedWeierstrassAtlas_iff`. -/
def IsLocallyWeierstrass {X S : Scheme.{u}} (π : X ⟶ S) (zero : S ⟶ X)
    (hzero : zero ≫ π = 𝟙 S) : Prop :=
  ∀ s : S, ∃ (U : S.affineOpens) (_ : s ∈ U.1) (W : WeierstrassCurve Γ(S, U.1)),
    W.IsElliptic ∧
      ∃ e : pullback π U.1.ι ≅ W.projModel,
        e.hom ≫ W.projModelOver = pullback.snd π U.1.ι ≫ U.2.isoSpec.hom ∧
        (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ zero) (𝟙 _)
            (by rw [Category.assoc, hzero, Category.comp_id, Category.id_comp])) ≫ e.hom =
          W.projModelZero

/-- The local-model condition `IsLocallyWeierstrass π zero hzero` holds if and only if every point
of `S` has an affine open neighbourhood `U` with an elliptic Weierstrass curve `W` over `Γ(S, U)`
and an isomorphism of `pullback π U.ι` with the projective model of `W`, lying over
`U ≅ Spec Γ(S, U)` and carrying the section induced by `zero` to the zero section of the model. -/
theorem isLocallyWeierstrass_iff {X S : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}
    (hzero : zero ≫ π = 𝟙 S) :
    IsLocallyWeierstrass π zero hzero ↔
      ∀ s : S, ∃ (U : S.affineOpens) (_ : s ∈ U.1) (W : WeierstrassCurve Γ(S, U.1)),
        W.IsElliptic ∧
          ∃ e : pullback π U.1.ι ≅ W.projModel,
            e.hom ≫ W.projModelOver = pullback.snd π U.1.ι ≫ U.2.isoSpec.hom ∧
            (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ zero) (𝟙 _)
                (by rw [Category.assoc, hzero, Category.comp_id, Category.id_comp])) ≫ e.hom =
              W.projModelZero :=
  Iff.rfl

namespace PointedWeierstrassChart

variable {S X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}

/-- The base of a pointed Weierstrass chart is affine: it is isomorphic to `Spec ring`. -/
instance isAffine_base (c : PointedWeierstrassChart π zero) : IsAffine c.base :=
  .of_isIso c.baseIso.hom

section Range

variable (c : PointedWeierstrassChart π zero)

-- `Spec` of the sections over the image `U` of the chart is `Spec ring`, through `U ≅ base`.
private noncomputable def rangeSpecIso : Spec Γ(S, c.baseMap.opensRange) ≅ Spec c.ring :=
  (isAffineOpen_opensRange c.baseMap).isoSpec.symm ≪≫ c.baseMap.isoOpensRange.symm ≪≫ c.baseIso

-- The ring isomorphism whose `Spec` is `rangeSpecIso`. Without `(Y := .op _)` the unifier cannot
-- match `Spec c.ring` with `Scheme.Spec.obj ?Y`.
private noncomputable def rangeRingEquiv : c.ring ≃+* Γ(S, c.baseMap.opensRange) :=
  (Spec.fullyFaithful.preimageIso (Y := .op _) c.rangeSpecIso).unop.commRingCatIsoToRingEquiv

-- `Spec` of the inverse of `rangeRingEquiv` is the inverse of `rangeSpecIso`; `(X := .op _)` is
-- needed for the same reason as in `rangeRingEquiv`.
private theorem specMap_rangeRingEquiv_symm :
    Spec.map (CommRingCat.ofHom (c.rangeRingEquiv.symm : Γ(S, _) →+* c.ring)) =
      c.rangeSpecIso.inv :=
  Spec.fullyFaithful.map_preimage (X := .op _) _

private theorem isPullback_opensRange :
    IsPullback c.toTotal (c.toBase ≫ c.baseMap.isoOpensRange.hom) π c.baseMap.opensRange.ι := by
  apply c.isPullback.of_iso (.refl _) (.refl _) c.baseMap.isoOpensRange (.refl _) <;> simp

-- The restriction of `X` to the image of the chart is the projective model of the transported
-- equation.
private noncomputable def rangeModelIso : pullback π c.baseMap.opensRange.ι ≅
    (c.equation.map (c.rangeRingEquiv : c.ring →+* Γ(S, c.baseMap.opensRange))).projModel :=
  c.isPullback_opensRange.isoPullback.symm ≪≫ c.modelIso ≪≫ (c.equation.projModelMapIso _).symm

private theorem rangeModelIso_hom_projModelOver :
    c.rangeModelIso.hom ≫
        (c.equation.map (c.rangeRingEquiv : c.ring →+* Γ(S, c.baseMap.opensRange))).projModelOver =
      pullback.snd π c.baseMap.opensRange.ι ≫ (isAffineOpen_opensRange c.baseMap).isoSpec.hom := by
  -- precomposed with `isoPullback`, this is `modelIso_over` read through `rangeSpecIso`
  rw [← cancel_epi c.isPullback_opensRange.isoPullback.hom]
  simp [rangeModelIso, specMap_rangeRingEquiv_symm, rangeSpecIso]

private theorem lift_rangeModelIso_hom (hzero : zero ≫ π = 𝟙 S) :
    ((isAffineOpen_opensRange c.baseMap).isoSpec.inv ≫
        pullback.lift (c.baseMap.opensRange.ι ≫ zero) (𝟙 _) (by simp [hzero])) ≫
        c.rangeModelIso.hom =
      (c.equation.map
        (c.rangeRingEquiv : c.ring →+* Γ(S, c.baseMap.opensRange))).projModelZero := by
  -- the section induced by `zero` is `pulledZero`, along `isoOpensRange` and `isoPullback`
  have hL : pullback.lift (c.baseMap.opensRange.ι ≫ zero) (𝟙 _) (by simp [hzero]) =
      c.baseMap.isoOpensRange.inv ≫ c.pulledZero ≫ c.isPullback_opensRange.isoPullback.hom :=
    pullback.hom_ext (by simp) (by simp)
  -- then `modelIso_zero` and the inverse of `projModelMapIso` conclude, through `rangeSpecIso`
  simp [hL, rangeModelIso, specMap_rangeRingEquiv_symm, rangeSpecIso]

end Range

/-- The pointed Weierstrass chart on an affine open `U` of `S` given by an elliptic Weierstrass
curve `W` over `Γ(S, U)` and an isomorphism `e` of the chosen pullback `pullback π U.ι` with the
projective model of `W`, lying over `U ≅ Spec Γ(S, U)` and carrying the section induced by `zero` to
the zero section. Its base is `U`, its coefficient ring is `Γ(S, U)` and its section is
`pullback.lift (U.ι ≫ zero) (𝟙 U)`. -/
noncomputable def ofAffineOpen (hzero : zero ≫ π = 𝟙 S) (U : S.affineOpens)
    (W : WeierstrassCurve Γ(S, U.1)) (hW : W.IsElliptic) (e : pullback π U.1.ι ≅ W.projModel)
    (hover : e.hom ≫ W.projModelOver = pullback.snd π U.1.ι ≫ U.2.isoSpec.hom)
    (hzero' : (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ zero) (𝟙 _) (by simp [hzero])) ≫ e.hom =
      W.projModelZero) : PointedWeierstrassChart π zero where
  base := U.1
  baseMap := U.1.ι
  baseMap_open := inferInstance
  ring := Γ(S, U.1)
  baseIso := U.2.isoSpec
  equation := W
  equation_elliptic := hW
  pullbackCarrier := pullback π U.1.ι
  toTotal := pullback.fst π U.1.ι
  toBase := pullback.snd π U.1.ι
  isPullback := .of_hasPullback π U.1.ι
  modelIso := e
  modelIso_over := hover
  pulledZero := pullback.lift (U.1.ι ≫ zero) (𝟙 _) (by simp [hzero])
  pulledZero_toBase := pullback.lift_snd _ _ _
  pulledZero_toTotal := pullback.lift_fst _ _ _
  modelIso_zero := by simp [← hzero']

section Restrict

variable (c : PointedWeierstrassChart π zero) (V : c.base.affineOpens)

-- The ring homomorphism whose `Spec` is the inclusion of `V` into the base of the chart, read
-- through `V ≅ Spec Γ(base, V)` and `base ≅ Spec ring`.
private noncomputable def restrictRingHom : c.ring ⟶ Γ(c.base, V.1) :=
  Spec.preimage (V.2.isoSpec.inv ≫ V.1.ι ≫ c.baseIso.hom)

private theorem specMap_restrictRingHom :
    Spec.map (c.restrictRingHom V) = V.2.isoSpec.inv ≫ V.1.ι ≫ c.baseIso.hom :=
  Spec.map_preimage _

-- Over `V`, the chart is the base change of the projective model along
-- `Spec Γ(base, V) ⟶ Spec ring`.
private theorem isPullback_restrict :
    IsPullback (pullback.fst c.toBase V.1.ι ≫ c.modelIso.hom)
      (pullback.snd c.toBase V.1.ι ≫ V.2.isoSpec.hom) c.equation.projModelOver
      (Spec.map (CommRingCat.ofHom (c.restrictRingHom V).hom)) := by
  refine (IsPullback.of_hasPullback c.toBase V.1.ι).of_iso (.refl _) c.modelIso V.2.isoSpec
    c.baseIso ?_ ?_ ?_ ?_ <;> simp [specMap_restrictRingHom]

-- Over `V`, the chart is the projective model of the coefficient extension of its equation.
private noncomputable def restrictModelIso :
    pullback c.toBase V.1.ι ≅ (c.equation.map (c.restrictRingHom V).hom).projModel :=
  (c.isPullback_restrict V).isoIsPullback _ _ (c.equation.isPullback_projModelBaseChange _)

private theorem restrictModelIso_hom_projModelOver :
    (c.restrictModelIso V).hom ≫ (c.equation.map (c.restrictRingHom V).hom).projModelOver =
      pullback.snd c.toBase V.1.ι ≫ V.2.isoSpec.hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

private theorem restrictModelIso_hom_projModelBaseChange :
    (c.restrictModelIso V).hom ≫ c.equation.projModelBaseChange (c.restrictRingHom V).hom =
      pullback.fst c.toBase V.1.ι ≫ c.modelIso.hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The **restriction** of a pointed Weierstrass chart `c` to an affine open `V` of its base: the
chart with base `V`, coefficient ring `Γ(base, V)` and, as equation, the coefficient extension of
the equation of `c` along `ring ⟶ Γ(base, V)`. Its base is included in that of `c` by
`restrictι`. -/
noncomputable def restrict : PointedWeierstrassChart π zero where
  base := V.1
  baseMap := V.1.ι ≫ c.baseMap
  baseMap_open := inferInstance
  ring := Γ(c.base, V.1)
  baseIso := V.2.isoSpec
  equation := c.equation.map (c.restrictRingHom V).hom
  equation_elliptic := inferInstance
  pullbackCarrier := pullback c.toBase V.1.ι
  toTotal := pullback.fst c.toBase V.1.ι ≫ c.toTotal
  toBase := pullback.snd c.toBase V.1.ι
  isPullback := (IsPullback.of_hasPullback c.toBase V.1.ι).paste_horiz c.isPullback
  modelIso := c.restrictModelIso V
  modelIso_over := c.restrictModelIso_hom_projModelOver V
  pulledZero := pullback.lift (V.1.ι ≫ c.pulledZero) (𝟙 _) (by simp)
  pulledZero_toBase := pullback.lift_snd _ _ _
  pulledZero_toTotal := by simp
  modelIso_zero := by
    -- compare the two sides through the base change square of the projective model
    refine (c.equation.isPullback_projModelBaseChange _).hom_ext ?_ ?_
    · simp [restrictModelIso_hom_projModelBaseChange,
        WeierstrassCurve.projModelZero_projModelBaseChange, specMap_restrictRingHom]
    · -- `𝟙 (Spec Γ(base, V))` is stated with `CommRingCat.of`, out of reach of `comp_id`
      simp only [Category.assoc, restrictModelIso_hom_projModelOver, pullback.lift_snd_assoc,
        Category.id_comp, WeierstrassCurve.projModelZero_projModelOver]
      exact (Category.comp_id _).symm

/-- The inclusion of the base of the restriction `c.restrict V` into the base of `c`, an open
immersion with image `V` (`opensRange_restrictι`). -/
noncomputable def restrictι : (c.restrict V).base ⟶ c.base :=
  V.1.ι

instance : IsOpenImmersion (c.restrictι V) :=
  inferInstanceAs (IsOpenImmersion V.1.ι)

/-- The base of the restriction `c.restrict V` lies over the base of `c`. -/
@[reassoc (attr := simp)]
theorem restrictι_baseMap : c.restrictι V ≫ c.baseMap = (c.restrict V).baseMap :=
  (rfl)

/-- The image of the base of the restriction `c.restrict V` in the base of `c` is `V`. -/
@[simp]
theorem opensRange_restrictι : (c.restrictι V).opensRange = V.1 :=
  V.1.opensRange_ι

/-- The image of the base of the restriction `c.restrict V` in the base of `c` is `V`, as a set of
points. -/
@[simp]
theorem range_restrictι : Set.range (c.restrictι V) = V.1 :=
  V.1.range_ι

end Restrict

section Map

variable {k c : PointedWeierstrassChart π zero} {h : k.base ⟶ c.base}

/-- The morphism from the restriction of the curve to the base of a chart `k` to its restriction to
the base of a chart `c`, induced by a morphism `h` of bases over `S`. -/
noncomputable def pullbackCarrierMap (hh : h ≫ c.baseMap = k.baseMap) :
    k.pullbackCarrier ⟶ c.pullbackCarrier :=
  c.isPullback.lift k.toTotal (k.toBase ≫ h) (by rw [Category.assoc, hh, k.isPullback.w])

variable (hh : h ≫ c.baseMap = k.baseMap)

/-- The morphism `pullbackCarrierMap` lies over the inclusions into the curve. -/
@[reassoc (attr := simp)]
theorem pullbackCarrierMap_toTotal : pullbackCarrierMap hh ≫ c.toTotal = k.toTotal :=
  IsPullback.lift_fst _ _ _ _

/-- The morphism `pullbackCarrierMap` lies over the morphism of bases. -/
@[reassoc (attr := simp)]
theorem pullbackCarrierMap_toBase : pullbackCarrierMap hh ≫ c.toBase = k.toBase ≫ h :=
  IsPullback.lift_snd _ _ _ _

/-- The restriction of the curve to the base of `k` is the base change along `h` of its
restriction to the base of `c`. -/
theorem isPullback_pullbackCarrierMap : IsPullback (pullbackCarrierMap hh) k.toBase c.toBase h :=
  .of_right (by simpa [hh] using k.isPullback) (pullbackCarrierMap_toBase hh) c.isPullback

/-- The morphism `pullbackCarrierMap` carries the section induced by the zero section to the section
induced by the zero section. -/
@[reassoc (attr := simp)]
theorem pulledZero_pullbackCarrierMap : k.pulledZero ≫ pullbackCarrierMap hh = h ≫ c.pulledZero :=
  c.isPullback.hom_ext (by simp [reassoc_of% hh]) (by simp)

/-- The morphism between the projective models of the equations of two charts `k` and `c` induced
by a morphism `h` of bases over `S`: `pullbackCarrierMap hh`, read through the isomorphisms of the
restrictions of the curve with the projective models (`modelIso_hom_projModelMap`). It lies over
`Spec k.ring ≅ k.base ⟶ c.base ≅ Spec c.ring`, as a base change square
(`isPullback_projModelMap`), and carries the zero section to the zero section
(`projModelZero_projModelMap`). -/
noncomputable def projModelMap : k.equation.projModel ⟶ c.equation.projModel :=
  k.modelIso.inv ≫ pullbackCarrierMap hh ≫ c.modelIso.hom

/-- Through the isomorphisms with the projective models, `projModelMap hh` is
`pullbackCarrierMap hh`. -/
@[reassoc (attr := simp)]
theorem modelIso_hom_projModelMap :
    k.modelIso.hom ≫ projModelMap hh = pullbackCarrierMap hh ≫ c.modelIso.hom := by
  simp [projModelMap]

/-- The projective model of the equation of `k` is the base change of that of `c` along
`Spec k.ring ≅ k.base ⟶ c.base ≅ Spec c.ring`, through `projModelMap hh`. -/
theorem isPullback_projModelMap : IsPullback (projModelMap hh) k.equation.projModelOver
    c.equation.projModelOver (k.baseIso.inv ≫ h ≫ c.baseIso.hom) :=
  (isPullback_pullbackCarrierMap hh).of_iso k.modelIso c.modelIso k.baseIso c.baseIso
    (by simp) k.modelIso_over.symm c.modelIso_over.symm (by simp)

/-- The morphism `projModelMap hh` carries the zero section to the zero section. -/
@[reassoc (attr := simp)]
theorem projModelZero_projModelMap : k.equation.projModelZero ≫ projModelMap hh =
    (k.baseIso.inv ≫ h ≫ c.baseIso.hom) ≫ c.equation.projModelZero := by
  rw [← cancel_epi k.baseIso.hom, ← k.modelIso_zero_assoc]
  simp

end Map

end PointedWeierstrassChart

/-- A morphism `π` with a section `zero` that admits a pointed Weierstrass atlas satisfies the
local-model condition `IsLocallyWeierstrass π zero hzero`. The converse also holds:
`nonempty_pointedWeierstrassAtlas_iff`. -/
theorem PointedWeierstrassAtlas.isLocallyWeierstrass {X S : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}
    (hzero : zero ≫ π = 𝟙 S) (A : PointedWeierstrassAtlas π zero) :
    IsLocallyWeierstrass π zero hzero := (isLocallyWeierstrass_iff hzero).mpr fun s ↦ by
  obtain ⟨i, x, rfl⟩ := A.covers s
  -- `U` is the image of the chart, and the equation moves to `Γ(S, U)` along `ring ≅ Γ(S, U)`
  exact ⟨⟨_, isAffineOpen_opensRange (A.chart i).baseMap⟩, ⟨x, rfl⟩, _, inferInstance,
    (A.chart i).rangeModelIso, (A.chart i).rangeModelIso_hom_projModelOver,
    (A.chart i).lift_rangeModelIso_hom hzero⟩

/-- A morphism with a section admits a pointed Weierstrass atlas if and only if it satisfies the
local-model condition `IsLocallyWeierstrass`. -/
theorem nonempty_pointedWeierstrassAtlas_iff {X S : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}
    (hzero : zero ≫ π = 𝟙 S) :
    Nonempty (PointedWeierstrassAtlas π zero) ↔ IsLocallyWeierstrass π zero hzero := by
  refine ⟨fun ⟨A⟩ ↦ A.isLocallyWeierstrass hzero, fun h ↦ ?_⟩
  choose U hU W hW e hover hzero' using (isLocallyWeierstrass_iff hzero).mp h
  exact ⟨{
    index := S
    chart s := .ofAffineOpen hzero (U s) (W s) (hW s) (e s) (hover s) (hzero' s)
    covers s := ⟨s, ⟨s, hU s⟩, rfl⟩ }⟩

/-! ### Elliptic curves over a scheme -/

/-- An **elliptic curve over a scheme** `S`, as a geometric object: a morphism
`structureMap : carrier ⟶ S`, smooth of relative dimension one and proper, with a section `zero`,
such that `structureMap` and `zero` admit a pointed Weierstrass atlas, so that Zariski-locally on
`S` the curve is the projective model of an elliptic Weierstrass curve with `zero` the zero section
`[0 : 1 : 0]`. The atlas appears under `Nonempty`, so no local equation is part of the data. -/
structure EllipticCurveGeom (S : Scheme.{u}) where
  /-- The total space. -/
  carrier : Scheme.{u}
  /-- The structure morphism. -/
  structureMap : carrier ⟶ S
  /-- The zero section. -/
  zero : S ⟶ carrier
  /-- The zero section is a section of the structure morphism. -/
  zero_comp : zero ≫ structureMap = 𝟙 S
  /-- The structure morphism is smooth of relative dimension one. -/
  smooth : SmoothOfRelativeDimension 1 structureMap
  /-- The structure morphism is proper. -/
  proper : IsProper structureMap
  /-- A pointed Weierstrass atlas exists: Zariski-locally on `S`, the curve is the projective model
  of an elliptic Weierstrass curve, compatibly with the zero section. -/
  localModel : Nonempty (PointedWeierstrassAtlas structureMap zero)

attribute [instance] EllipticCurveGeom.smooth EllipticCurveGeom.proper

namespace EllipticCurveGeom

/-- The zero section of an elliptic curve is a section of its structure morphism: the field
`zero_comp`, as a `simp` lemma. -/
@[reassoc (attr := simp)]
theorem zero_comp_structureMap {S : Scheme.{u}} (E : EllipticCurveGeom S) :
    E.zero ≫ E.structureMap = 𝟙 S :=
  E.zero_comp

/-- An elliptic curve over `S` satisfies the local-model condition `IsLocallyWeierstrass` for its
structure morphism and zero section: the pointwise form of the atlas condition `localModel`. -/
theorem isLocallyWeierstrass {S : Scheme.{u}} (E : EllipticCurveGeom S) :
    IsLocallyWeierstrass E.structureMap E.zero E.zero_comp :=
  E.localModel.elim (PointedWeierstrassAtlas.isLocallyWeierstrass E.zero_comp)

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
