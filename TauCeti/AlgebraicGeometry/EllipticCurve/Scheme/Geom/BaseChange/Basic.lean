/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Basic
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Section

/-!
# Base change of elliptic curves over a scheme

Let `E` be an elliptic curve over a scheme `S`, in the sense of `EllipticCurveGeom`, and
`f : T ⟶ S` a morphism of schemes. The base change `E.baseChange f` is the elliptic curve over `T`
whose total space is the pullback of the structure morphism of `E` along `f`, with the second
projection as structure morphism and the section induced by `f ≫ E.zero` as zero section.
Smoothness of relative dimension one, properness and the local-model condition
`IsLocallyWeierstrass` for a morphism with a section are stable under base change.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.baseChange E f`: the base change of an elliptic
  curve `E` over `S` along `f : T ⟶ S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.baseChangeIso E f`: the identification of the total
  space of `E.baseChange f` with the pullback of `E.structureMap` along `f`, compatible with the
  structure morphisms (`baseChangeIso_hom_snd`) and the zero sections (`zero_baseChangeIso_hom`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.baseChangeMap E k hk`: the canonical morphism
  between base changes induced by a morphism `k` of bases over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.baseChangeLift hg₁ hg₂ hh`: for a base change square
  `hg₁` of `E` along `u : T₁ ⟶ S`, a morphism from an elliptic curve `E₂` to `E` over `v : T₂ ⟶ S`
  and `h : T₂ ⟶ T₁` with `h ≫ u = v`, the induced morphism `E₂ ⟶ E₁` over `h`; it is a base change
  square when `g₂` also exhibits a base change (`isPullback_baseChangeLift`), and preserves zero
  sections when both `g₁` and `g₂` preserve them (`zero_baseChangeLift`).
* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.carrierMap hg hh` and
  `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.modelMap hg hh`: for a base change square
  `hg` of a morphism with a section, and charts `k` and `c` of its two sides whose bases are related
  by a morphism over the base change, the induced morphism between the restrictions to the chart
  bases, and the same morphism between the projective models of their equations.

## Main results

* `TauCeti.AlgebraicGeometry.IsLocallyWeierstrass.baseChange`: the local-model condition for a
  morphism with a section is stable under base change.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isPullback_baseChange`: the base change of `E` along
  `f` is a pullback of the structure morphism of `E` along `f`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.baseChangeMap_id` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.baseChangeMap_comp`: the canonical morphisms between
  base changes preserve identities and composition.
* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.isPullback_modelMap` and
  `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.projModelZero_modelMap`: the morphism
  `modelMap hg hh` is a base change square of projective models carrying the zero section to the
  zero section. Statements about the projective models of Weierstrass equations which are
  compatible with such squares therefore pass to elliptic curves along base change squares.
* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.modelPoint_modelMap_of_comp_eq`: if an
  endomorphism of `X` over `S` fixes a section, the induced endomorphism of the projective model of
  a chart fixes its model point.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_chart_comp_baseMap`: for elliptic curves over
  `S` and `S'` and a morphism `f : S' ⟶ S`, the charts of the curve over `S'` whose bases map over
  `f` into bases of charts of the curve over `S` cover `S'`.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`. `IsLocallyWeierstrass.baseChange` is
`ModularCurves.LocallyWeierstrass.baseChange` in
`projects/ModularCurves/ModularCurves/EllipticCurve/Basic.lean`; the fields of
`EllipticCurveGeom.baseChange` are those of `ModularCurves.EllipticCurve.baseChange` in
`projects/ModularCurves/ModularCurves/EllipticCurve/GroupLaw.lean`, without the group structure.
AINTLIB's Weierstrass model over `V` extends coefficients along an `Algebra` instance built from
`g.appLE U V _`; here it is `W.map (g.appLE U V _).hom`.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-! ### The local-model condition under base change -/

section IsLocallyWeierstrass

variable {X S T : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}

-- Over an affine open `V ⊆ g⁻¹ U` of `T`, the coefficient extension of a Weierstrass model of `π`
-- over `U` along `g.appLE U V` is a Weierstrass model of the base change of `π` along `g`.
private theorem exists_iso_projModel_map_appLE (hzero : zero ≫ π = 𝟙 S) (g : T ⟶ S) {U : S.Opens}
    (hU : IsAffineOpen U) {V : T.Opens} (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)
    {W : WeierstrassCurve Γ(S, U)} (e : pullback π U.ι ≅ W.projModel)
    (hover : e.hom ≫ W.projModelOver = pullback.snd π U.ι ≫ hU.isoSpec.hom)
    (hz : (hU.isoSpec.inv ≫ pullback.lift (U.ι ≫ zero) (𝟙 _) (by simp [hzero])) ≫ e.hom =
      W.projModelZero) :
    ∃ e' : pullback (pullback.snd π g) V.ι ≅ (W.map (g.appLE U V hVU).hom).projModel,
      e'.hom ≫ (W.map (g.appLE U V hVU).hom).projModelOver =
        pullback.snd (pullback.snd π g) V.ι ≫ hV.isoSpec.hom ∧
      (hV.isoSpec.inv ≫ pullback.lift (V.ι ≫ pullbackSection π g (g ≫ zero) (by simp [hzero])) (𝟙 _)
          (by simp)) ≫ e'.hom = (W.map (g.appLE U V hVU).hom).projModelZero := by
  -- the model over `U` is a pullback of `π` along `Spec Γ(S, U) ⟶ S`, so its coefficient
  -- extension is a pullback of `π` along `Spec Γ(T, V) ⟶ T ⟶ S`
  have hM : IsPullback (e.inv ≫ pullback.fst π U.ι) W.projModelOver π hU.fromSpec := by
    refine (IsPullback.of_hasPullback π U.ι).of_iso e (.refl _) hU.isoSpec (.refl _)
      ?_ hover.symm ?_ ?_ <;> simp
  have hR := (W.isPullback_projModelBaseChange (g.appLE U V hVU).hom).paste_horiz hM
  rw [CommRingCat.ofHom_hom, IsAffineOpen.SpecMap_appLE_fromSpec g hU hV] at hR
  -- and so is the restriction to `V` of the base change of `π` along `g`
  have hL : IsPullback (pullback.fst (pullback.snd π g) V.ι ≫ pullback.fst π g)
      (pullback.snd (pullback.snd π g) V.ι ≫ hV.isoSpec.hom) π (hV.fromSpec ≫ g) := by
    refine ((IsPullback.of_hasPullback _ _).paste_horiz (.of_hasPullback π g)).of_iso
      (.refl _) (.refl _) hV.isoSpec (.refl _) ?_ ?_ ?_ ?_ <;> simp
  -- the zero sections agree after composing with both projections of `hR`; on the second, both
  -- sides are the identity of `Spec Γ(T, V)`, on the right written via `CommRingCat.of`
  refine ⟨hL.isoIsPullback _ _ hR, hL.isoIsPullback_hom_snd _ _ hR, hR.hom_ext ?_ ?_⟩ <;>
    simp [W.projModelZero_projModelBaseChange_assoc, ← hz,
      IsAffineOpen.SpecMap_appLE_fromSpec_assoc g hU hV, CommRingCat.of_carrier]

/-- **The local-model condition is stable under base change**: if a morphism `π : X ⟶ S` with
the section `zero` satisfies `IsLocallyWeierstrass`, then so does its base change
`pullback.snd π g` along any `g : T ⟶ S`, with the section induced by `g ≫ zero`. -/
theorem IsLocallyWeierstrass.baseChange {hzero : zero ≫ π = 𝟙 S}
    (h : IsLocallyWeierstrass π zero hzero) (g : T ⟶ S) :
    IsLocallyWeierstrass (pullback.snd π g) (pullbackSection π g (g ≫ zero) (by simp [hzero]))
      (pullbackSection_snd _ _ _ _) := by
  refine (isLocallyWeierstrass_iff _).mpr fun t ↦ ?_
  obtain ⟨U, hgtU, W, hW, e, hover, hz⟩ := (isLocallyWeierstrass_iff hzero).mp h (g t)
  obtain ⟨V, hV, htV, hVU⟩ := exists_isAffineOpen_mem_and_subset (U := g ⁻¹ᵁ U.1) hgtU
  exact ⟨⟨V, hV⟩, htV, _, inferInstance,
    exists_iso_projModel_map_appLE hzero g U.2 hV hVU e hover hz⟩

end IsLocallyWeierstrass

/-! ### Base change of elliptic curves -/

namespace EllipticCurveGeom

variable {S T : Scheme.{u}} (E : EllipticCurveGeom S) (f : T ⟶ S)

/-- The **base change** of an elliptic curve `E` over `S` along a morphism `f : T ⟶ S`: the
total space is the pullback of `E.structureMap` along `f`, the structure morphism is the second
projection, and the zero section is the section induced by `f ≫ E.zero` (see `baseChangeIso`). -/
noncomputable def baseChange : EllipticCurveGeom T where
  carrier := pullback E.structureMap f
  structureMap := pullback.snd E.structureMap f
  zero := pullbackSection E.structureMap f (f ≫ E.zero) (by simp)
  zero_comp := pullbackSection_snd _ _ _ _
  smooth := inferInstance
  proper := inferInstance
  localModel := (nonempty_pointedWeierstrassAtlas_iff _).mpr (E.isLocallyWeierstrass.baseChange f)

/-- The isomorphism identifying the total space of `E.baseChange f` with the pullback of
`E.structureMap` along `f`. Under it, the structure morphism of `E.baseChange f` is the second
projection (`baseChangeIso_hom_snd`) and its zero section is the section induced by `f ≫ E.zero`
(`zero_baseChangeIso_hom`). -/
noncomputable def baseChangeIso : (E.baseChange f).carrier ≅ pullback E.structureMap f :=
  Iso.refl _

/-- Under `baseChangeIso`, the structure morphism of `E.baseChange f` is the second projection. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd : (E.baseChangeIso f).hom ≫ pullback.snd E.structureMap f =
    (E.baseChange f).structureMap := by
  simp [baseChangeIso, baseChange]

/-- Under `baseChangeIso`, the zero section of `E.baseChange f` is the section of the pullback
induced by `f ≫ E.zero`. -/
@[reassoc (attr := simp)]
theorem zero_baseChangeIso_hom : (E.baseChange f).zero ≫ (E.baseChangeIso f).hom =
    pullbackSection E.structureMap f (f ≫ E.zero) (by simp) := by
  simp [baseChangeIso, baseChange]

/-- The base change `E.baseChange f` is a pullback of the structure morphism of `E` along `f`: the
square formed by the projection `(E.baseChangeIso f).hom ≫ pullback.fst _ _` to `E`, the two
structure morphisms and `f` is a pullback square. -/
theorem isPullback_baseChange :
    IsPullback ((E.baseChangeIso f).hom ≫ pullback.fst E.structureMap f)
      (E.baseChange f).structureMap E.structureMap f :=
  (IsPullback.of_hasPullback _ _).of_iso (E.baseChangeIso f).symm (.refl _) (.refl _) (.refl _)
    (by simp) (by simp [Iso.eq_inv_comp]) (by simp) (by simp)

variable {T' T'' : Scheme.{u}} {f : T ⟶ S} {f' : T' ⟶ S} {f'' : T'' ⟶ S}

/-- The canonical morphism between base changes of `E` induced by a morphism `k : T' ⟶ T`
over `S`. On the pullback models it is the identity on `E.carrier` and `k` on the bases. -/
noncomputable def baseChangeMap (k : T' ⟶ T) (hk : k ≫ f = f') :
    (E.baseChange f').carrier ⟶ (E.baseChange f).carrier :=
  (E.baseChangeIso f').hom ≫ pullback.mapSnd E.structureMap f f' k hk ≫
    (E.baseChangeIso f).inv

/-- On the pullback models, `baseChangeMap` is `pullback.mapSnd`: it is the identity on the
elliptic curve and the given morphism on the bases. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_baseChangeIso_hom (k : T' ⟶ T) (hk : k ≫ f = f') :
    E.baseChangeMap k hk ≫ (E.baseChangeIso f).hom =
      (E.baseChangeIso f').hom ≫ pullback.mapSnd E.structureMap f f' k hk := by
  simp [baseChangeMap]

/-- The canonical morphism between base changes lies over the given morphism of bases. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_structureMap (k : T' ⟶ T) (hk : k ≫ f = f') :
    E.baseChangeMap k hk ≫ (E.baseChange f).structureMap =
      (E.baseChange f').structureMap ≫ k := by
  rw [← E.baseChangeIso_hom_snd f, E.baseChangeMap_baseChangeIso_hom_assoc]
  simp

/-- The canonical morphism between base changes carries the pulled-back zero section to the
pulled-back zero section. -/
@[reassoc (attr := simp)]
theorem zero_baseChangeMap (k : T' ⟶ T) (hk : k ≫ f = f') :
    (E.baseChange f').zero ≫ E.baseChangeMap k hk = k ≫ (E.baseChange f).zero := by
  rw [← cancel_mono (E.baseChangeIso f).hom]
  subst f'
  simp only [Category.assoc, E.baseChangeMap_baseChangeIso_hom, E.zero_baseChangeIso_hom]
  exact pullbackSection_comp_mapSnd E.structureMap f (k ≫ f) k rfl (f ≫ E.zero) (by simp)

/-- Base change along the identity morphism induces the identity morphism of the base-changed
elliptic curve. -/
@[simp]
theorem baseChangeMap_id : E.baseChangeMap (f := f) (𝟙 T) (by simp) = 𝟙 _ := by
  simp [baseChangeMap]

/-- The canonical morphisms between base changes are compatible with composition of morphisms of
bases. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_comp (k : T' ⟶ T) (hk : k ≫ f = f') (l : T'' ⟶ T')
    (hl : l ≫ f' = f'') :
    E.baseChangeMap l hl ≫ E.baseChangeMap k hk =
      E.baseChangeMap (l ≫ k) (by rw [Category.assoc, hk, hl]) := by
  simp [baseChangeMap]

section BaseChangeLift

variable {E} {T₁ T₂ : Scheme.{u}} {E₁ : EllipticCurveGeom T₁} {E₂ : EllipticCurveGeom T₂}
  {g₁ : E₁.carrier ⟶ E.carrier} {u : T₁ ⟶ S} (hg₁ : IsPullback g₁ E₁.structureMap E.structureMap u)
  {g₂ : E₂.carrier ⟶ E.carrier} {v : T₂ ⟶ S} {h : T₂ ⟶ T₁}

/-- Let `g₁ : E₁ ⟶ E` exhibit the elliptic curve `E₁` over `T₁` as a base change of `E` along
`u : T₁ ⟶ S`, and let `g₂ : E₂ ⟶ E` be a morphism from an elliptic curve `E₂` over `T₂` lying
over `v : T₂ ⟶ S`. Given `h : T₂ ⟶ T₁` with `h ≫ u = v`, this is the induced morphism `E₂ ⟶ E₁`
lying over `h`, compatibly with `g₁` and `g₂`. When `g₂` is also a base change square, so is this
morphism (`isPullback_baseChangeLift`), and it preserves zero sections when `g₁` and `g₂` do
(`zero_baseChangeLift`). -/
noncomputable def baseChangeLift (hg₂ : CommSq g₂ E₂.structureMap E.structureMap v)
    (hh : h ≫ u = v) : E₂.carrier ⟶ E₁.carrier :=
  hg₁.lift g₂ (E₂.structureMap ≫ h) (by rw [Category.assoc, hh, hg₂.w])

/-- The morphism `baseChangeLift hg₁ hg₂ hh` is compatible with the morphisms `g₁` and `g₂` to
`E`. -/
@[reassoc (attr := simp)]
theorem baseChangeLift_fst (hg₂ : CommSq g₂ E₂.structureMap E.structureMap v) (hh : h ≫ u = v) :
    baseChangeLift hg₁ hg₂ hh ≫ g₁ = g₂ :=
  IsPullback.lift_fst _ _ _ _

/-- The morphism `baseChangeLift hg₁ hg₂ hh` lies over the morphism `h` of bases. -/
@[reassoc (attr := simp)]
theorem baseChangeLift_structureMap (hg₂ : CommSq g₂ E₂.structureMap E.structureMap v)
    (hh : h ≫ u = v) : baseChangeLift hg₁ hg₂ hh ≫ E₁.structureMap = E₂.structureMap ≫ h :=
  IsPullback.lift_snd _ _ _ _

/-- If `g₂` exhibits `E₂` as a base change of `E`, then `baseChangeLift` exhibits `E₂` as the base
change of `E₁` along `h`. -/
theorem isPullback_baseChangeLift (hg₂ : IsPullback g₂ E₂.structureMap E.structureMap v)
    (hh : h ≫ u = v) :
    IsPullback (baseChangeLift hg₁ hg₂.toCommSq hh) E₂.structureMap E₁.structureMap h :=
  .of_right (by rw [baseChangeLift_fst, hh]; exact hg₂) (baseChangeLift_structureMap _ _ _) hg₁

/-- If `g₁` and `g₂` carry the zero sections of `E₁` and `E₂` to that of `E`, then
`baseChangeLift hg₁ hg₂ hh` carries the zero section of `E₂` to that of `E₁`. -/
@[reassoc]
theorem zero_baseChangeLift (hg₂ : CommSq g₂ E₂.structureMap E.structureMap v) (hh : h ≫ u = v)
    (h0₁ : E₁.zero ≫ g₁ = u ≫ E.zero) (h0₂ : E₂.zero ≫ g₂ = v ≫ E.zero) :
    E₂.zero ≫ baseChangeLift hg₁ hg₂ hh = h ≫ E₁.zero :=
  hg₁.hom_ext (by simp [h0₁, h0₂, reassoc_of% hh]) (by simp)

end BaseChangeLift

end EllipticCurveGeom

/-! ### Charts over a base change square -/

namespace PointedWeierstrassChart

variable {S X S' X' : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X} {π' : X' ⟶ S'} {zero' : S' ⟶ X'}
  {g : X' ⟶ X} {f : S' ⟶ S} (hg : IsPullback g π' π f)
  {k : PointedWeierstrassChart π' zero'} {c : PointedWeierstrassChart π zero} {h : k.base ⟶ c.base}
  (hh : h ≫ c.baseMap = k.baseMap ≫ f)

/-- Let `g : X' ⟶ X` be the base change of `π : X ⟶ S` along `f : S' ⟶ S`, and let `k` and `c` be
pointed Weierstrass charts of `π'` and `π` whose bases are related by `h : k.base ⟶ c.base` over
`f`. This is the morphism from the restriction of `X'` to the base of `k` to the restriction of `X`
to the base of `c` induced by `g`, lying over `h`. It generalizes `pullbackCarrierMap`, the case
`f = 𝟙 S` and `g = 𝟙 X`. -/
noncomputable def carrierMap : k.pullbackCarrier ⟶ c.pullbackCarrier :=
  c.isPullback.lift (k.toTotal ≫ g) (k.toBase ≫ h) (by
    rw [Category.assoc, hg.w, reassoc_of% k.isPullback.w, Category.assoc, hh])

/-- The morphism `carrierMap hg hh` lies over `g`. -/
@[reassoc (attr := simp)]
theorem carrierMap_toTotal : carrierMap hg hh ≫ c.toTotal = k.toTotal ≫ g :=
  IsPullback.lift_fst _ _ _ _

/-- The morphism `carrierMap hg hh` lies over the morphism `h` of bases. -/
@[reassoc (attr := simp)]
theorem carrierMap_toBase : carrierMap hg hh ≫ c.toBase = k.toBase ≫ h :=
  IsPullback.lift_snd _ _ _ _

/-- The restriction of `X'` to the base of `k` is the base change along `h` of the restriction of
`X` to the base of `c`, through `carrierMap hg hh`. -/
theorem isPullback_carrierMap : IsPullback (carrierMap hg hh) k.toBase c.toBase h :=
  .of_right (by rw [carrierMap_toTotal, hh]; exact k.isPullback.paste_horiz hg)
    (carrierMap_toBase hg hh) c.isPullback

/-- If `g` carries the section `zero'` to `zero`, then `carrierMap hg hh` carries the section of
`k` induced by `zero'` to the section of `c` induced by `zero`. -/
@[reassoc]
theorem pulledZero_carrierMap (h0 : zero' ≫ g = f ≫ zero) :
    k.pulledZero ≫ carrierMap hg hh = h ≫ c.pulledZero :=
  c.isPullback.hom_ext (by simp [h0, reassoc_of% hh]) (by simp)

/-- The morphism `carrierMap hg hh` between the restrictions of `X'` and `X` to the bases of `k`
and `c`, read through the isomorphisms of these restrictions with the projective models of the
equations of `k` and `c` (`modelIso_hom_modelMap`). It is a base change square of projective models
(`isPullback_modelMap`) and, when `g` preserves the sections, carries the zero section to the zero
section (`projModelZero_modelMap`). -/
noncomputable def modelMap : k.equation.projModel ⟶ c.equation.projModel :=
  k.modelIso.inv ≫ carrierMap hg hh ≫ c.modelIso.hom

/-- Through the isomorphisms with the projective models, `modelMap hg hh` is
`carrierMap hg hh`. -/
@[reassoc]
theorem modelIso_hom_modelMap :
    k.modelIso.hom ≫ modelMap hg hh = carrierMap hg hh ≫ c.modelIso.hom := by
  simp [modelMap]

/-- The projective model of the equation of `k` is the base change of that of `c` along
`Spec k.ring ≅ k.base ⟶ c.base ≅ Spec c.ring`, through `modelMap hg hh`. -/
theorem isPullback_modelMap : IsPullback (modelMap hg hh) k.equation.projModelOver
    c.equation.projModelOver (k.baseIso.inv ≫ h ≫ c.baseIso.hom) :=
  (isPullback_carrierMap hg hh).of_iso k.modelIso c.modelIso k.baseIso c.baseIso
    (by simp [modelMap]) k.modelIso_over.symm c.modelIso_over.symm (by simp)

/-- If `g` carries the section `zero'` to `zero`, then `modelMap hg hh` carries the zero section of
the projective model of the equation of `k` to that of `c`. -/
theorem projModelZero_modelMap (h0 : zero' ≫ g = f ≫ zero) :
    k.equation.projModelZero ≫ modelMap hg hh =
      (k.baseIso.inv ≫ h ≫ c.baseIso.hom) ≫ c.equation.projModelZero := by
  rw [← cancel_epi k.baseIso.hom, ← k.modelIso_zero_assoc]
  simp [modelMap, pulledZero_carrierMap_assoc hg hh h0]

variable (c) in
/-- If an endomorphism `σ` of `X` over `S`, cartesian over the identity, fixes a section `P`, then
the induced endomorphism of the projective model of the chart fixes the model point of `P`. -/
theorem modelPoint_modelMap_of_comp_eq {P : S ⟶ X} (hP : P ≫ π = 𝟙 S) {σ : X ⟶ X}
    (hσ : IsPullback σ π π (𝟙 S)) (hσP : P ≫ σ = P) :
    c.modelPoint hP ≫ modelMap hσ (by simp : 𝟙 c.base ≫ c.baseMap = c.baseMap ≫ 𝟙 S) =
      c.modelPoint hP := by
  have : c.chartPoint hP ≫ carrierMap hσ (by simp : 𝟙 c.base ≫ c.baseMap = c.baseMap ≫ 𝟙 S) =
      c.chartPoint hP :=
    c.isPullback.hom_ext (by simp [hσP]) (by simp)
  simp only [modelPoint_def, Category.assoc, modelIso_hom_modelMap, reassoc_of% this]

end PointedWeierstrassChart

/-! ### Charts compatible with a morphism of bases -/

namespace EllipticCurveGeom

open PointedWeierstrassChart

variable {S S' : Scheme.{u}}

/-- **Charts compatible with a morphism of bases.** For elliptic curves `E` over `S` and `E'` over
`S'` and a morphism `f : S' ⟶ S`, every point of `S'` lies in the base of a pointed Weierstrass
chart `k` of `E'` whose base maps over `f` into the base of a pointed Weierstrass chart `c` of `E`.
The chart `k` can be taken to be the restriction of any chart of `E'` around the point to an affine
open. -/
theorem exists_chart_comp_baseMap (E : EllipticCurveGeom S) (E' : EllipticCurveGeom S')
    (f : S' ⟶ S) (s : S') :
    ∃ (k : PointedWeierstrassChart E'.structureMap E'.zero)
      (c : PointedWeierstrassChart E.structureMap E.zero) (h : k.base ⟶ c.base),
      h ≫ c.baseMap = k.baseMap ≫ f ∧ s ∈ Set.range k.baseMap := by
  obtain ⟨A⟩ := E'.localModel
  obtain ⟨B⟩ := E.localModel
  obtain ⟨i, a, ha⟩ := A.covers s
  obtain ⟨j, b, hb⟩ := B.covers (f s)
  let d := A.chart i
  let c := B.chart j
  -- an affine open `V` of the base of `d`, around `a`, mapping into the base of `c` under `f`
  have hmem : a ∈ d.baseMap ⁻¹ᵁ f ⁻¹ᵁ c.baseMap.opensRange := ⟨b, by rw [hb, ha]⟩
  obtain ⟨V, hV, haV, hVU⟩ := exists_isAffineOpen_mem_and_subset hmem
  have hk : Set.range ((d.restrict ⟨V, hV⟩).baseMap ≫ f) ⊆ Set.range c.baseMap := by
    rintro _ ⟨y, rfl⟩
    have hy : d.restrictι ⟨V, hV⟩ y ∈ V := (d.range_restrictι ⟨V, hV⟩).subset ⟨y, rfl⟩
    rw [← restrictι_baseMap, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact hVU hy
  obtain ⟨y, hy⟩ : a ∈ Set.range (d.restrictι ⟨V, hV⟩) := by
    rwa [range_restrictι]
  exact ⟨d.restrict ⟨V, hV⟩, c, IsOpenImmersion.lift c.baseMap _ hk, IsOpenImmersion.lift_fac _ _ _,
    y, by rw [← restrictι_baseMap, Scheme.Hom.comp_apply, hy, ha]⟩

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
