/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom
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

## Main results

* `TauCeti.AlgebraicGeometry.IsLocallyWeierstrass.baseChange`: the local-model condition for a
  morphism with a section is stable under base change.

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

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
