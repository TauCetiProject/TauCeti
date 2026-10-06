/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Section

/-!
# Pointed locally Weierstrass curves

A pointed Weierstrass chart identifies a relative curve over an affine open of its base with
an elliptic projective Weierstrass model, carrying the distinguished section to infinity.
A pointed Weierstrass atlas is a covering family of these charts. The base maps are open
immersions, so the condition is Zariski-local, not merely local for a finer topology.

`EllipticCurveGeom` records a relative curve with a section and the existence of such an atlas.
The atlas is existence-truncated: the curve does not select equations. Smoothness of relative
dimension one and properness follow from the charts. No group law is included.

Every elliptic Weierstrass equation supplies an `EllipticCurveGeom` over its coefficient ring.
The construction uses Mathlib's chosen pullbacks, so the section of a restricted curve is
uniquely determined rather than stored as additional chart data.

`IsLocallyWeierstrass` expresses the same condition using equations over `Γ(S,U)` for affine
opens `U`. The theorem `nonempty_pointedWeierstrassAtlas_iff` bridges the two formulations;
`EllipticCurveGeom.isLocallyWeierstrass` supplies the affine-open interface for geometric curves.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.5–2.2.6.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti

variable {S X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}

/-- An elliptic Weierstrass presentation over an affine open of the base, preserving the
specified section. The pullback and its section are canonical, not additional choices. -/
structure PointedWeierstrassChart (π : X ⟶ S) (zero : S ⟶ X) where
  /-- The coefficient ring of the local equation. -/
  ring : Type u
  /-- The commutative ring structure on the coefficients. -/
  [commRing : CommRing ring]
  /-- The affine open immersion into the base. -/
  baseMap : Spec (.of ring) ⟶ S
  /-- The base map identifies the spectrum with a Zariski open subscheme. -/
  baseMap_open : IsOpenImmersion baseMap
  /-- The local Weierstrass equation, with unit discriminant. -/
  equation : WeierstrassCurve ring
  /-- The local equation has unit discriminant. -/
  equation_elliptic : equation.IsElliptic
  /-- The presentation of the restricted curve by the projective cubic. -/
  modelIso : pullback π baseMap ≅ equation.projModel
  /-- The presentation commutes with projection to the affine base. -/
  modelIso_over : modelIso.hom ≫ equation.projModelOver = pullback.snd π baseMap
  /-- The point at infinity projects to the specified section of the original curve. -/
  modelIso_zero : equation.projModelZero ≫ modelIso.inv ≫ pullback.fst π baseMap =
    baseMap ≫ zero

attribute [instance] PointedWeierstrassChart.commRing PointedWeierstrassChart.baseMap_open
  PointedWeierstrassChart.equation_elliptic

namespace PointedWeierstrassChart

variable (C : PointedWeierstrassChart π zero)

/-- The inverse presentation also lies over the affine base. -/
@[reassoc (attr := simp)]
theorem modelIso_inv_over :
    C.modelIso.inv ≫ pullback.snd π C.baseMap = C.equation.projModelOver := by
  rw [← C.modelIso_over, Iso.inv_hom_id_assoc]

attribute [reassoc (attr := simp)] modelIso_over modelIso_zero

/-- The specified section satisfies the section law on the chart's affine base. -/
@[reassoc]
theorem baseMap_zero_comp : (C.baseMap ≫ zero) ≫ π = C.baseMap := by
  rw [← C.modelIso_zero, Category.assoc, Category.assoc, pullback.condition,
    ← Category.assoc]
  simp [Category.assoc]

/-- The presentation carries the canonical restricted section to infinity. -/
@[reassoc (attr := simp)]
theorem zero_lift_modelIso_hom :
    pullbackSection π C.baseMap (C.baseMap ≫ zero) C.baseMap_zero_comp ≫ C.modelIso.hom =
      C.equation.projModelZero := by
  apply (cancel_mono C.modelIso.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext <;> simp

/-- The curve restricted to a pointed Weierstrass chart is proper over that chart. -/
instance isProper_snd : IsProper (pullback.snd π C.baseMap) := by
  rw [← C.modelIso_over]
  infer_instance

/-- The curve restricted to a pointed Weierstrass chart is smooth of relative dimension one. -/
instance smoothOfRelativeDimension_snd :
    SmoothOfRelativeDimension 1 (pullback.snd π C.baseMap) := by
  rw [← C.modelIso_over]
  exact HasRingHomProperty.comp_of_isOpenImmersion
    (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

/-- The identity base map gives a pointed chart for an elliptic Weierstrass model. -/
noncomputable def ofWeierstrass {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] : PointedWeierstrassChart W.projModelOver W.projModelZero where
  ring := R
  baseMap := 𝟙 _
  baseMap_open := inferInstance
  equation := W
  equation_elliptic := inferInstance
  modelIso := asIso (pullback.fst W.projModelOver (𝟙 _))
  modelIso_over := by simpa using (pullback.condition (f := W.projModelOver) (g := 𝟙 _))
  modelIso_zero := by simp

end PointedWeierstrassChart

/-- A jointly surjective family of pointed Weierstrass charts. -/
structure PointedWeierstrassAtlas (π : X ⟶ S) (zero : S ⟶ X) where
  /-- The indexing type of the covering family. -/
  index : Type u
  /-- A pointed presentation for each member of the covering family. -/
  chart : index → PointedWeierstrassChart π zero
  /-- The chart base maps jointly cover every point of the base scheme. -/
  covers : ∀ s : S, ∃ i : index, ∃ x : Spec (.of (chart i).ring), (chart i).baseMap x = s

namespace PointedWeierstrassAtlas

variable (A : PointedWeierstrassAtlas π zero)

/-- The affine open cover of the base underlying a pointed Weierstrass atlas. -/
@[expose, simps! I₀ X f]
noncomputable def openCover : S.OpenCover :=
  Scheme.Cover.mkOfCovers A.index (fun i ↦ Spec (.of (A.chart i).ring))
    (fun i ↦ (A.chart i).baseMap) A.covers

include A

/-- Properness can be checked on the pointed Weierstrass charts. -/
theorem isProper : IsProper π := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) A.openCover
  intro i
  exact (A.chart i).isProper_snd

/-- A pointed Weierstrass atlas makes the relative curve smooth of relative dimension one. -/
theorem smoothOfRelativeDimension : SmoothOfRelativeDimension 1 π := by
  let := HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension 1)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  apply IsZariskiLocalAtTarget.of_openCover (P := @SmoothOfRelativeDimension 1) A.openCover
  intro i
  exact (A.chart i).smoothOfRelativeDimension_snd

/-- Every elliptic Weierstrass model has the one-chart atlas over its coefficient ring. -/
noncomputable def ofWeierstrass {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] : PointedWeierstrassAtlas W.projModelOver W.projModelZero where
  index := PUnit
  chart _ := PointedWeierstrassChart.ofWeierstrass W
  covers s := ⟨PUnit.unit, s, rfl⟩

end PointedWeierstrassAtlas

/-- Around every base point there is an affine open `U` and an elliptic equation over
`Γ(S,U)` presenting the restricted curve over `Spec Γ(S,U)` and carrying its canonical
restricted section to infinity. -/
def IsLocallyWeierstrass (π : X ⟶ S) (zero : S ⟶ X) (hzero : zero ≫ π = 𝟙 S) : Prop :=
  ∀ s : S, ∃ (U : S.affineOpens), s ∈ U.1 ∧
    ∃ W : WeierstrassCurve Γ(S, U.1), W.IsElliptic ∧
      ∃ e : pullback π U.2.fromSpec ≅ W.projModel,
        e.hom ≫ W.projModelOver = pullback.snd π U.2.fromSpec ∧
        pullbackSection π U.2.fromSpec (U.2.fromSpec ≫ zero)
          (by simp [hzero]) ≫ e.hom = W.projModelZero

/-- The affine-open witnesses characterize the local-Weierstrass predicate. -/
theorem isLocallyWeierstrass_iff (hzero : zero ≫ π = 𝟙 S) :
    IsLocallyWeierstrass π zero hzero ↔
      ∀ s : S, ∃ (U : S.affineOpens), s ∈ U.1 ∧
        ∃ W : WeierstrassCurve Γ(S, U.1), W.IsElliptic ∧
          ∃ e : pullback π U.2.fromSpec ≅ W.projModel,
            e.hom ≫ W.projModelOver = pullback.snd π U.2.fromSpec ∧
            pullbackSection π U.2.fromSpec (U.2.fromSpec ≫ zero)
              (by simp [hzero]) ≫ e.hom = W.projModelZero :=
  Iff.rfl

namespace PointedWeierstrassChart

/-- A chart can be expressed over the canonical ring of sections of its affine base open. -/
theorem exists_affineOpen_model (C : PointedWeierstrassChart π zero)
    (hzero : zero ≫ π = 𝟙 S) :
    ∃ (U : S.affineOpens), (U.1 : Set S) = Set.range C.baseMap ∧
      ∃ W : WeierstrassCurve Γ(S, U.1), W.IsElliptic ∧
        ∃ e : pullback π U.2.fromSpec ≅ W.projModel,
          e.hom ≫ W.projModelOver = pullback.snd π U.2.fromSpec ∧
          pullbackSection π U.2.fromSpec (U.2.fromSpec ≫ zero)
            (by simp [hzero]) ≫ e.hom = W.projModelZero := by
  let U : S.affineOpens := ⟨C.baseMap.opensRange, isAffineOpen_opensRange C.baseMap⟩
  let := IsAffineOpen.isOpenImmersion_fromSpec U.2
  let b : Spec Γ(S, U.1) ≅ Spec (.of C.ring) :=
    (IsOpenImmersion.isoOfRangeEq C.baseMap U.2.fromSpec U.2.range_fromSpec.symm).symm
  have hb : b.hom ≫ C.baseMap = U.2.fromSpec :=
    IsOpenImmersion.isoOfRangeEq_inv_fac C.baseMap U.2.fromSpec U.2.range_fromSpec.symm
  let r : C.ring ≃+* Γ(S, U.1) :=
    (Scheme.Spec.preimageIso b).unop.commRingCatIsoToRingEquiv
  have hr : Spec.map (CommRingCat.ofHom r.toRingHom) = b.hom := by
    dsimp only [r]
    rw [RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
      CommRingCat.ofHom_hom]
    simp [← Scheme.Spec_map]
  let p : pullback π U.2.fromSpec ≅ pullback π C.baseMap :=
    asIso (pullback.map π U.2.fromSpec π C.baseMap (𝟙 _) b.hom (𝟙 _)
      (by simp) (by simpa using hb.symm))
  let e := p ≪≫ C.modelIso ≪≫ (projModelRingIso C.equation r).symm
  refine ⟨U, rfl, C.equation.map r.toRingHom, inferInstance, e, ?_, ?_⟩
  · apply (cancel_mono b.hom).mp
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, Category.assoc, Category.assoc, ← hr,
      ← projModelRingIso_hom_over, Iso.inv_hom_id_assoc, C.modelIso_over]
    simpa [p] using congrArg (pullback.snd π U.2.fromSpec ≫ ·) hr.symm
  · have hsec : pullbackSection π U.2.fromSpec (U.2.fromSpec ≫ zero)
        (by simp [hzero]) ≫ p.hom =
        b.hom ≫ pullbackSection π C.baseMap (C.baseMap ≫ zero) C.baseMap_zero_comp := by
      apply pullback.hom_ext
      · simp only [p, asIso_hom, Category.assoc, pullback.lift_fst,
          Category.comp_id, pullbackSection_fst]
        rw [← Category.assoc, hb]
      · simp [p, Category.assoc]
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, ← Category.assoc, hsec]
    simp only [Category.assoc, C.zero_lift_modelIso_hom_assoc]
    rw [← Category.assoc, ← hr, ← projModelRingIso_zero_hom]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end PointedWeierstrassChart

/-- Existence of an atlas is equivalent to having a pointed Weierstrass chart through every
point of the base. This formulation chooses neither equations nor an indexing family. -/
theorem nonempty_pointedWeierstrassAtlas_iff_exists_chart :
    Nonempty (PointedWeierstrassAtlas π zero) ↔
      ∀ s : S, ∃ C : PointedWeierstrassChart π zero, s ∈ Set.range C.baseMap := by
  constructor
  · rintro ⟨A⟩ s
    obtain ⟨i, x, hx⟩ := A.covers s
    exact ⟨A.chart i, x, hx⟩
  · intro h
    classical
    choose C x hx using h
    exact ⟨⟨S, C, fun s ↦ ⟨s, x s, hx s⟩⟩⟩

/-- An atlas exists exactly when the canonical affine-open local-Weierstrass condition holds. -/
theorem nonempty_pointedWeierstrassAtlas_iff (hzero : zero ≫ π = 𝟙 S) :
    Nonempty (PointedWeierstrassAtlas π zero) ↔ IsLocallyWeierstrass π zero hzero := by
  rw [nonempty_pointedWeierstrassAtlas_iff_exists_chart]
  constructor
  · intro h s
    obtain ⟨C, hs⟩ := h s
    obtain ⟨U, hU, W, hW, e, he, hz⟩ := C.exists_affineOpen_model hzero
    refine ⟨U, ?_, W, hW, e, he, hz⟩
    -- Membership of an affine open is membership of its underlying set.
    change s ∈ (U.1 : Set S)
    rwa [hU]
  · intro h s
    obtain ⟨U, hs, W, hW, e, he, hz⟩ := h s
    let C : PointedWeierstrassChart π zero :=
      { ring := Γ(S, U.1)
        baseMap := U.2.fromSpec
        baseMap_open := IsAffineOpen.isOpenImmersion_fromSpec U.2
        equation := W
        equation_elliptic := hW
        modelIso := e
        modelIso_over := he
        modelIso_zero := by rw [← hz]; simp [Category.assoc] }
    refine ⟨C, ?_⟩
    -- The chart's base map is the canonical spectrum immersion.
    change s ∈ Set.range U.2.fromSpec
    rw [U.2.range_fromSpec]
    exact hs

/-- A pointed relative curve that is Zariski-locally an elliptic Weierstrass model.
Smoothness of relative dimension one and properness are consequences of the local model.
This is the geometric data of an elliptic curve, without its group law. -/
structure EllipticCurveGeom (S : Scheme.{u}) where
  /-- The total space of the relative curve. -/
  carrier : Scheme.{u}
  /-- The projection to the base. -/
  structureMap : carrier ⟶ S
  /-- The distinguished section, locally the point at infinity. -/
  zero : S ⟶ carrier
  /-- The distinguished section is a right inverse of the structure map. -/
  zero_comp : zero ≫ structureMap = 𝟙 S
  /-- A pointed Weierstrass atlas exists, without selecting local equations as curve data. -/
  localModel : Nonempty (PointedWeierstrassAtlas structureMap zero)

namespace EllipticCurveGeom

/-- A geometric elliptic curve is determined by its carrier, projection and zero section. -/
@[ext (iff := false)]
theorem ext {E E' : EllipticCurveGeom S} (hcarrier : E.carrier = E'.carrier)
    (hstructureMap : E.structureMap = eqToHom hcarrier ≫ E'.structureMap)
    (hzero : E.zero ≫ eqToHom hcarrier = E'.zero) : E = E' := by
  cases E
  cases E'
  cases hcarrier
  simp_all

variable (E : EllipticCurveGeom S)

/-- The distinguished point is a section of the relative curve. -/
@[reassoc (attr := simp)]
theorem zero_comp_structureMap : E.zero ≫ E.structureMap = 𝟙 S :=
  E.zero_comp

/-- The geometric elliptic curve is proper over its base. -/
instance isProper : IsProper E.structureMap :=
  E.localModel.elim PointedWeierstrassAtlas.isProper

/-- The geometric elliptic curve is smooth of relative dimension one over its base. -/
instance smoothOfRelativeDimension : SmoothOfRelativeDimension 1 E.structureMap :=
  E.localModel.elim PointedWeierstrassAtlas.smoothOfRelativeDimension

/-- Around every base point, the curve has a pointed elliptic Weierstrass presentation. -/
theorem exists_chart (s : S) :
    ∃ C : PointedWeierstrassChart E.structureMap E.zero, s ∈ Set.range C.baseMap :=
  nonempty_pointedWeierstrassAtlas_iff_exists_chart.mp E.localModel s

/-- A geometric elliptic curve satisfies the canonical affine-open local-model condition. -/
theorem isLocallyWeierstrass :
    IsLocallyWeierstrass E.structureMap E.zero E.zero_comp :=
  (nonempty_pointedWeierstrassAtlas_iff E.zero_comp).mp E.localModel

/-- The geometric elliptic curve of an elliptic Weierstrass equation. -/
@[expose, simps! carrier structureMap zero]
noncomputable def ofWeierstrass {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] : EllipticCurveGeom (Spec (.of R)) where
  carrier := W.projModel
  structureMap := W.projModelOver
  zero := W.projModelZero
  zero_comp := W.projModelZero_projModelOver
  localModel := ⟨PointedWeierstrassAtlas.ofWeierstrass W⟩

end EllipticCurveGeom

end TauCeti
