/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth

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
  [commRing : CommRing ring]
  /-- The affine open immersion into the base. -/
  baseMap : Spec (.of ring) ⟶ S
  baseMap_open : IsOpenImmersion baseMap
  /-- The local Weierstrass equation, with unit discriminant. -/
  equation : WeierstrassCurve ring
  equation_elliptic : equation.IsElliptic
  /-- The presentation of the restricted curve by the projective cubic. -/
  modelIso : pullback π baseMap ≅ equation.projModel
  modelIso_over : modelIso.hom ≫ equation.projModelOver = pullback.snd π baseMap
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

/-- The presentation carries the canonical restricted section to infinity. -/
@[reassoc (attr := simp)]
theorem zero_lift_modelIso_hom (hzero : zero ≫ π = 𝟙 S) :
    pullback.lift (C.baseMap ≫ zero) (𝟙 _) (by simp [hzero]) ≫ C.modelIso.hom =
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
  zero_comp : zero ≫ structureMap = 𝟙 S
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
