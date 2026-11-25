/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Conormal
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Glue
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.OfWeierstrass

/-!
# Invariant differentials and adapted `x`-coordinates on elliptic curves over schemes

For an elliptic curve `E` over `S`, `E.zero` is a relative effective Cartier divisor
(`isRelativeEffectiveCartier_zero_ker`), and a nowhere-vanishing **invariant differential** on
`E/S` is a global basis `𝟙_ S.Modules ≅ E.zero.conormalSheaf`
(`EllipticCurveGeom.InvariantDifferential`, Katz–Mazur 2.2.8; Deligne–Rapoport II.1.5). Invariant
differentials pull back along pointed cartesian squares (`invariantDifferentialPullback`) and are
determined on any pointed Weierstrass atlas (`invariantDifferential_ext_of_atlas`). For sections
`P, Q : S ⟶ E` missing `E.zero` everywhere, `WeierstrassCurve.projModelAdaptedXCoord` glues via
`glueChartSection` to `EllipticCurveGeom.adaptedXCoord` (and `adaptedXCoordMap`), compatible with
pointed cartesian squares (`appTop_adaptedXCoord_of_isPullback`).

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Princeton Univ. Press, 1985,
  2.2.8 and 2.2.9.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.5.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme (ΓSpecIso)
open AlgebraicGeometry.Scheme.Modules (unitSmulIso unitSmulIso_one unitSmulIso_inj
  existsUnique_unitSmulIso_eq)
open AlgebraicGeometry.Scheme.Hom (conormalBasisPullback conormalBasisPullback_id
  conormalBasisPullback_comp conormalBasisPullback_congr conormalBasisPullback_unitSmulIso
  conormalBasisPullbackOfIso conormalBasisPullbackOfIso_def conormalBasisPullbackOfIso_symm_apply)

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- `E.zero` is a relative effective Cartier divisor on `E` over `S`. -/
theorem isRelativeEffectiveCartier_zero_ker :
    E.zero.ker.IsRelativeEffectiveCartier E.structureMap :=
  Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension E.zero E.zero_comp

/-- `E.zero` is an effective Cartier divisor on `E`. -/
theorem isEffectiveCartier_zero_ker : E.zero.ker.IsEffectiveCartier :=
  E.isRelativeEffectiveCartier_zero_ker.isEffectiveCartier

/-- A nowhere-vanishing **invariant differential** `𝟙_ S.Modules ≅ E.zero.conormalSheaf` on `E`. -/
abbrev InvariantDifferential : Type u := 𝟙_ S.Modules ≅ E.zero.conormalSheaf

section Pullback

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {f : S' ⟶ S} {g : E'.carrier ⟶ E.carrier}

section FixedSquare

variable (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)

/-- Pullback of an invariant differential along a pointed cartesian square `(g, f)`. -/
noncomputable def invariantDifferentialPullback (ω : E.InvariantDifferential) :
    E'.InvariantDifferential :=
  conormalBasisPullback E.zero_comp E'.zero_comp hg h0 ω

/-- `invariantDifferentialPullback` is `Scheme.Hom.conormalBasisPullback`. -/
theorem invariantDifferentialPullback_def (ω : E.InvariantDifferential) :
    invariantDifferentialPullback hg h0 ω =
      conormalBasisPullback E.zero_comp E'.zero_comp hg h0 ω := by rfl

/-- Pulling back `u • ω` scales the pulled-back differential by `f^* u`. -/
theorem invariantDifferentialPullback_unitSmulIso (u : Γ(S, ⊤)ˣ) (ω : E.InvariantDifferential) :
    invariantDifferentialPullback hg h0 (unitSmulIso u ω) =
      unitSmulIso (Units.map f.appTop.hom.toMonoidHom u) (invariantDifferentialPullback hg h0 ω) :=
  conormalBasisPullback_unitSmulIso E.zero_comp E'.zero_comp hg h0 u ω

end FixedSquare

/-- Pulling back an invariant differential along the identity square is the identity. -/
@[simp]
theorem invariantDifferentialPullback_id (ω : E.InvariantDifferential) :
    invariantDifferentialPullback (.id_horiz E.structureMap)
      (by rw [Category.comp_id, Category.id_comp]) ω = ω :=
  conormalBasisPullback_id E.zero_comp _ _ ω

/-- Contravariant functoriality of `invariantDifferentialPullback` under horizontal pasting. -/
theorem invariantDifferentialPullback_comp {S'' : Scheme.{u}} {E'' : EllipticCurveGeom S''}
    {f' : S'' ⟶ S'} {g' : E''.carrier ⟶ E'.carrier}
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    (hg' : IsPullback g' E''.structureMap E'.structureMap f') (h0' : E''.zero ≫ g' = f' ≫ E'.zero)
    (ω : E.InvariantDifferential) :
    invariantDifferentialPullback hg' h0' (invariantDifferentialPullback hg h0 ω) =
      invariantDifferentialPullback (hg'.paste_horiz hg)
        (by rw [reassoc_of% h0', h0, Category.assoc]) ω :=
  conormalBasisPullback_comp E.zero_comp E'.zero_comp E''.zero_comp hg h0 hg' h0' ω

/-- `invariantDifferentialPullback` depends only on `(f, g)` and `ω`. -/
theorem invariantDifferentialPullback_congr {f₁ f₂ : S' ⟶ S} {g₁ g₂ : E'.carrier ⟶ E.carrier}
    (hf : f₁ = f₂) (hg : g₁ = g₂)
    (hp₁ : IsPullback g₁ E'.structureMap E.structureMap f₁) (h0₁ : E'.zero ≫ g₁ = f₁ ≫ E.zero)
    (hp₂ : IsPullback g₂ E'.structureMap E.structureMap f₂) (h0₂ : E'.zero ≫ g₂ = f₂ ≫ E.zero)
    (ω : E.InvariantDifferential) :
    invariantDifferentialPullback hp₁ h0₁ ω = invariantDifferentialPullback hp₂ h0₂ ω :=
  conormalBasisPullback_congr E.zero_comp E'.zero_comp hf hg hp₁ h0₁ hp₂ h0₂ ω

end Pullback

end EllipticCurveGeom

namespace PointedWeierstrassChart

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}

/-- Pullback of `ω : E.InvariantDifferential` to the projective model of a chart `c`. -/
noncomputable def modelDifferential (c : PointedWeierstrassChart E.structureMap E.zero)
    (ω : E.InvariantDifferential) :
    𝟙_ (Spec c.ring).Modules ≅ c.equation.projModelZero.conormalSheaf :=
  conormalBasisPullback E.zero_comp c.equation.projModelZero_projModelOver
    c.isPullback_modelIso_inv_toTotal c.projModelZero_modelIso_inv_toTotal ω

/-- `modelDifferential` is `Scheme.Hom.conormalBasisPullback` along the chart projection. -/
theorem modelDifferential_def (c : PointedWeierstrassChart E.structureMap E.zero)
    (ω : E.InvariantDifferential) :
    c.modelDifferential ω = conormalBasisPullback E.zero_comp c.equation.projModelZero_projModelOver
      c.isPullback_modelIso_inv_toTotal c.projModelZero_modelIso_inv_toTotal ω := by rfl

/-- Along `modelMap hg hh`, `c.modelDifferential ω` pulls back to `k.modelDifferential` of
`invariantDifferentialPullback hg h0 ω`. -/
theorem conormalBasisPullback_modelDifferential {S' : Scheme.{u}} {E' : EllipticCurveGeom S'}
    {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S}
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    {k : PointedWeierstrassChart E'.structureMap E'.zero}
    {c : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k.baseMap ≫ f) (ω : E.InvariantDifferential) :
    conormalBasisPullback c.equation.projModelZero_projModelOver
        k.equation.projModelZero_projModelOver (isPullback_modelMap hg hh)
        (projModelZero_modelMap hg hh h0) (c.modelDifferential ω) =
      k.modelDifferential (EllipticCurveGeom.invariantDifferentialPullback hg h0 ω) := by
  rw [modelDifferential, modelDifferential, EllipticCurveGeom.invariantDifferentialPullback,
    conormalBasisPullback_comp, conormalBasisPullback_comp]
  refine conormalBasisPullback_congr E.zero_comp k.equation.projModelZero_projModelOver
    (by simp [hh]) ?_ _ _ _ _ ω
  rw [← cancel_epi k.modelIso.hom, modelIso_hom_modelMap_assoc, Iso.hom_inv_id_assoc,
    carrierMap_toTotal]; simp

private noncomputable def adaptedXCoordSection (c : PointedWeierstrassChart E.structureMap E.zero)
    {P Q : S ⟶ E.carrier} (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)
    (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s) (ω : E.InvariantDifferential) :
    Γ(c.base, ⊤) :=
  c.baseIso.hom.appTop ((ΓSpecIso c.ring).inv (c.equation.projModelAdaptedXCoord
    (c.modelPoint_projModelOver hP) (c.modelPoint_projModelOver hQ) (c.modelPoint_apply_ne hP hP₀)
    (c.modelPoint_apply_ne hQ hQ₀) (c.modelDifferential ω)))

private theorem appTop_adaptedXCoordSection {S' : Scheme.{u}} {E' : EllipticCurveGeom S'}
    {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S}
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    {P Q : S ⟶ E.carrier} {P' Q' : S' ⟶ E'.carrier}
    (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)
    (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s)
    (hP' : P' ≫ E'.structureMap = 𝟙 S') (hQ' : Q' ≫ E'.structureMap = 𝟙 S')
    (hP'₀ : ∀ s, P' s ≠ E'.zero s) (hQ'₀ : ∀ s, Q' s ≠ E'.zero s)
    (hPg : P' ≫ g = f ≫ P) (hQg : Q' ≫ g = f ≫ Q)
    {k : PointedWeierstrassChart E'.structureMap E'.zero}
    {c : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k.baseMap ≫ f) (ω : E.InvariantDifferential) :
    h.appTop (c.adaptedXCoordSection hP hQ hP₀ hQ₀ ω) =
      k.adaptedXCoordSection hP' hQ' hP'₀ hQ'₀
        (EllipticCurveGeom.invariantDifferentialPullback hg h0 ω) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : c.ring ⟶ k.ring, Spec.map φ = k.baseIso.inv ≫ h ≫ c.baseIso.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hF := isPullback_modelMap hg hh; have hz := projModelZero_modelMap hg hh h0
  have hPF := modelPoint_modelMap hg hh hP hP' hPg; have hQF := modelPoint_modelMap hg hh hQ hQ' hQg
  have hω := conormalBasisPullback_modelDifferential hg h0 hh ω
  rw [← hφ, ← CommRingCat.ofHom_hom φ] at hF hz hPF hQF
  have hx := WeierstrassCurve.map_projModelAdaptedXCoord_of_isPullback hF hz
    (k.modelPoint_projModelOver hP') (k.modelPoint_projModelOver hQ')
    (k.modelPoint_apply_ne hP' hP'₀) (k.modelPoint_apply_ne hQ' hQ'₀)
    (c.modelPoint_projModelOver hP) (c.modelPoint_projModelOver hQ)
    (c.modelPoint_apply_ne hP hP₀) (c.modelPoint_apply_ne hQ hQ₀) hPF hQF (c.modelDifferential ω)
  have hcongr := (conormalBasisPullback_congr c.equation.projModelZero_projModelOver
    k.equation.projModelZero_projModelOver (by rw [CommRingCat.ofHom_hom, hφ]) rfl
    hF hz _ _ _).trans hω
  rw [hcongr] at hx
  have hh' : h ≫ c.baseIso.hom = k.baseIso.hom ≫ Spec.map φ := by simp [hφ]
  rw [adaptedXCoordSection, adaptedXCoordSection, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, hh', Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  simpa using congrArg k.baseIso.hom.appTop (congrArg (ΓSpecIso k.ring).inv hx)

end PointedWeierstrassChart

namespace EllipticCurveGeom

open PointedWeierstrassChart

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **Invariant differentials are determined on any pointed Weierstrass atlas.** -/
theorem invariantDifferential_ext_of_atlas (A : PointedWeierstrassAtlas E.structureMap E.zero)
    {ω₁ ω₂ : E.InvariantDifferential}
    (h : ∀ i, (A.chart i).modelDifferential ω₁ = (A.chart i).modelDifferential ω₂) :
    ω₁ = ω₂ := by
  obtain ⟨u, rfl, -⟩ := existsUnique_unitSmulIso_eq ω₂ ω₁
  suffices hu : u = 1 by rw [hu, unitSmulIso_one]
  ext; rw [Units.val_one]; refine A.openCover.ext_elem (U := ⊤) _ _ (fun (i : A.index) ↦ ?_)
  change (A.chart i).baseMap.appTop (u : Γ(S, ⊤)) = (A.chart i).baseMap.appTop 1
  let c := A.chart i; have hi := (h i).symm
  rw [modelDifferential, conormalBasisPullback_unitSmulIso, ← modelDifferential] at hi
  conv_rhs at hi => rw [← unitSmulIso_one (c.modelDifferential ω₁)]
  have hval : (c.baseIso.inv ≫ c.baseMap).appTop (u : Γ(S, ⊤)) =
      (c.baseIso.inv ≫ c.baseMap).appTop 1 := by
    simpa [Units.coe_map, map_one] using congrArg Units.val ((unitSmulIso_inj _ _ _).mp hi)
  have hcomp : c.baseMap = c.baseIso.hom ≫ (c.baseIso.inv ≫ c.baseMap) := by simp
  dsimp only [c] at hcomp hval ⊢
  rw [hcomp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply, hval]

section AdaptedXCoord

variable {P Q : S ⟶ E.carrier} (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)
  (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s) (ω : E.InvariantDifferential)

private theorem appTop_adaptedXCoordSection_id
    {k c : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k.baseMap) :
    h.appTop (c.adaptedXCoordSection hP hQ hP₀ hQ₀ ω) =
      k.adaptedXCoordSection hP hQ hP₀ hQ₀ ω := by
  simpa only [invariantDifferentialPullback_id] using
    appTop_adaptedXCoordSection (.id_horiz E.structureMap)
      (by rw [Category.comp_id, Category.id_comp]) hP hQ hP₀ hQ₀ hP hQ hP₀ hQ₀
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, Category.id_comp])
      (by simpa using hh) ω

/-- The **`ω`-adapted `x`-coordinate** of `(P, Q)` (KM 2.2.9), as `S ⟶ Spec ℤ[T]`. -/
noncomputable def adaptedXCoordMap :
    S ⟶ Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))) :=
  E.glueChartSectionMap (fun c ↦ c.adaptedXCoordSection hP hQ hP₀ hQ₀ ω)
    (E.appTop_adaptedXCoordSection_id hP hQ hP₀ hQ₀ ω)

/-- The **`ω`-adapted `x`-coordinate** of `(P, Q)` (KM 2.2.9), as a global function in `Γ(S, ⊤)`. -/
noncomputable def adaptedXCoord : Γ(S, ⊤) :=
  E.glueChartSection (fun c ↦ c.adaptedXCoordSection hP hQ hP₀ hQ₀ ω)
    (E.appTop_adaptedXCoordSection_id hP hQ hP₀ hQ₀ ω)

/-- `adaptedXCoordMap` is the morphism to `Spec ℤ[T]` with coordinate `adaptedXCoord`. -/
theorem adaptedXCoordMap_eq :
    E.adaptedXCoordMap hP hQ hP₀ hQ₀ ω =
      (AffineSpace.toSpecMvPolyIntEquiv PUnit).symm fun _ ↦ E.adaptedXCoord hP hQ hP₀ hQ₀ ω :=
  E.glueChartSectionMap_eq _ _

/-- On a chart `c`, `adaptedXCoord` restricts to `WeierstrassCurve.projModelAdaptedXCoord`. -/
theorem baseMap_appTop_adaptedXCoord (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.baseMap.appTop (E.adaptedXCoord hP hQ hP₀ hQ₀ ω) =
      c.baseIso.hom.appTop ((ΓSpecIso c.ring).inv (c.equation.projModelAdaptedXCoord
        (c.modelPoint_projModelOver hP) (c.modelPoint_projModelOver hQ)
        (c.modelPoint_apply_ne hP hP₀) (c.modelPoint_apply_ne hQ hQ₀) (c.modelDifferential ω))) :=
  E.baseMap_appTop_glueChartSection _ _ c

/-- A global function on `S` agreeing with `projModelAdaptedXCoord` on every chart of an atlas
equals `E.adaptedXCoord hP hQ hP₀ hQ₀ ω`. -/
theorem eq_adaptedXCoord_of_atlas (A : PointedWeierstrassAtlas E.structureMap E.zero) {x : Γ(S, ⊤)}
    (hx : ∀ i, (A.chart i).baseMap.appTop x =
      (A.chart i).baseIso.hom.appTop ((ΓSpecIso (A.chart i).ring).inv
        ((A.chart i).equation.projModelAdaptedXCoord ((A.chart i).modelPoint_projModelOver hP)
          ((A.chart i).modelPoint_projModelOver hQ) ((A.chart i).modelPoint_apply_ne hP hP₀)
          ((A.chart i).modelPoint_apply_ne hQ hQ₀) ((A.chart i).modelDifferential ω)))) :
    x = E.adaptedXCoord hP hQ hP₀ hQ₀ ω :=
  E.eq_glueChartSection_of_atlas _ _ A hx

end AdaptedXCoord

section BaseChange

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {f : S' ⟶ S} {g : E'.carrier ⟶ E.carrier}

/-- **Invariance of `adaptedXCoord` under pointed cartesian squares.** -/
theorem appTop_adaptedXCoord_of_isPullback
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    {P Q : S ⟶ E.carrier} {P' Q' : S' ⟶ E'.carrier}
    (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)
    (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s)
    (hP' : P' ≫ E'.structureMap = 𝟙 S') (hQ' : Q' ≫ E'.structureMap = 𝟙 S')
    (hP'₀ : ∀ s, P' s ≠ E'.zero s) (hQ'₀ : ∀ s, Q' s ≠ E'.zero s)
    (hPg : P' ≫ g = f ≫ P) (hQg : Q' ≫ g = f ≫ Q) (ω : E.InvariantDifferential) :
    f.appTop (E.adaptedXCoord hP hQ hP₀ hQ₀ ω) =
      E'.adaptedXCoord hP' hQ' hP'₀ hQ'₀ (invariantDifferentialPullback hg h0 ω) :=
  E.appTop_glueChartSection_of_forall_chart _ _ E' _
    (E'.appTop_adaptedXCoordSection_id hP' hQ' hP'₀ hQ'₀ _) f
    fun hh ↦ appTop_adaptedXCoordSection hg h0 hP hQ hP₀ hQ₀ hP' hQ' hP'₀ hQ'₀ hPg hQg hh ω

end BaseChange

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry

namespace WeierstrassCurve

open TauCeti.AlgebraicGeometry

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- The canonical Weierstrass invariant differential on `W.toEllipticCurveGeom`. -/
noncomputable def toEllipticCurveGeomDifferential : W.toEllipticCurveGeom.InvariantDifferential :=
  conormalBasisPullbackOfIso W.projModelZero_projModelOver W.toEllipticCurveGeom.zero_comp
    (toEllipticCurveGeomIso W) (toEllipticCurveGeomIso_hom_projModelOver W)
    (zero_toEllipticCurveGeomIso_hom W) W.weierstrassDifferential

/-- `toEllipticCurveGeomDifferential` is `W.weierstrassDifferential` pulled back along
`toEllipticCurveGeomIso W`. -/
theorem toEllipticCurveGeomDifferential_def :
    W.toEllipticCurveGeomDifferential =
      conormalBasisPullbackOfIso W.projModelZero_projModelOver W.toEllipticCurveGeom.zero_comp
        (toEllipticCurveGeomIso W) (toEllipticCurveGeomIso_hom_projModelOver W)
        (zero_toEllipticCurveGeomIso_hom W) W.weierstrassDifferential := by rfl

/-- Pulling `W.toEllipticCurveGeomDifferential` back along `(toEllipticCurveGeomIso W).symm`
recovers `W.weierstrassDifferential`. -/
@[simp]
theorem conormalBasisPullbackOfIso_toEllipticCurveGeomDifferential :
    conormalBasisPullbackOfIso W.toEllipticCurveGeom.zero_comp W.projModelZero_projModelOver
        (toEllipticCurveGeomIso W).symm (toEllipticCurveGeomIso_inv_structureMap W)
        (projModelZero_toEllipticCurveGeomIso_inv W) W.toEllipticCurveGeomDifferential =
      W.weierstrassDifferential := by
  rw [toEllipticCurveGeomDifferential, conormalBasisPullbackOfIso_symm_apply]

/-- On `W.toEllipticCurveGeom`, `adaptedXCoord` agrees with `W.projModelAdaptedXCoord`. -/
theorem adaptedXCoord_toEllipticCurveGeom {P Q : Spec (.of R) ⟶ W.toEllipticCurveGeom.carrier}
    (hP : P ≫ W.toEllipticCurveGeom.structureMap = 𝟙 _)
    (hQ : Q ≫ W.toEllipticCurveGeom.structureMap = 𝟙 _)
    (hP₀ : ∀ s, P s ≠ W.toEllipticCurveGeom.zero s) (hQ₀ : ∀ s, Q s ≠ W.toEllipticCurveGeom.zero s)
    (ω : W.toEllipticCurveGeom.InvariantDifferential) :
    W.toEllipticCurveGeom.adaptedXCoord hP hQ hP₀ hQ₀ ω =
      (ΓSpecIso (.of R)).inv (W.projModelAdaptedXCoord
        (P := P ≫ (toEllipticCurveGeomIso W).hom) (Q := Q ≫ (toEllipticCurveGeomIso W).hom)
        (by rw [Category.assoc, toEllipticCurveGeomIso_hom_projModelOver, hP])
        (by rw [Category.assoc, toEllipticCurveGeomIso_hom_projModelOver, hQ])
        (W.comp_toEllipticCurveGeomIso_hom_ne_projModelZero hP₀)
        (W.comp_toEllipticCurveGeomIso_hom_ne_projModelZero hQ₀)
        (conormalBasisPullbackOfIso W.toEllipticCurveGeom.zero_comp W.projModelZero_projModelOver
          (toEllipticCurveGeomIso W).symm (toEllipticCurveGeomIso_inv_structureMap W)
          (projModelZero_toEllipticCurveGeomIso_inv W) ω)) := by
  let c := toEllipticCurveGeomChart W
  have h := W.toEllipticCurveGeom.baseMap_appTop_adaptedXCoord hP hQ hP₀ hQ₀ ω c
  let ω' := conormalBasisPullbackOfIso W.toEllipticCurveGeom.zero_comp W.projModelZero_projModelOver
    (toEllipticCurveGeomIso W).symm (toEllipticCurveGeomIso_inv_structureMap W)
    (projModelZero_toEllipticCurveGeomIso_inv W) ω
  have hω_c : c.modelDifferential ω = ω' := by
    dsimp only [ω']
    rw [PointedWeierstrassChart.modelDifferential_def, conormalBasisPullbackOfIso_def]
    exact conormalBasisPullback_congr W.toEllipticCurveGeom.zero_comp W.projModelZero_projModelOver
      (by simp [c, toEllipticCurveGeomChart]) (by simp [c, toEllipticCurveGeomChart]) _ _ _ _ ω
  have hcongr : ∀ {P₁ P₂ Q₁ Q₂ : Spec (.of R) ⟶ W.projModel} (_ : P₁ = P₂) (_ : Q₁ = Q₂)
      {ω₁ ω₂} (_ : ω₁ = ω₂) (hP₁ hQ₁ hP₁₀ hQ₁₀ hP₂ hQ₂ hP₂₀ hQ₂₀),
      W.projModelAdaptedXCoord (P := P₁) (Q := Q₁) hP₁ hQ₁ hP₁₀ hQ₁₀ ω₁ =
        W.projModelAdaptedXCoord (P := P₂) (Q := Q₂) hP₂ hQ₂ hP₂₀ hQ₂₀ ω₂ := by
    rintro _ _ _ _ rfl rfl _ _ rfl _ _ _ _ _ _ _ _; rfl
  dsimp only [c, toEllipticCurveGeomChart] at h
  simp only [Scheme.Hom.id_appTop, Iso.refl_hom, CommRingCat.id_apply] at h; rw [h]; congr 1
  exact hcongr (W.toEllipticCurveGeomChart_modelPoint hP)
    (W.toEllipticCurveGeomChart_modelPoint hQ) hω_c _ _ _ _ _ _ _ _

end WeierstrassCurve
