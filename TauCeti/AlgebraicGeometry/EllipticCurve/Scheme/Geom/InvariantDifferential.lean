/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Conormal
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Glue
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.OfWeierstrass
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.LegendreNormalForm

/-!
# Invariant differentials and adapted `x`-coordinates on elliptic curves over schemes

Let `E` be an elliptic curve over a scheme `S`. Since `E ⟶ S` is separated and smooth of relative
dimension one, the zero section `E.zero : S ⟶ E` is a relative effective Cartier divisor on `E`,
and its conormal sheaf `ω_{E/S} = E.zero.conormalSheaf` (`ℐ / ℐ²` pulled back along `E.zero`) is
an invertible `𝒪_S`-module. Following Katz–Mazur (KM 2.2.8) and Deligne–Rapoport (II.1.5), a
nowhere-vanishing **invariant differential** on `E/S` is a global basis of `ω_{E/S}`, i.e. an
isomorphism `𝟙_ S.Modules ≅ E.zero.conormalSheaf` (`EllipticCurveGeom.InvariantDifferential E`).

Along any pointed cartesian square `(g : E' ⟶ E, f : S' ⟶ S)`, an invariant differential `ω` on
`E` pulls back to `EllipticCurveGeom.invariantDifferentialPullback hg h0 ω` on `E'` via
`Scheme.Hom.conormalBasisPullback`. On every pointed Weierstrass chart `c` of `E`, pulling `ω`
back to the projective model of `c.equation` yields `c.modelDifferential ω`, and two invariant
differentials on `E` are equal whenever their chart pullbacks agree on a pointed Weierstrass atlas
(`EllipticCurveGeom.invariantDifferential_ext_of_atlas`), because any two bases of an invertible
`𝒪_S`-module differ by a unique global unit (`Scheme.Modules.existsUnique_unitSmulIso_eq`).

Given two sections `P, Q : S ⟶ E` missing the zero section at every point of `S` and an invariant
differential `ω : E.InvariantDifferential`, the `ω`-adapted `x`-coordinates
`WeierstrassCurve.projModelAdaptedXCoord` on the pointed Weierstrass charts of `E` agree on chart
overlaps (`WeierstrassCurve.map_projModelAdaptedXCoord_of_isPullback`) and therefore glue to a
global function `EllipticCurveGeom.adaptedXCoord E hP hQ hP₀ hQ₀ ω : Γ(S, ⊤)` (equivalently a
morphism `EllipticCurveGeom.adaptedXCoordMap E hP hQ hP₀ hQ₀ ω : S ⟶ Spec ℤ[T]`), compatible with
arbitrary pointed cartesian squares (`EllipticCurveGeom.appTop_adaptedXCoord_of_isPullback`).

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.InvariantDifferential E`: an isomorphism
  `𝟙_ S.Modules ≅ E.zero.conormalSheaf`, i.e. a nowhere-vanishing invariant differential on `E/S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.invariantDifferentialPullback`: pullback of an
  invariant differential along a pointed cartesian square of elliptic curves.
* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.modelDifferential`: the conormal basis on the
  projective model of a chart's equation induced by an invariant differential on `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.adaptedXCoordMap` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.adaptedXCoord`: the `ω`-adapted `x`-coordinate of
  `(P, Q)` normalized by `x(P) = 0`, as a morphism `S ⟶ Spec ℤ[T]` and as an element of `Γ(S, ⊤)`.
* `WeierstrassCurve.toEllipticCurveGeomDifferential`: the canonical Weierstrass differential on
  `W.toEllipticCurveGeom`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.invariantDifferential_ext_of_atlas`: two invariant
  differentials agreeing on every chart of a pointed Weierstrass atlas are equal.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.baseMap_appTop_adaptedXCoord` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.eq_adaptedXCoord_of_atlas`: local formula and atlas
  characterization of `adaptedXCoord`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.appTop_adaptedXCoord_of_isPullback`: compatibility
  of `adaptedXCoord` with pointed cartesian squares of elliptic curves.
* `WeierstrassCurve.adaptedXCoord_toEllipticCurveGeom`: on `W.toEllipticCurveGeom`,
  `adaptedXCoord` agrees with `W.projModelAdaptedXCoord`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.8 and 2.2.9.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.5.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- The zero section of an elliptic curve `E` over `S` is a relative effective Cartier divisor on
`E` over `S`, since `E ⟶ S` is separated and smooth of relative dimension one. -/
theorem isRelativeEffectiveCartier_zero_ker :
    E.zero.ker.IsRelativeEffectiveCartier E.structureMap :=
  Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension E.zero E.zero_comp

/-- The zero section of an elliptic curve `E` over `S` is an effective Cartier divisor on `E`. -/
theorem isEffectiveCartier_zero_ker : E.zero.ker.IsEffectiveCartier :=
  E.isRelativeEffectiveCartier_zero_ker.isEffectiveCartier

/-- A nowhere-vanishing **invariant differential** on an elliptic curve `E` over `S` (KM 2.2.8):
a global basis `𝟙_ S.Modules ≅ E.zero.conormalSheaf` of the conormal sheaf `ω_{E/S}` of the zero
section. -/
abbrev InvariantDifferential : Type u :=
  𝟙_ S.Modules ≅ E.zero.conormalSheaf

/-! ### Pullback of invariant differentials -/

section Pullback

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {f : S' ⟶ S}
  {g : E'.carrier ⟶ E.carrier}

/-- Pullback of an invariant differential along a pointed cartesian square `(g, f)` from `E'/S'`
to `E/S`. -/
noncomputable def invariantDifferentialPullback
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    (ω : E.InvariantDifferential) : E'.InvariantDifferential :=
  Scheme.Hom.conormalBasisPullback E.zero_comp E'.zero_comp hg h0 ω

/-- `invariantDifferentialPullback` is `Scheme.Hom.conormalBasisPullback`. -/
theorem invariantDifferentialPullback_def
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    (ω : E.InvariantDifferential) :
    invariantDifferentialPullback hg h0 ω =
      Scheme.Hom.conormalBasisPullback E.zero_comp E'.zero_comp hg h0 ω :=
  (rfl)

/-- Pulling back an invariant differential along the identity square is the identity. -/
@[simp]
theorem invariantDifferentialPullback_id (ω : E.InvariantDifferential) :
    invariantDifferentialPullback (IsPullback.id_horiz E.structureMap)
      (by rw [Category.comp_id, Category.id_comp]) ω = ω :=
  Scheme.Hom.conormalBasisPullback_id E.zero_comp _ _ ω

/-- Pulling back an invariant differential is contravariantly functorial under horizontal pasting
of pointed cartesian squares. -/
theorem invariantDifferentialPullback_comp {S'' : Scheme.{u}} {E'' : EllipticCurveGeom S''}
    {f' : S'' ⟶ S'} {g' : E''.carrier ⟶ E'.carrier}
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    (hg' : IsPullback g' E''.structureMap E'.structureMap f') (h0' : E''.zero ≫ g' = f' ≫ E'.zero)
    (ω : E.InvariantDifferential) :
    invariantDifferentialPullback hg' h0' (invariantDifferentialPullback hg h0 ω) =
      invariantDifferentialPullback (hg'.paste_horiz hg)
        (by rw [reassoc_of% h0', h0, Category.assoc]) ω :=
  Scheme.Hom.conormalBasisPullback_comp E.zero_comp E'.zero_comp
    E''.zero_comp hg h0 hg' h0' ω

/-- `invariantDifferentialPullback` depends only on the morphisms `(f, g)` and `ω`. -/
theorem invariantDifferentialPullback_congr {f₁ f₂ : S' ⟶ S} {g₁ g₂ : E'.carrier ⟶ E.carrier}
    (hf : f₁ = f₂) (hg : g₁ = g₂)
    (hp₁ : IsPullback g₁ E'.structureMap E.structureMap f₁) (h0₁ : E'.zero ≫ g₁ = f₁ ≫ E.zero)
    (hp₂ : IsPullback g₂ E'.structureMap E.structureMap f₂) (h0₂ : E'.zero ≫ g₂ = f₂ ≫ E.zero)
    (ω : E.InvariantDifferential) :
    invariantDifferentialPullback hp₁ h0₁ ω = invariantDifferentialPullback hp₂ h0₂ ω :=
  Scheme.Hom.conormalBasisPullback_congr E.zero_comp E'.zero_comp
    hf hg hp₁ h0₁ hp₂ h0₂ ω

/-- Pulling back `u • ω` scales the pulled-back differential by `f^* u`. -/
theorem invariantDifferentialPullback_unitSmulIso
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    (u : Γ(S, ⊤)ˣ) (ω : E.InvariantDifferential) :
    invariantDifferentialPullback hg h0 (Scheme.Modules.unitSmulIso u ω) =
      Scheme.Modules.unitSmulIso (Units.map f.appTop.hom.toMonoidHom u)
        (invariantDifferentialPullback hg h0 ω) :=
  Scheme.Hom.conormalBasisPullback_unitSmulIso E.zero_comp E'.zero_comp hg h0 u ω

end Pullback

end EllipticCurveGeom

/-! ### Chart pullbacks and atlas extensionality -/

namespace PointedWeierstrassChart

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}

/-- The conormal basis of the zero section on the projective model of a pointed Weierstrass chart
`c` of `E` obtained by pulling back an invariant differential `ω` on `E`. -/
noncomputable def modelDifferential (c : PointedWeierstrassChart E.structureMap E.zero)
    (ω : E.InvariantDifferential) :
    𝟙_ (Spec c.ring).Modules ≅ c.equation.projModelZero.conormalSheaf :=
  Scheme.Hom.conormalBasisPullback E.zero_comp c.equation.projModelZero_projModelOver
    c.isPullback_modelIso_inv_toTotal c.projModelZero_modelIso_inv_toTotal ω

/-- `modelDifferential` is `Scheme.Hom.conormalBasisPullback` along the chart projection. -/
theorem modelDifferential_def (c : PointedWeierstrassChart E.structureMap E.zero)
    (ω : E.InvariantDifferential) :
    c.modelDifferential ω =
      Scheme.Hom.conormalBasisPullback E.zero_comp c.equation.projModelZero_projModelOver
        c.isPullback_modelIso_inv_toTotal c.projModelZero_modelIso_inv_toTotal ω :=
  (rfl)

/-- If `g : X' ⟶ X` lies in a cartesian square over `f : S' ⟶ S` and carries `P'` to `P`, then on
charts `k` and `c` related by `h : k.base ⟶ c.base` over `f`, the morphism `modelMap hg hh` carries
the model point of `P'` to that of `P`. -/
theorem modelPoint_modelMap {X S' X' : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}
    {π' : X' ⟶ S'} {zero' : S' ⟶ X'} {g : X' ⟶ X} {f : S' ⟶ S}
    (hg : IsPullback g π' π f) {k : PointedWeierstrassChart π' zero'}
    {c : PointedWeierstrassChart π zero} {h : k.base ⟶ c.base} (hh : h ≫ c.baseMap = k.baseMap ≫ f)
    {P : S ⟶ X} {P' : S' ⟶ X'} (hP : P ≫ π = 𝟙 S) (hP' : P' ≫ π' = 𝟙 S')
    (hPg : P' ≫ g = f ≫ P) :
    k.modelPoint hP' ≫ modelMap hg hh = (k.baseIso.inv ≫ h ≫ c.baseIso.hom) ≫ c.modelPoint hP := by
  have hchart : k.chartPoint hP' ≫ carrierMap hg hh = h ≫ c.chartPoint hP :=
    c.isPullback.hom_ext (by simp [hPg, reassoc_of% hh]) (by simp)
  rw [modelPoint_def, Category.assoc, Category.assoc, modelIso_hom_modelMap, reassoc_of% hchart,
    chartPoint_modelIso_hom, Category.assoc, Category.assoc]

/-- Along `modelMap hg hh`, the model differential of `ω` on `c` pulls back to the model
differential of `invariantDifferentialPullback hg h0 ω` on `k`. -/
theorem conormalBasisPullback_modelDifferential {S' : Scheme.{u}} {E' : EllipticCurveGeom S'}
    {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S}
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    {k : PointedWeierstrassChart E'.structureMap E'.zero}
    {c : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k.baseMap ≫ f) (ω : E.InvariantDifferential) :
    Scheme.Hom.conormalBasisPullback c.equation.projModelZero_projModelOver
        k.equation.projModelZero_projModelOver (isPullback_modelMap hg hh)
        (projModelZero_modelMap hg hh h0) (c.modelDifferential ω) =
      k.modelDifferential (EllipticCurveGeom.invariantDifferentialPullback hg h0 ω) := by
  rw [modelDifferential, modelDifferential, EllipticCurveGeom.invariantDifferentialPullback,
    Scheme.Hom.conormalBasisPullback_comp, Scheme.Hom.conormalBasisPullback_comp]
  refine Scheme.Hom.conormalBasisPullback_congr E.zero_comp
    k.equation.projModelZero_projModelOver ?_ ?_ _ _ _ _ ω
  · simp [hh]
  · rw [← cancel_epi k.modelIso.hom, modelIso_hom_modelMap_assoc, Iso.hom_inv_id_assoc,
      carrierMap_toTotal]
    simp

-- The `ω`-adapted `x`-coordinate of `(P, Q)` on the base of a pointed Weierstrass chart `c`.
private noncomputable def adaptedXCoordSection (c : PointedWeierstrassChart E.structureMap E.zero)
    {P Q : S ⟶ E.carrier} (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)
    (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s) (ω : E.InvariantDifferential) :
    Γ(c.base, ⊤) :=
  c.baseIso.hom.appTop ((Scheme.ΓSpecIso c.ring).inv
    (c.equation.projModelAdaptedXCoord (c.modelPoint_projModelOver hP)
      (c.modelPoint_projModelOver hQ) (c.modelPoint_apply_ne hP hP₀)
      (c.modelPoint_apply_ne hQ hQ₀) (c.modelDifferential ω)))

-- The `ω`-adapted `x`-coordinate of `(P, Q)` on a chart `c`, as a morphism to `Spec ℤ[T]`.
private noncomputable def adaptedXCoordChartMap (c : PointedWeierstrassChart E.structureMap E.zero)
    {P Q : S ⟶ E.carrier} (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)
    (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s) (ω : E.InvariantDifferential) :
    c.base ⟶ Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))) :=
  (AffineSpace.toSpecMvPolyIntEquiv PUnit).symm fun _ ↦
    c.adaptedXCoordSection hP hQ hP₀ hQ₀ ω

-- Compatibility of `adaptedXCoordSection` along morphisms of charts over a base change square.
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
  have hF := isPullback_modelMap hg hh
  have hz := projModelZero_modelMap hg hh h0
  have hPF := modelPoint_modelMap hg hh hP hP' hPg
  have hQF := modelPoint_modelMap hg hh hQ hQ' hQg
  have hω := conormalBasisPullback_modelDifferential hg h0 hh ω
  rw [← hφ, ← CommRingCat.ofHom_hom φ] at hF hz hPF hQF
  have hx := WeierstrassCurve.map_projModelAdaptedXCoord_of_isPullback hF hz
    (k.modelPoint_projModelOver hP') (k.modelPoint_projModelOver hQ')
    (k.modelPoint_apply_ne hP' hP'₀) (k.modelPoint_apply_ne hQ' hQ'₀)
    (c.modelPoint_projModelOver hP) (c.modelPoint_projModelOver hQ)
    (c.modelPoint_apply_ne hP hP₀) (c.modelPoint_apply_ne hQ hQ₀)
    hPF hQF (c.modelDifferential ω)
  have hcongr : Scheme.Hom.conormalBasisPullback c.equation.projModelZero_projModelOver
      k.equation.projModelZero_projModelOver hF hz (c.modelDifferential ω) =
      k.modelDifferential (EllipticCurveGeom.invariantDifferentialPullback hg h0 ω) := by
    rw [← hω]
    exact Scheme.Hom.conormalBasisPullback_congr c.equation.projModelZero_projModelOver
      k.equation.projModelZero_projModelOver (by rw [CommRingCat.ofHom_hom, hφ]) rfl _ _ _ _ _
  rw [hcongr] at hx
  have hh' : h ≫ c.baseIso.hom = k.baseIso.hom ≫ Spec.map φ := by simp [hφ]
  rw [adaptedXCoordSection, adaptedXCoordSection, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, hh', Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply _ (Spec.map φ).appTop, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  exact congrArg (k.baseIso.hom.appTop ∘ (Scheme.ΓSpecIso k.ring).inv) hx

private theorem comp_adaptedXCoordChartMap {S' : Scheme.{u}} {E' : EllipticCurveGeom S'}
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
    h ≫ c.adaptedXCoordChartMap hP hQ hP₀ hQ₀ ω =
      k.adaptedXCoordChartMap hP' hQ' hP'₀ hQ'₀
        (EllipticCurveGeom.invariantDifferentialPullback hg h0 ω) := by
  refine (AffineSpace.toSpecMvPolyIntEquiv PUnit).injective (funext fun _ ↦ ?_)
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp, adaptedXCoordChartMap, adaptedXCoordChartMap,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact appTop_adaptedXCoordSection hg h0 hP hQ hP₀ hQ₀ hP' hQ' hP'₀ hQ'₀ hPg hQg hh ω

end PointedWeierstrassChart

namespace EllipticCurveGeom

open PointedWeierstrassChart

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

-- Global functions on `S` agreeing on the bases of every chart of an atlas are equal.
private theorem appTop_ext_of_atlas (A : PointedWeierstrassAtlas E.structureMap E.zero)
    {x y : Γ(S, ⊤)} (h : ∀ i, (A.chart i).baseMap.appTop x = (A.chart i).baseMap.appTop y) :
    x = y := by
  have hmap : (AffineSpace.toSpecMvPolyIntEquiv PUnit).symm (fun _ ↦ x) =
      (AffineSpace.toSpecMvPolyIntEquiv PUnit).symm (fun _ ↦ y) := by
    refine A.hom_ext (𝟙 S) _ _ fun i ↦ ?_
    rw [← Category.comp_id (pullback.fst _ _), pullback.condition, Category.assoc, Category.assoc]
    congr 1
    refine (AffineSpace.toSpecMvPolyIntEquiv PUnit).injective (funext fun _ ↦ ?_)
    rw [AffineSpace.toSpecMvPolyIntEquiv_comp, Equiv.apply_symm_apply,
      AffineSpace.toSpecMvPolyIntEquiv_comp, Equiv.apply_symm_apply, h i]
  simpa using congr($(congrArg (AffineSpace.toSpecMvPolyIntEquiv PUnit) hmap) PUnit.unit)

/-- **Invariant differentials are determined on any pointed Weierstrass atlas.** Two invariant
differentials on `E` whose pullbacks `c.modelDifferential` agree on every chart of a pointed
Weierstrass atlas `A` of `E` are equal. -/
theorem invariantDifferential_ext_of_atlas (A : PointedWeierstrassAtlas E.structureMap E.zero)
    {ω₁ ω₂ : E.InvariantDifferential}
    (h : ∀ i, (A.chart i).modelDifferential ω₁ = (A.chart i).modelDifferential ω₂) :
    ω₁ = ω₂ := by
  obtain ⟨u, rfl, -⟩ := Scheme.Modules.existsUnique_unitSmulIso_eq ω₂ ω₁
  suffices hu : u = 1 by rw [hu, Scheme.Modules.unitSmulIso_one]
  ext
  refine E.appTop_ext_of_atlas A fun i ↦ ?_
  let c := A.chart i
  have hi := (h i).symm
  rw [modelDifferential, Scheme.Hom.conormalBasisPullback_unitSmulIso, ← modelDifferential] at hi
  conv_rhs at hi => rw [← Scheme.Modules.unitSmulIso_one (c.modelDifferential ω₁)]
  have hu_i : Units.map (c.baseIso.inv ≫ c.baseMap).appTop.hom.toMonoidHom u = 1 :=
    (Scheme.Modules.unitSmulIso_inj _ _ _).mp hi
  have hval : (c.baseIso.inv ≫ c.baseMap).appTop (u : Γ(S, ⊤)) =
      (c.baseIso.inv ≫ c.baseMap).appTop 1 := by
    simpa [map_one] using congrArg Units.val hu_i
  have hcomp : c.baseMap = c.baseIso.hom ≫ (c.baseIso.inv ≫ c.baseMap) := by simp
  rw [Units.val_one, hcomp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply,
    hval]

/-! ### The glued `ω`-adapted `x`-coordinate -/

section AdaptedXCoord

variable {P Q : S ⟶ E.carrier} (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)
  (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s) (ω : E.InvariantDifferential)

private noncomputable def pieceAdaptedXCoordMap
    (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback (𝟙 S) c.baseMap ⟶ Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))) :=
  pullback.snd _ _ ≫ c.adaptedXCoordChartMap hP hQ hP₀ hQ₀ ω

private theorem map_pieceAdaptedXCoordMap
    {k c : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k.baseMap) :
    pullback.map (𝟙 S) k.baseMap (𝟙 S) c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫
      pieceAdaptedXCoordMap E hP hQ hP₀ hQ₀ ω c =
      pieceAdaptedXCoordMap E hP hQ hP₀ hQ₀ ω k := by
  rw [pieceAdaptedXCoordMap, pieceAdaptedXCoordMap, pullback.lift_snd_assoc, Category.assoc,
    comp_adaptedXCoordChartMap (IsPullback.id_horiz E.structureMap)
      (by rw [Category.comp_id, Category.id_comp]) hP hQ hP₀ hQ₀ hP hQ hP₀ hQ₀
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, Category.id_comp])
      (by simpa using hh) ω,
    invariantDifferentialPullback_id]

/-- The **`ω`-adapted `x`-coordinate** of `(P, Q)` normalized by `x(P) = 0` (KM 2.2.9), as a
morphism `S ⟶ Spec ℤ[T]` to the affine line. -/
noncomputable def adaptedXCoordMap :
    S ⟶ Spec (.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))) :=
  glueMorphisms (pieceAdaptedXCoordMap E hP hQ hP₀ hQ₀ ω)
    (map_pieceAdaptedXCoordMap E hP hQ hP₀ hQ₀ ω)

/-- The **`ω`-adapted `x`-coordinate** of `(P, Q)` normalized by `x(P) = 0` (KM 2.2.9), as a
global function in `Γ(S, ⊤)`. On every pointed Weierstrass chart `c` of `E`, it restricts to
`WeierstrassCurve.projModelAdaptedXCoord` of `(P, Q, ω)` (`baseMap_appTop_adaptedXCoord`). -/
noncomputable def adaptedXCoord : Γ(S, ⊤) :=
  AffineSpace.toSpecMvPolyIntEquiv PUnit (E.adaptedXCoordMap hP hQ hP₀ hQ₀ ω) PUnit.unit

/-- `adaptedXCoordMap` is the morphism to `Spec ℤ[T]` with coordinate `adaptedXCoord`. -/
theorem adaptedXCoordMap_eq :
    E.adaptedXCoordMap hP hQ hP₀ hQ₀ ω =
      (AffineSpace.toSpecMvPolyIntEquiv PUnit).symm fun _ ↦ E.adaptedXCoord hP hQ hP₀ hQ₀ ω :=
  (Equiv.eq_symm_apply _).mpr (funext fun _ ↦ rfl)

private theorem baseMap_comp_adaptedXCoordMap
    (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.baseMap ≫ E.adaptedXCoordMap hP hQ hP₀ hQ₀ ω =
      c.adaptedXCoordChartMap hP hQ hP₀ hQ₀ ω := by
  have h : pullback.fst (𝟙 S) c.baseMap ≫ E.adaptedXCoordMap hP hQ hP₀ hQ₀ ω =
      pieceAdaptedXCoordMap E hP hQ hP₀ hQ₀ ω c :=
    fst_glueMorphisms _ (map_pieceAdaptedXCoordMap E hP hQ hP₀ hQ₀ ω) c
  calc c.baseMap ≫ E.adaptedXCoordMap hP hQ hP₀ hQ₀ ω
      = pullback.lift (f := 𝟙 S) (g := c.baseMap) c.baseMap (𝟙 c.base) (by simp) ≫
          pullback.fst _ _ ≫ E.adaptedXCoordMap hP hQ hP₀ hQ₀ ω := by
        rw [pullback.lift_fst_assoc]
    _ = c.adaptedXCoordChartMap hP hQ hP₀ hQ₀ ω := by
        rw [h, pieceAdaptedXCoordMap, pullback.lift_snd_assoc, Category.id_comp]

/-- **The adapted `x`-coordinate on a chart.** On the base of a pointed Weierstrass chart `c` of
`E`, `adaptedXCoord` agrees with `WeierstrassCurve.projModelAdaptedXCoord` on the projective model
of `c.equation`. -/
theorem baseMap_appTop_adaptedXCoord (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.baseMap.appTop (E.adaptedXCoord hP hQ hP₀ hQ₀ ω) =
      c.baseIso.hom.appTop ((Scheme.ΓSpecIso c.ring).inv
        (c.equation.projModelAdaptedXCoord (c.modelPoint_projModelOver hP)
          (c.modelPoint_projModelOver hQ) (c.modelPoint_apply_ne hP hP₀)
          (c.modelPoint_apply_ne hQ hQ₀) (c.modelDifferential ω))) := by
  rw [adaptedXCoord, ← AffineSpace.toSpecMvPolyIntEquiv_comp, baseMap_comp_adaptedXCoordMap,
    adaptedXCoordChartMap, Equiv.apply_symm_apply, adaptedXCoordSection]

/-- **The adapted `x`-coordinate is determined by any atlas.** A global function on `S` agreeing
with `projModelAdaptedXCoord` on every chart of a pointed Weierstrass atlas of `E` equals
`E.adaptedXCoord hP hQ hP₀ hQ₀ ω`. -/
theorem eq_adaptedXCoord_of_atlas (A : PointedWeierstrassAtlas E.structureMap E.zero)
    {x : Γ(S, ⊤)}
    (hx : ∀ i, (A.chart i).baseMap.appTop x =
      (A.chart i).baseIso.hom.appTop ((Scheme.ΓSpecIso (A.chart i).ring).inv
        ((A.chart i).equation.projModelAdaptedXCoord
          ((A.chart i).modelPoint_projModelOver hP)
          ((A.chart i).modelPoint_projModelOver hQ)
          ((A.chart i).modelPoint_apply_ne hP hP₀)
          ((A.chart i).modelPoint_apply_ne hQ hQ₀)
          ((A.chart i).modelDifferential ω)))) :
    x = E.adaptedXCoord hP hQ hP₀ hQ₀ ω :=
  E.appTop_ext_of_atlas A fun i ↦
    (hx i).trans (E.baseMap_appTop_adaptedXCoord hP hQ hP₀ hQ₀ ω _).symm

end AdaptedXCoord

section BaseChange

variable {E} {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {f : S' ⟶ S}
  {g : E'.carrier ⟶ E.carrier}

/-- **Invariance of `adaptedXCoord` under pointed cartesian squares.** Let `(g, f)` be a pointed
cartesian square from `E'/S'` to `E/S` carrying sections `(P', Q')` to `(P, Q)`. Then `f.appTop`
maps the `ω`-adapted `x`-coordinate of `(P, Q)` on `E` to the `(g^* ω)`-adapted `x`-coordinate of
`(P', Q')` on `E'`. -/
theorem appTop_adaptedXCoord_of_isPullback
    (hg : IsPullback g E'.structureMap E.structureMap f) (h0 : E'.zero ≫ g = f ≫ E.zero)
    {P Q : S ⟶ E.carrier} {P' Q' : S' ⟶ E'.carrier}
    (hP : P ≫ E.structureMap = 𝟙 S) (hQ : Q ≫ E.structureMap = 𝟙 S)
    (hP₀ : ∀ s, P s ≠ E.zero s) (hQ₀ : ∀ s, Q s ≠ E.zero s)
    (hP' : P' ≫ E'.structureMap = 𝟙 S') (hQ' : Q' ≫ E'.structureMap = 𝟙 S')
    (hP'₀ : ∀ s, P' s ≠ E'.zero s) (hQ'₀ : ∀ s, Q' s ≠ E'.zero s)
    (hPg : P' ≫ g = f ≫ P) (hQg : Q' ≫ g = f ≫ Q) (ω : E.InvariantDifferential) :
    f.appTop (E.adaptedXCoord hP hQ hP₀ hQ₀ ω) =
      E'.adaptedXCoord hP' hQ' hP'₀ hQ'₀ (invariantDifferentialPullback hg h0 ω) := by
  choose k c h hh hk using E.exists_chart_comp_baseMap E' f
  refine E'.eq_adaptedXCoord_of_atlas hP' hQ' hP'₀ hQ'₀ _ ⟨S', k, fun s ↦ ⟨s, hk s⟩⟩ fun s ↦ ?_
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← hh s, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, E.baseMap_appTop_adaptedXCoord hP hQ hP₀ hQ₀ ω (c s)]
  exact appTop_adaptedXCoordSection hg h0 hP hQ hP₀ hQ₀ hP' hQ' hP'₀ hQ'₀ hPg hQg (hh s) ω

end BaseChange

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry

/-! ### Comparison with `WeierstrassCurve.toEllipticCurveGeom` -/

namespace WeierstrassCurve

open TauCeti.AlgebraicGeometry

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- The canonical Weierstrass invariant differential `dx / (2y + a₁x + a₃)` on
`W.toEllipticCurveGeom`. -/
noncomputable def toEllipticCurveGeomDifferential : W.toEllipticCurveGeom.InvariantDifferential :=
  Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R))) (g := (toEllipticCurveGeomIso W).hom)
    W.projModelZero_projModelOver W.toEllipticCurveGeom.zero_comp
    (IsPullback.of_horiz_isIso ⟨by rw [toEllipticCurveGeomIso_hom_projModelOver, Category.comp_id]⟩)
    (by rw [zero_toEllipticCurveGeomIso_hom, Category.id_comp]) W.weierstrassDifferential

/-- `toEllipticCurveGeomDifferential` is `W.weierstrassDifferential` pulled back along
`(toEllipticCurveGeomIso W).hom`. -/
theorem toEllipticCurveGeomDifferential_def :
    W.toEllipticCurveGeomDifferential =
      Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R))) (g := (toEllipticCurveGeomIso W).hom)
        W.projModelZero_projModelOver W.toEllipticCurveGeom.zero_comp
        (IsPullback.of_horiz_isIso
          ⟨by rw [toEllipticCurveGeomIso_hom_projModelOver, Category.comp_id]⟩)
        (by rw [zero_toEllipticCurveGeomIso_hom, Category.id_comp]) W.weierstrassDifferential :=
  (rfl)

-- The tautological global chart of `W.toEllipticCurveGeom` over `Spec R`.
private noncomputable abbrev globalChart :
    PointedWeierstrassChart W.toEllipticCurveGeom.structureMap W.toEllipticCurveGeom.zero where
  base := Spec (.of R)
  baseMap := 𝟙 _
  baseMap_open := inferInstance
  ring := .of R
  baseIso := Iso.refl _
  equation := W
  equation_elliptic := inferInstance
  pullbackCarrier := W.toEllipticCurveGeom.carrier
  toTotal := 𝟙 _
  toBase := W.toEllipticCurveGeom.structureMap
  isPullback := .of_id_fst
  modelIso := toEllipticCurveGeomIso W
  modelIso_over := by simp
  pulledZero := W.toEllipticCurveGeom.zero
  pulledZero_toBase := by simp
  pulledZero_toTotal := by simp
  modelIso_zero := by simp

/-- Under `(toEllipticCurveGeomIso W).inv`, the structure morphism of `W.toEllipticCurveGeom` is
`W.projModelOver`. -/
@[reassoc (attr := simp)]
theorem toEllipticCurveGeomIso_inv_structureMap :
    (toEllipticCurveGeomIso W).inv ≫ W.toEllipticCurveGeom.structureMap = W.projModelOver :=
  (Iso.inv_comp_eq _).mpr (toEllipticCurveGeomIso_hom_projModelOver W).symm

/-- Under `(toEllipticCurveGeomIso W).inv`, `W.projModelZero` maps to
`W.toEllipticCurveGeom.zero`. -/
@[reassoc (attr := simp)]
theorem projModelZero_toEllipticCurveGeomIso_inv :
    W.projModelZero ≫ (toEllipticCurveGeomIso W).inv = W.toEllipticCurveGeom.zero :=
  (Iso.comp_inv_eq _).mpr (zero_toEllipticCurveGeomIso_hom W).symm

/-- A section of `W.toEllipticCurveGeom` missing the zero section at every point maps under
`(toEllipticCurveGeomIso W).hom` to a section missing `W.projModelZero` at every point. -/
theorem comp_toEllipticCurveGeomIso_hom_ne_projModelZero
    {P : Spec (.of R) ⟶ W.toEllipticCurveGeom.carrier}
    (hP₀ : ∀ s, P s ≠ W.toEllipticCurveGeom.zero s) (s : Spec (.of R)) :
    (P ≫ (toEllipticCurveGeomIso W).hom) s ≠ W.projModelZero s := fun hs ↦
  hP₀ s <| by
    have h1 := congrArg (toEllipticCurveGeomIso W).inv hs
    rwa [← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← Scheme.Hom.comp_apply, projModelZero_toEllipticCurveGeomIso_inv] at h1

private theorem globalChart_modelPoint {P : Spec (.of R) ⟶ W.toEllipticCurveGeom.carrier}
    (hP : P ≫ W.toEllipticCurveGeom.structureMap = 𝟙 _) :
    (globalChart W).modelPoint hP = P ≫ (toEllipticCurveGeomIso W).hom := by
  apply (globalChart W).isPullback_modelIso_inv_toTotal.hom_ext
  · rw [PointedWeierstrassChart.modelPoint_modelIso_inv_toTotal]
    simp [globalChart]
  · rw [PointedWeierstrassChart.modelPoint_projModelOver, Category.assoc,
      toEllipticCurveGeomIso_hom_projModelOver, hP]

/-- On `W.toEllipticCurveGeom`, `adaptedXCoord` agrees with `W.projModelAdaptedXCoord` read through
`Scheme.ΓSpecIso`. -/
theorem adaptedXCoord_toEllipticCurveGeom
    {P Q : Spec (.of R) ⟶ W.toEllipticCurveGeom.carrier}
    (hP : P ≫ W.toEllipticCurveGeom.structureMap = 𝟙 _)
    (hQ : Q ≫ W.toEllipticCurveGeom.structureMap = 𝟙 _)
    (hP₀ : ∀ s, P s ≠ W.toEllipticCurveGeom.zero s)
    (hQ₀ : ∀ s, Q s ≠ W.toEllipticCurveGeom.zero s)
    (ω : W.toEllipticCurveGeom.InvariantDifferential) :
    W.toEllipticCurveGeom.adaptedXCoord hP hQ hP₀ hQ₀ ω =
      (Scheme.ΓSpecIso (.of R)).inv
        (W.projModelAdaptedXCoord
          (P := P ≫ (toEllipticCurveGeomIso W).hom) (Q := Q ≫ (toEllipticCurveGeomIso W).hom)
          (by rw [Category.assoc, toEllipticCurveGeomIso_hom_projModelOver, hP])
          (by rw [Category.assoc, toEllipticCurveGeomIso_hom_projModelOver, hQ])
          (W.comp_toEllipticCurveGeomIso_hom_ne_projModelZero hP₀)
          (W.comp_toEllipticCurveGeomIso_hom_ne_projModelZero hQ₀)
          (Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R)))
            (g := (toEllipticCurveGeomIso W).inv) W.toEllipticCurveGeom.zero_comp
            W.projModelZero_projModelOver
            (IsPullback.of_horiz_isIso
              ⟨by rw [toEllipticCurveGeomIso_inv_structureMap, Category.comp_id]⟩)
            (by rw [projModelZero_toEllipticCurveGeomIso_inv, Category.id_comp]) ω)) := by
  have h := W.toEllipticCurveGeom.baseMap_appTop_adaptedXCoord hP hQ hP₀ hQ₀ ω (globalChart W)
  have hω_c : (globalChart W).modelDifferential ω =
      Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R)))
        (g := (toEllipticCurveGeomIso W).inv) W.toEllipticCurveGeom.zero_comp
        W.projModelZero_projModelOver
        (IsPullback.of_horiz_isIso
          ⟨by rw [toEllipticCurveGeomIso_inv_structureMap, Category.comp_id]⟩)
        (by rw [projModelZero_toEllipticCurveGeomIso_inv, Category.id_comp]) ω :=
    Scheme.Hom.conormalBasisPullback_congr W.toEllipticCurveGeom.zero_comp
      W.projModelZero_projModelOver (Category.id_comp _) (Category.comp_id _) _ _ _ _ ω
  obtain ⟨x₁, y₁, h₁, hx₁⟩ := W.exists_eq_projModelAffinePoint
    (by rw [Category.assoc, toEllipticCurveGeomIso_hom_projModelOver, hP])
    (W.comp_toEllipticCurveGeomIso_hom_ne_projModelZero hP₀)
  obtain ⟨x₂, y₂, h₂, hx₂⟩ := W.exists_eq_projModelAffinePoint
    (by rw [Category.assoc, toEllipticCurveGeomIso_hom_projModelOver, hQ])
    (W.comp_toEllipticCurveGeomIso_hom_ne_projModelZero hQ₀)
  have hcoord : W.projModelAdaptedXCoord
      ((globalChart W).modelPoint_projModelOver hP)
      ((globalChart W).modelPoint_projModelOver hQ)
      ((globalChart W).modelPoint_apply_ne hP hP₀)
      ((globalChart W).modelPoint_apply_ne hQ hQ₀)
      ((globalChart W).modelDifferential ω) =
      W.projModelAdaptedXCoord
        (by rw [Category.assoc, toEllipticCurveGeomIso_hom_projModelOver, hP])
        (by rw [Category.assoc, toEllipticCurveGeomIso_hom_projModelOver, hQ])
        (W.comp_toEllipticCurveGeomIso_hom_ne_projModelZero hP₀)
        (W.comp_toEllipticCurveGeomIso_hom_ne_projModelZero hQ₀)
        (Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R)))
          (g := (toEllipticCurveGeomIso W).inv) W.toEllipticCurveGeom.zero_comp
          W.projModelZero_projModelOver
          (IsPullback.of_horiz_isIso
            ⟨by rw [toEllipticCurveGeomIso_inv_structureMap, Category.comp_id]⟩)
          (by rw [projModelZero_toEllipticCurveGeomIso_inv, Category.id_comp]) ω) := by
    rw [W.projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint _ _ _ _ _ h₁ h₂
        ((W.globalChart_modelPoint hP).trans hx₁) ((W.globalChart_modelPoint hQ).trans hx₂),
      W.projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint _ _ _ _ _ h₁ h₂ hx₁ hx₂, hω_c]
  simpa only [Scheme.Hom.id_appTop, Iso.refl_hom, CommRingCat.id_apply, hcoord] using h

end WeierstrassCurve
