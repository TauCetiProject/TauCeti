/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
public import TauCeti.RingTheory.FormalGroup.Hom.Basic
public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.RingTheory.FormalGroup.Point.Order
import TauCeti.RingTheory.MvPowerSeries.Rename
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Formal-group homomorphisms induced by isogenies and morphisms of elliptic curves

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`, and let `φ.formalSeries` be
the Laurent expansion at infinity of `φ*(-x₂ / y₂)` in the parameter `z₁ = -x₁ / y₁`. This file
establishes the functor from elliptic-curve morphisms to formal-group homomorphisms:

* **Homomorphism law (`subst_formalGroup_formalSeries`, `formalGroupHom`)**: `φ.formalSeries` is a
  homomorphism of formal group laws from `formalGroup W₁` to `formalGroup W₂`:
  `φ.formalSeries(F₁(X, Y)) = F₂(φ.formalSeries(X), φ.formalSeries(Y))`.
* **Group-law compatibility (`Hom.formalSeries_add`, `Hom.formalSeriesPointHom`)**: extending
  `formalSeries` to `Hom W₁.toAffine W₂.toAffine` by `0 ↦ 0` gives an injective additive group
  homomorphism into `(formalGroup W₂).Point Unit`, so
  `(f + g).formalSeries = F₂(f.formalSeries, g.formalSeries)` and
  `(n • f).formalSeries = [n]_{Ê₂}(f.formalSeries)` for all `n : ℤ`.
* **Multiplication by `n` (`formalSeries_mulByIntIsogeny`,
  `formalSeries_mulByIntIsogenyOfNeZero`)**: for every `n : ℤ` with `ψ_n ≠ 0`, the formal series of
  `[n] : W → W` is `(formalGroup W).zsmulSeries n`.

Both the homomorphism law and additivity are proved by comparing rational-point arithmetic on `W`
base-changed to `KK = FractionRing (MvPowerSeries ι K)` with the chord parametrization `θ` of
`FormalGroup/Add/Assoc.lean`. A nonzero multivariate series `q` with zero constant term determines
both a `K`-algebra embedding `evalFracAlgHom W hq hq0 : K(W) →ₐ[K] KK` and the point
`mapThetaPoint W hq hq0` of `W(KK)`, which is the image of `genericPoint W` under
`evalFracAlgHom`. Functoriality of `Hom.pointMap` along field homomorphisms
(`Hom.pointMap_map_algebraMap_map_genericPoint`) then translates curve-point addition on `W(KK)`
into `formalAdd` identities via `thetaPoint_add_of_ne` and `thetaPoint_inj`.

## Main definitions

* `TauCeti.Isogeny.formalGroupHom`: an isogeny `φ : W₁ → W₂` bundled as a
  `FormalGroupHom (formalGroup W₁) (formalGroup W₂)`.
* `TauCeti.Isogeny.Hom.formalSeries`: the formal series of `f : Hom W₁ W₂` (`0` at `f = 0`).
* `TauCeti.Isogeny.Hom.formalSeriesPointHom`: `Hom.formalSeries` as an additive homomorphism
  `Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit`.
* `TauCeti.Isogeny.Hom.formalGroupHom`: a morphism `f : Hom W₁ W₂` as a
  `FormalGroupHom (formalGroup W₁) (formalGroup W₂)`.

## Main results

* `TauCeti.Isogeny.subst_formalGroup_formalSeries`: `φ.formalSeries` satisfies
  `φ(F₁(X, Y)) = F₂(φ(X), φ(Y))`.
* `TauCeti.Isogeny.Hom.formalSeries_add`:
  `(f + g).formalSeries = F₂(f.formalSeries, g.formalSeries)` for all morphisms `f, g : Hom W₁ W₂`.
* `TauCeti.Isogeny.Hom.formalSeries_zsmul`: `(n • f).formalSeries = [n]_{Ê₂}(f.formalSeries)` for
  all `n : ℤ` and morphisms `f : Hom W₁ W₂`.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny`,
  `TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`: `[n].formalSeries = [n]_Ê`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4, IV.1–IV.2, IV.4, and
  IV.7.
-/

public section

open WeierstrassCurve HahnSeries MvPowerSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.Isogeny

/-! ### Evaluating function fields and generic points at multivariate series -/

section ThetaBridge

variable {K : Type*} [Field K]

/-- Evaluating rational functions on `W` at a nonzero multivariate parameter `q` with zero constant
term, via Laurent expansion at infinity followed by `LaurentSeries.substMvAlgHom`. -/
private noncomputable def evalFracAlgHom (W : WeierstrassCurve K) {ι : Type*}
    {q : MvPowerSeries ι K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    W.toAffine.FunctionField →ₐ[K] FractionRing (MvPowerSeries ι K) :=
  (LaurentSeries.substMvAlgHom (L := FractionRing (MvPowerSeries ι K)) hq hq0).comp
    W.functionFieldLaurentExpansion

private theorem evalFracAlgHom_comp_fieldPullback {W₁ W₂ : WeierstrassCurve K}
    (φ : Isogeny W₁.toAffine W₂.toAffine) {ι : Type*} {q : MvPowerSeries ι K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (evalFracAlgHom W₁ hq hq0).comp φ.fieldPullback =
      evalFracAlgHom W₂
        (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)
        ((PowerSeries.subst_mvPowerSeries_eq_zero_iff hq hq0).not.mpr φ.formalSeries_ne_zero) := by
  apply AlgHom.ext
  intro f
  simp only [evalFracAlgHom, AlgHom.comp_apply, φ.functionFieldLaurentExpansion_fieldPullback,
    LaurentSeries.substMvAlgHom_comp_substAlgHom_apply]

/-- The chord-parametrized point `θ(q)` transported to
`(W.toAffine.map (algebraMap K (FractionRing (MvPowerSeries ι K)))).Point`. -/
private noncomputable def mapThetaPoint (W : WeierstrassCurve K) [W.IsElliptic] {ι : Type*}
    [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {q : MvPowerSeries ι K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (W.toAffine.map (algebraMap K (FractionRing (MvPowerSeries ι K)))).Point :=
  AddEquiv.cast (M := fun V : WeierstrassCurve _ ↦ V.toAffine.Point)
    (W.fracCurve_eq_map ι (FractionRing (MvPowerSeries ι K)))
    (W.thetaPoint (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero) hq hq0)

private theorem mapThetaPoint_inj (W : WeierstrassCurve K) [W.IsElliptic] {ι : Type*}
    [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {q₁ q₂ : MvPowerSeries ι K} (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (h : mapThetaPoint W h₁ hq₁0 = mapThetaPoint W h₂ hq₂0) : q₁ = q₂ := by
  have := MvPowerSeries.isDomain_of_isDomain (σ := ι) (R := K)
  exact (W.thetaPoint_inj (KK := FractionRing (MvPowerSeries ι K))
    (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero) h₁ h₂ hq₁0 hq₂0).mp
    ((AddEquiv.cast (M := fun V : WeierstrassCurve _ ↦ V.toAffine.Point)
      (W.fracCurve_eq_map ι (FractionRing (MvPowerSeries ι K)))).injective h)

private theorem mapThetaPoint_congr (W : WeierstrassCurve K) [W.IsElliptic] {ι : Type*}
    [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {q₁ q₂ : MvPowerSeries ι K} (heq : q₁ = q₂)
    (h₁ : constantCoeff q₁ = 0) (hq₁0 : q₁ ≠ 0)
    (h₂ : constantCoeff q₂ = 0) (hq₂0 : q₂ ≠ 0) :
    mapThetaPoint W h₁ hq₁0 = mapThetaPoint W h₂ hq₂0 := by
  subst heq
  rfl

private theorem subst_pairSubstitution_formalAdd_eq {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) {ι : Type*} {q₁ q₂ : MvPowerSeries ι R}
    (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    MvPowerSeries.subst (pairSubstitution q₁ q₂) (formalAdd W) =
      MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries := by
  have hs : MvPowerSeries.HasSubst ![q₁, q₂] :=
    MvPowerSeries.hasSubst_finTwo (.of_constantCoeff_zero h₁) (.of_constantCoeff_zero h₂)
  rw [formalGroup_toPowerSeries, MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _ hs]
  congr 1
  funext s
  rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [pairSubstitution]

private theorem constantCoeff_subst_formalGroup {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) {ι : Type*} {q₁ q₂ : MvPowerSeries ι R}
    (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    constantCoeff (MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries) = 0 :=
  (formalGroup W).constantCoeff_val_add
    (x := ⟨q₁, .of_constantCoeff_zero h₁⟩) (y := ⟨q₂, .of_constantCoeff_zero h₂⟩) h₁ h₂

private theorem subst_formalGroup_ne_zero {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) {ι : Type*} {q₁ q₂ : MvPowerSeries ι R}
    (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hne : q₁ ≠ PowerSeries.subst q₂ W.formalInverse) :
    MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries ≠ 0 := fun h0 ↦
  hne <| by
    rw [← W.formalGroup_addInvX]
    exact ((formalGroup W).eq_subst_addInvX_iff_subst_left_eq_zero
      (.of_constantCoeff_zero h₂) (.of_constantCoeff_zero h₁)).mpr h0

private theorem mapThetaPoint_add_of_ne (W : WeierstrassCurve K) [W.IsElliptic] {ι : Type*}
    [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {q₁ q₂ : MvPowerSeries ι K} (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hne₁ : q₁ ≠ q₂) (hne₂ : q₁ ≠ PowerSeries.subst q₂ W.formalInverse)
    (hFc : constantCoeff (MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries) = 0)
    (hF0 : MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries ≠ 0) :
    mapThetaPoint W h₁ hq₁0 + mapThetaPoint W h₂ hq₂0 = mapThetaPoint W hFc hF0 := by
  have := MvPowerSeries.isDomain_of_isDomain (σ := ι) (R := K)
  have hFeq := subst_pairSubstitution_formalAdd_eq W h₁ h₂
  have hFc' : constantCoeff
      (MvPowerSeries.subst (pairSubstitution q₁ q₂) (formalAdd W)) = 0 := hFeq ▸ hFc
  have hF0' : MvPowerSeries.subst (pairSubstitution q₁ q₂) (formalAdd W) ≠ 0 := hFeq ▸ hF0
  simp only [mapThetaPoint, ← map_add]
  rw [W.thetaPoint_add_of_ne (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero)
    h₁ h₂ hq₁0 hq₂0 hne₁ hne₂ hFc' hF0',
    (W.thetaPoint_inj (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero) hFc' hFc hF0' hF0).mpr hFeq]

private theorem mapThetaPoint_add_of_subst_separates (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {g : ι → MvPowerSeries Unit K} (hg : MvPowerSeries.HasSubst g)
    {q₁ q₂ : MvPowerSeries ι K} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hg₁ : MvPowerSeries.subst g q₁ = PowerSeries.X) (hg₂ : MvPowerSeries.subst g q₂ = 0)
    (hFc : constantCoeff (MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries) = 0)
    (hF0 : MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries ≠ 0) :
    mapThetaPoint W h₁ hq₁0 + mapThetaPoint W h₂ hq₂0 = mapThetaPoint W hFc hF0 := by
  have := MvPowerSeries.isDomain_of_isDomain (σ := ι) (R := K)
  have hFeq := subst_pairSubstitution_formalAdd_eq W h₁ h₂
  have hFc' : constantCoeff
      (MvPowerSeries.subst (pairSubstitution q₁ q₂) (formalAdd W)) = 0 := hFeq ▸ hFc
  have hF0' : MvPowerSeries.subst (pairSubstitution q₁ q₂) (formalAdd W) ≠ 0 := hFeq ▸ hF0
  simp only [mapThetaPoint, ← map_add]
  rw [W.thetaPoint_add_of_subst_separates (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero)
    hg h₁ h₂ hq₁0 hq₂0 hg₁ hg₂ hFc' hF0',
    (W.thetaPoint_inj (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero) hFc' hFc hF0' hF0).mpr hFeq]

private theorem evalFracAlgHom_genericX_and_genericY (W : WeierstrassCurve K) {ι : Type*}
    {q : MvPowerSeries ι K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    let ρ := algebraMap (MvPowerSeries ι K) (FractionRing (MvPowerSeries ι K))
    evalFracAlgHom W hq hq0 W.toAffine.genericX = ρ q / ρ (PowerSeries.subst q (formalW W)) ∧
      evalFracAlgHom W hq hq0 W.toAffine.genericY = -1 / ρ (PowerSeries.subst q (formalW W)) := by
  have := MvPowerSeries.isDomain_of_isDomain (σ := ι) (R := K)
  let KK := FractionRing (MvPowerSeries ι K)
  let ρ := algebraMap (MvPowerSeries ι K) KK
  let σ := evalFracAlgHom W hq hq0
  have hw0 : ρ (PowerSeries.subst q (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero (KK := KK) hq hq0
  have hinvY : σ (-W.toAffine.genericY⁻¹) = ρ (PowerSeries.subst q (formalW W)) := by
    dsimp only [σ, evalFracAlgHom, ρ, KK]
    rw [AlgHom.comp_apply, functionFieldLaurentExpansion_neg_inv_genericY,
      LaurentSeries.substMvAlgHom_coe]
  have hY : σ W.toAffine.genericY = -1 / ρ (PowerSeries.subst q (formalW W)) := by
    rw [map_neg, map_inv₀] at hinvY
    rw [← inv_inv (σ W.toAffine.genericY), neg_eq_iff_eq_neg.mp hinvY, inv_neg]
    ring
  have hparam : σ (-W.toAffine.genericX / W.toAffine.genericY) = ρ q := by
    dsimp only [σ, evalFracAlgHom, ρ, KK]
    rw [AlgHom.comp_apply, functionFieldLaurentExpansion_neg_genericX_div_genericY,
      LaurentSeries.substMvAlgHom_coe, PowerSeries.subst_X (.of_constantCoeff_zero hq)]
  refine ⟨?_, hY⟩
  have hY0 : σ W.toAffine.genericY ≠ 0 := hY ▸ div_ne_zero (by norm_num) hw0
  have hmul : -σ W.toAffine.genericX = ρ q * (-1 / ρ (PowerSeries.subst q (formalW W))) := by
    rw [← hY, ← hparam, map_div₀, map_neg, div_mul_cancel₀ _ hY0]
  linear_combination -hmul

/-- **Specializing `genericPoint W` along `evalFracAlgHom W hq hq0` gives
`mapThetaPoint W hq hq0`.** -/
private theorem map_evalFracAlgHom_genericPoint (W : WeierstrassCurve K) [W.IsElliptic] {ι : Type*}
    [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {q : MvPowerSeries ι K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    Affine.Point.map (evalFracAlgHom W hq hq0) (Affine.genericPoint W.toAffine) =
      mapThetaPoint W hq hq0 := by
  have := MvPowerSeries.isDomain_of_isDomain (σ := ι) (R := K)
  let KK := FractionRing (MvPowerSeries ι K)
  let ρ := algebraMap (MvPowerSeries ι K) KK
  obtain ⟨hX, hY⟩ := evalFracAlgHom_genericX_and_genericY W hq hq0
  have hns₀ :=
    (W.toAffine.baseChange_nonsingular (evalFracAlgHom W hq hq0).injective ..).mpr
      (Affine.nonsingular_genericX_genericY W.toAffine)
  have hLHS : Affine.Point.map (evalFracAlgHom W hq hq0) (Affine.genericPoint W.toAffine) =
      Affine.Point.some _ _ hns₀ := by
    rw [Affine.genericPoint_eq_some, Affine.Point.map_some]
  have hns₁ : (W.map (algebraMap K KK)).toAffine.Nonsingular
      (ρ q / ρ (PowerSeries.subst q (formalW W)))
      (-1 / ρ (PowerSeries.subst q (formalW W))) := by
    -- `(W.baseChange KK)` and `W.map (algebraMap K KK)` agree on unfolding `baseChange`.
    change (W.baseChange KK).toAffine.Nonsingular _ _
    rwa [← hX, ← hY]
  have hns : (fracCurve W ι KK).toAffine.Nonsingular
      (ρ q / ρ (PowerSeries.subst q (formalW W)))
      (-1 / ρ (PowerSeries.subst q (formalW W))) :=
    (W.fracCurve_eq_map ι KK).symm ▸ hns₁
  have hRHS : mapThetaPoint W hq hq0 =
      Affine.Point.some _ _ (W.fracCurve_eq_map ι KK ▸ hns) := by
    rw [mapThetaPoint,
      W.thetaPoint_eq_some (KK := KK) (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero) hq hq0 hns,
      AddEquiv.cast_apply, Affine.Point.cast_some (W.fracCurve_eq_map ι KK)]
  rw [hLHS, hRHS]
  -- `W.toAffine⁄KK` and `W.toAffine.map (algebraMap K KK)` agree on unfolding `baseChange`.
  change Affine.Point.some (W' := W.toAffine.map (algebraMap K (FractionRing (MvPowerSeries ι K))))
      _ _ _ =
    Affine.Point.some (W' := W.toAffine.map (algebraMap K (FractionRing (MvPowerSeries ι K))))
      _ _ _
  simp only [hX, hY, ρ, KK]

/-- **Base-changed isogenies act on `mapThetaPoint` by substituting into their formal series.** -/
private theorem pointMap_ofIsogeny_mapThetaPoint {W₁ W₂ : WeierstrassCurve K}
    [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {ι : Type*}
    [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {q : MvPowerSeries ι K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    ((Hom.ofIsogeny φ).map (algebraMap K (FractionRing (MvPowerSeries ι K)))).pointMap
        (mapThetaPoint W₁ hq hq0) =
      mapThetaPoint W₂
        (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)
        ((PowerSeries.subst_mvPowerSeries_eq_zero_iff hq hq0).not.mpr φ.formalSeries_ne_zero) := by
  have h₁ := Hom.pointMap_map_algebraMap_map_genericPoint
    (Hom.ofIsogeny φ) (evalFracAlgHom W₁ hq hq0)
  have h₂ := map_evalFracAlgHom_genericPoint W₁ hq hq0
  have h₃ := map_evalFracAlgHom_genericPoint W₂
    (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)
    ((PowerSeries.subst_mvPowerSeries_eq_zero_iff hq hq0).not.mpr φ.formalSeries_ne_zero)
  rw [Hom.tautologicalPoint_ofIsogeny, Isogeny.tautologicalPoint_eq_map_genericPoint,
    Affine.Point.map_map, evalFracAlgHom_comp_fieldPullback φ hq hq0] at h₁
  exact (congrArg ((Hom.ofIsogeny φ).map
    (algebraMap K (FractionRing (MvPowerSeries ι K)))).pointMap h₂.symm).trans (h₁.trans h₃)

end ThetaBridge

/-! ### Isogenies induce formal-group homomorphisms -/

section FormalGroupHom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K}

/-- Chord addition of `θ(φ(X₀))` and `θ(φ(X₁))` on `W₂`. -/
private theorem mapThetaPoint_add_formalSeries_coords [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    [DecidableEq (FractionRing (MvPowerSeries (Fin 2) K))] :
    let u : Fin 2 → MvPowerSeries (Fin 2) K := fun i ↦ PowerSeries.subst (X i) φ.formalSeries
    have huc : ∀ i, constantCoeff (u i) = 0 := fun i ↦
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ φ.constantCoeff_formalSeries
    have hune : ∀ i, u i ≠ 0 := fun i ↦
      (PowerSeries.subst_mvPowerSeries_eq_zero_iff (constantCoeff_X i)
        (nonZeroDivisors.ne_zero X_mem_nonZeroDivisors)).not.mpr φ.formalSeries_ne_zero
    ∃ (hF₂c : constantCoeff (MvPowerSeries.subst ![u 0, u 1] (formalGroup W₂).toPowerSeries) = 0)
      (hF₂ne : MvPowerSeries.subst ![u 0, u 1] (formalGroup W₂).toPowerSeries ≠ 0),
      mapThetaPoint W₂ (huc 0) (hune 0) + mapThetaPoint W₂ (huc 1) (hune 1) =
        mapThetaPoint W₂ hF₂c hF₂ne := by
  intro u huc hune
  let g : Fin 2 → PowerSeries K := ![PowerSeries.X, 0]
  have hg : MvPowerSeries.HasSubst g := MvPowerSeries.HasSubst.X_zero (i := ())
  have hgu0 : MvPowerSeries.subst g (u 0) = φ.formalSeries := by
    rw [MvPowerSeries.subst_powerSeriesSubst hg (.of_constantCoeff_zero (constantCoeff_X 0)),
      subst_X hg]
    dsimp only [g]
    rw [Matrix.cons_val_zero, PowerSeries.X_subst]
  have hgu1 : MvPowerSeries.subst g (u 1) = 0 := by
    rw [MvPowerSeries.subst_powerSeriesSubst hg (.of_constantCoeff_zero (constantCoeff_X 1)),
      subst_X hg]
    dsimp only [g]
    rw [Matrix.cons_val_one, Matrix.cons_val_zero,
      PowerSeries.subst_zero_of_constantCoeff_zero φ.constantCoeff_formalSeries]
  have hu_ne₁ : u 0 ≠ u 1 := fun h ↦ φ.formalSeries_ne_zero (by rw [← hgu0, h, hgu1])
  have hu_ne₂ : u 0 ≠ PowerSeries.subst (u 1) W₂.formalInverse := fun h ↦
    φ.formalSeries_ne_zero <| by
      rw [← hgu0, h, PowerSeries.subst_def, W₂.subst_subst_formalInverse_eq_zero hg (huc 1) hgu1]
  have hF₂c := constantCoeff_subst_formalGroup W₂ (huc 0) (huc 1)
  have hF₂ne := subst_formalGroup_ne_zero W₂ (huc 0) (huc 1) hu_ne₂
  exact ⟨hF₂c, hF₂ne, mapThetaPoint_add_of_ne W₂ (huc 0) (huc 1) (hune 0) (hune 1)
    hu_ne₁ hu_ne₂ hF₂c hF₂ne⟩

/-- **The formal series of an isogeny `φ : W₁ → W₂` of elliptic curves is a homomorphism of formal
group laws** from `formalGroup W₁` to `formalGroup W₂`:
`φ.formalSeries(F₁(X, Y)) = F₂(φ.formalSeries(X), φ.formalSeries(Y))`. -/
theorem subst_formalGroup_formalSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    PowerSeries.subst (formalGroup W₁).toPowerSeries φ.formalSeries =
      MvPowerSeries.subst (fun i ↦ φ.formalSeries.toMvPowerSeries i)
        (formalGroup W₂).toPowerSeries := by
  classical
  have := φ.isElliptic
  let KK := FractionRing (MvPowerSeries (Fin 2) K)
  have h0c : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 0
  have h1c : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 1
  have h0ne : (X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have h1ne : (X 1 : MvPowerSeries (Fin 2) K) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  let g : Fin 2 → PowerSeries K := ![PowerSeries.X, 0]
  have hg : MvPowerSeries.HasSubst g := MvPowerSeries.HasSubst.X_zero (i := ())
  have hg0 : MvPowerSeries.subst g (X 0 : MvPowerSeries (Fin 2) K) = PowerSeries.X := by
    rw [subst_X hg]
    dsimp only [g]
    rw [Matrix.cons_val_zero]
  have hg1 : MvPowerSeries.subst g (X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    rw [subst_X hg]
    dsimp only [g]
    rw [Matrix.cons_val_one, Matrix.cons_val_zero]
  have hF₁eq : MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1]
      (formalGroup W₁).toPowerSeries = (formalGroup W₁).toPowerSeries := by
    rw [MvPowerSeries.finTwo_X_eq_X, MvPowerSeries.subst_self, id_eq]
  have hF₁c := constantCoeff_subst_formalGroup W₁ h0c h1c
  have hF₁ne : MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1]
      (formalGroup W₁).toPowerSeries ≠ 0 := by
    rw [← subst_pairSubstitution_formalAdd_eq W₁ h0c h1c]
    exact subst_pair_formalAdd_ne_zero W₁ hg h0c h1c hg0 hg1
  have hadd₁ := mapThetaPoint_add_of_subst_separates W₁ hg h0c h1c h0ne h1ne hg0 hg1 hF₁c hF₁ne
  obtain ⟨hF₂c, hF₂ne, hadd₂⟩ := mapThetaPoint_add_formalSeries_coords φ
  have hpt : ((Hom.ofIsogeny φ).map (algebraMap K KK)).pointMap (mapThetaPoint W₁ hF₁c hF₁ne) =
      mapThetaPoint W₂ hF₂c hF₂ne := by
    rw [← hadd₁, Hom.pointMap_add, pointMap_ofIsogeny_mapThetaPoint φ h0c h0ne,
      pointMap_ofIsogeny_mapThetaPoint φ h1c h1ne, hadd₂]
  rw [pointMap_ofIsogeny_mapThetaPoint φ hF₁c hF₁ne] at hpt
  have heq := mapThetaPoint_inj W₂ _ hF₂c _ hF₂ne hpt
  rw [hF₁eq] at heq
  refine heq.trans ?_
  congr 1
  funext i
  fin_cases i <;> simp [PowerSeries.toMvPowerSeries_eq_subst]

/-- **An isogeny `φ : W₁ → W₂` induces a bundled homomorphism of formal group laws**
`formalGroup W₁ → formalGroup W₂`. -/
noncomputable def formalGroupHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := φ.formalSeries
  zero_constantCoeff := φ.constantCoeff_formalSeries
  hom := φ.subst_formalGroup_formalSeries

@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries :=
  (rfl)

/-- **An isogeny of elliptic curves is uniquely determined by its induced formal-group
homomorphism.** -/
theorem formalGroupHom_injective [W₂.IsElliptic] :
    Function.Injective (formalGroupHom (K := K) (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h ↦ formalSeries_injective (congrArg FormalGroupHom.toPowerSeries h)

-- Fire before `formalGroupHom_comp`/`formalGroupHom_id`/etc. expand the inner formal-group hom.
@[simp↓]
theorem formalGroupHom_inj [W₂.IsElliptic] {φ ψ : Isogeny W₁.toAffine W₂.toAffine} :
    φ.formalGroupHom = ψ.formalGroupHom ↔ φ = ψ :=
  formalGroupHom_injective.eq_iff

@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext
  simp

@[simp]
theorem formalGroupHom_comp {W₃ : WeierstrassCurve K} [W₂.IsElliptic] [W₃.IsElliptic]
    (ψ : Isogeny W₂.toAffine W₃.toAffine) (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).formalGroupHom = ψ.formalGroupHom.comp φ.formalGroupHom := by
  ext
  simp

@[simp]
theorem formalGroupHom_negIsogeny (W : WeierstrassCurve K) [W.IsElliptic] :
    (negIsogeny W.toAffine).formalGroupHom = (formalGroup W).zsmulHom (-1) := by
  ext
  simp [FormalGroup.zsmulSeries_neg_one, W.formalGroup_addInvX]

end FormalGroupHom

/-! ### Extending `formalSeries` and `formalGroupHom` to `Hom W₁ W₂` -/

namespace Hom

section Basic

variable {K L : Type*} [Field K] [Field L] {W₁ W₂ W₃ : WeierstrassCurve K}

open scoped Classical in
/-- **The formal power series of a morphism `f : Hom W₁ W₂`**, equal to `0` at `f = 0` and to
`(toIsogeny hf).formalSeries` for `f ≠ 0`. -/
noncomputable def formalSeries (f : Hom W₁.toAffine W₂.toAffine) : K⟦X⟧ :=
  if hf : f = 0 then 0 else (toIsogeny hf).formalSeries

@[simp]
theorem formalSeries_zero : (0 : Hom W₁.toAffine W₂.toAffine).formalSeries = 0 := by
  classical simp [formalSeries]

@[simp]
theorem formalSeries_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalSeries = φ.formalSeries := by
  classical simp [formalSeries]

-- Fire before `formalSeries_add`/`formalSeries_comp`/etc. expand the inner formal series.
@[simp↓]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

theorem hasSubst_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.HasSubst f.formalSeries :=
  .of_constantCoeff_zero' f.constantCoeff_formalSeries

-- Fire before `formalSeries_add`/`formalSeries_comp`/etc. expand the inner formal series.
@[simp↓]
theorem formalSeries_eq_zero_iff (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalSeries = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · simp [φ.formalSeries_ne_zero]

/-- **Morphisms in `Hom W₁ W₂` are uniquely determined by their formal power series**, with no
ellipticity hypothesis on either curve. -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (K := K) (W₁ := W₁) (W₂ := W₂)) := by
  intro f g h
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · exact ((formalSeries_eq_zero_iff g).mp (by simpa using h.symm)).symm
  · rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
    · exact absurd (by simpa using h) φ.formalSeries_ne_zero
    · rw [formalSeries_ofIsogeny, formalSeries_ofIsogeny] at h
      exact congrArg ofIsogeny (Isogeny.formalSeries_injective h)

-- Fire before `formalSeries_add`/`formalSeries_comp`/etc. expand the inner formal series.
@[simp↓]
theorem formalSeries_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = g.formalSeries ↔ f = g :=
  formalSeries_injective.eq_iff

@[simp]
theorem formalSeries_id (W : WeierstrassCurve K) :
    (Hom.id W.toAffine).formalSeries = PowerSeries.X := by
  simp [Hom.id_def]

theorem formalSeries_one (W : WeierstrassCurve K) :
    (1 : Hom W.toAffine W.toAffine).formalSeries = PowerSeries.X := by
  rw [Hom.one_def, formalSeries_id]

@[simp]
theorem formalSeries_comp (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalSeries = PowerSeries.subst f.formalSeries g.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · simp
  · rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
    · simp [PowerSeries.subst_zero_of_constantCoeff_zero ψ.constantCoeff_formalSeries]
    · simp

@[simp]
theorem formalSeries_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalSeries = PowerSeries.subst f.formalSeries W₂.formalInverse := by
  rw [Hom.neg_def, formalSeries_comp, formalSeries_ofIsogeny, formalSeries_negIsogeny]

@[simp]
theorem formalSeries_map (f : Hom W₁.toAffine W₂.toAffine) (σ : K →+* L) :
    (f.map σ).formalSeries = PowerSeries.map σ f.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [zero_map, formalSeries_zero, formalSeries_zero, map_zero]
  · rw [ofIsogeny_map, formalSeries_ofIsogeny (W₁ := W₁.map σ) (W₂ := W₂.map σ),
      formalSeries_ofIsogeny, Isogeny.formalSeries_map]

end Basic

/-! ### Addition, scalar multiplication, and bundled formal-group homomorphisms -/

section Additive

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

/-- Generic additivity: when `φ ≠ ψ` and `φ + ψ ≠ 0`, the formal series of
`ofIsogeny φ + ofIsogeny ψ` is `F₂(φ.formalSeries, ψ.formalSeries)`. -/
private theorem formalSeries_add_ofIsogeny_of_ne (φ ψ : Isogeny W₁.toAffine W₂.toAffine)
    (hfg : ofIsogeny φ + ofIsogeny ψ ≠ 0) (hne : ofIsogeny φ ≠ ofIsogeny ψ) :
    (ofIsogeny φ + ofIsogeny ψ).formalSeries =
      MvPowerSeries.subst ![φ.formalSeries, ψ.formalSeries] (formalGroup W₂).toPowerSeries := by
  classical
  obtain ⟨χ, hχ⟩ := (ofIsogeny φ + ofIsogeny ψ).eq_zero_or_exists_ofIsogeny.resolve_left hfg
  have := φ.isElliptic
  have hne₁ : φ.formalSeries ≠ ψ.formalSeries := fun h ↦
    hne (congrArg ofIsogeny (Isogeny.formalSeries_injective h))
  have hne₂ : φ.formalSeries ≠ PowerSeries.subst ψ.formalSeries W₂.formalInverse := fun h ↦ by
    have hneg : ofIsogeny φ = -ofIsogeny ψ := formalSeries_injective <| by
      rw [formalSeries_ofIsogeny, formalSeries_neg, formalSeries_ofIsogeny, h]
    exact hfg (by rw [hneg, neg_add_cancel])
  have hFc := constantCoeff_subst_formalGroup W₂
    φ.constantCoeff_formalSeries ψ.constantCoeff_formalSeries
  have hF0 := subst_formalGroup_ne_zero W₂
    φ.constantCoeff_formalSeries ψ.constantCoeff_formalSeries hne₂
  let KK := FractionRing (MvPowerSeries Unit K)
  have hXc : constantCoeff (PowerSeries.X : MvPowerSeries Unit K) = 0 := PowerSeries.constantCoeff_X
  have hX0 : (PowerSeries.X : MvPowerSeries Unit K) ≠ 0 := PowerSeries.X_ne_zero
  have hpt : ((ofIsogeny φ + ofIsogeny ψ).map (algebraMap K KK)).pointMap
      (mapThetaPoint W₁ hXc hX0) = mapThetaPoint W₂ hFc hF0 := by
    rw [map_add, Hom.add_pointMap, pointMap_ofIsogeny_mapThetaPoint φ hXc hX0,
      pointMap_ofIsogeny_mapThetaPoint ψ hXc hX0]
    have hφX : PowerSeries.subst (PowerSeries.X : K⟦X⟧) φ.formalSeries = φ.formalSeries :=
      PowerSeries.X_subst _
    have hψX : PowerSeries.subst (PowerSeries.X : K⟦X⟧) ψ.formalSeries = ψ.formalSeries :=
      PowerSeries.X_subst _
    rw [mapThetaPoint_congr W₂ hφX _ _ φ.constantCoeff_formalSeries φ.formalSeries_ne_zero,
      mapThetaPoint_congr W₂ hψX _ _ ψ.constantCoeff_formalSeries ψ.formalSeries_ne_zero]
    exact mapThetaPoint_add_of_ne W₂ φ.constantCoeff_formalSeries ψ.constantCoeff_formalSeries
      φ.formalSeries_ne_zero ψ.formalSeries_ne_zero hne₁ hne₂ hFc hF0
  rw [hχ, pointMap_ofIsogeny_mapThetaPoint χ hXc hX0] at hpt
  have hχeq := mapThetaPoint_inj W₂ _ hFc _ hF0 hpt
  rw [PowerSeries.X_subst] at hχeq
  rw [hχ, formalSeries_ofIsogeny, hχeq]

/-- On an elliptic curve `W`, the formal series of `2 • Hom.id W.toAffine` agrees with the doubling
series `(formalGroup W).nsmulSeries 2`. -/
private theorem formalSeries_two_nsmul_id (W : WeierstrassCurve K) [W.IsElliptic] :
    ((2 : ℕ) • Hom.id W.toAffine).formalSeries = (formalGroup W).nsmulSeries 2 := by
  have h2ne : (2 : ℕ) • Hom.id W.toAffine ≠ 0 := fun h ↦ by
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← zero_zsmul (Hom.id W.toAffine)] at h
    exact (by decide : (2 : ℤ) ≠ 0) (Hom.zsmul_id_injective h)
  have hsum : ofIsogeny (toIsogeny h2ne) + ofIsogeny (negIsogeny W.toAffine) =
      Hom.id W.toAffine := by
    rw [ofIsogeny_toIsogeny, ofIsogeny_negIsogeny, Hom.one_def, two_nsmul, add_neg_cancel_right]
  have hfg : ofIsogeny (toIsogeny h2ne) + ofIsogeny (negIsogeny W.toAffine) ≠ 0 := by
    rw [hsum, Hom.id_def]
    exact ofIsogeny_ne_zero _
  have hne : ofIsogeny (toIsogeny h2ne) ≠ ofIsogeny (negIsogeny W.toAffine) := fun h ↦ by
    rw [ofIsogeny_toIsogeny, ofIsogeny_negIsogeny, Hom.one_def, ← Nat.cast_smul_eq_nsmul ℤ,
      ← neg_one_zsmul] at h
    exact (by decide : (2 : ℤ) ≠ -1) (Hom.zsmul_id_injective h)
  have hadd := formalSeries_add_ofIsogeny_of_ne (toIsogeny h2ne) (negIsogeny W.toAffine) hfg hne
  rw [hsum, formalSeries_id, formalSeries_negIsogeny, ← formalSeries_ofIsogeny (toIsogeny h2ne),
    ofIsogeny_toIsogeny] at hadd
  let p₂ : (formalGroup W).Point Unit :=
    ⟨((2 : ℕ) • Hom.id W.toAffine).formalSeries,
      ((2 : ℕ) • Hom.id W.toAffine).hasSubst_formalSeries⟩
  let pX : (formalGroup W).Point Unit :=
    ⟨PowerSeries.X, .of_constantCoeff_zero' PowerSeries.constantCoeff_X⟩
  have hnegX : (-pX).val = W.formalInverse := by
    rw [FormalGroup.neg_apply, PowerSeries.X_subst, W.formalGroup_addInvX]
  have hp : pX = p₂ + -pX := Subtype.ext (by rw [FormalGroup.add_apply, hnegX]; exact hadd)
  have hp₂ : p₂ = (2 : ℕ) • pX := by
    rw [← sub_eq_add_neg] at hp
    exact (sub_eq_iff_eq_add.mp hp.symm).trans (two_nsmul pX).symm
  have hval := congrArg Subtype.val hp₂
  rw [← (formalGroup W).subst_nsmulSeries pX 2, PowerSeries.X_subst] at hval
  exact hval

/-- **Additivity of formal power series**: the formal power series of a sum of morphisms
`f, g : Hom W₁ W₂` is the formal-group sum of their formal power series:
`(f + g).formalSeries = F₂(f.formalSeries, g.formalSeries)`. -/
@[simp]
theorem formalSeries_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalSeries =
      MvPowerSeries.subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries := by
  classical
  by_cases hf : f = 0
  · subst hf
    rw [zero_add, formalSeries_zero, (formalGroup W₂).zero_add g.hasSubst_formalSeries]
  by_cases hg : g = 0
  · subst hg
    rw [add_zero, formalSeries_zero, (formalGroup W₂).add_zero f.hasSubst_formalSeries]
  by_cases hfg : f + g = 0
  · have hfn : f = -g := eq_neg_of_add_eq_zero_left hfg
    rw [hfg, formalSeries_zero, hfn, formalSeries_neg, ← W₂.formalGroup_addInvX,
      (formalGroup W₂).subst_addInvX_self_eq_zero g.hasSubst_formalSeries]
  by_cases hfeqg : f = g
  · subst hfeqg
    have h2f : f + f = ((2 : ℕ) • Hom.id W₂.toAffine).comp f := by
      rw [two_nsmul, Hom.add_comp, Hom.id_comp]
    let p : (formalGroup W₂).Point Unit := ⟨f.formalSeries, f.hasSubst_formalSeries⟩
    rw [h2f, formalSeries_comp, formalSeries_two_nsmul_id,
      (formalGroup W₂).subst_nsmulSeries p 2, two_nsmul, FormalGroup.add_apply]
  obtain ⟨φ, rfl⟩ := f.eq_zero_or_exists_ofIsogeny.resolve_left hf
  obtain ⟨ψ, rfl⟩ := g.eq_zero_or_exists_ofIsogeny.resolve_left hg
  simpa only [formalSeries_ofIsogeny] using formalSeries_add_ofIsogeny_of_ne φ ψ hfg hfeqg

/-- **The formal series map as an additive homomorphism** from `Hom W₁ W₂` into the group
`(formalGroup W₂).Point Unit` of power-series points of the target formal group. -/
noncomputable def formalSeriesPointHom :
    Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit where
  toFun f := ⟨f.formalSeries, f.hasSubst_formalSeries⟩
  map_zero' := Subtype.ext formalSeries_zero
  map_add' f g := Subtype.ext (formalSeries_add f g)

@[simp]
theorem val_formalSeriesPointHom (f : Hom W₁.toAffine W₂.toAffine) :
    (formalSeriesPointHom f).val = f.formalSeries :=
  (rfl)

theorem formalSeriesPointHom_injective :
    Function.Injective (formalSeriesPointHom (K := K) (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h ↦ formalSeries_injective (congrArg Subtype.val h)

-- Fire before `map_add`/`map_neg`/etc. expand the inner `formalSeriesPointHom`.
@[simp↓]
theorem formalSeriesPointHom_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    formalSeriesPointHom f = formalSeriesPointHom g ↔ f = g :=
  formalSeriesPointHom_injective.eq_iff

@[simp]
theorem formalSeries_sub (f g : Hom W₁.toAffine W₂.toAffine) :
    (f - g).formalSeries =
      MvPowerSeries.subst ![f.formalSeries, PowerSeries.subst g.formalSeries W₂.formalInverse]
        (formalGroup W₂).toPowerSeries := by
  rw [sub_eq_add_neg, formalSeries_add, formalSeries_neg]

@[simp]
theorem formalSeries_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).nsmulSeries n) := by
  have h := congrArg Subtype.val ((formalSeriesPointHom (W₁ := W₁) (W₂ := W₂)).map_nsmul n f)
  rw [val_formalSeriesPointHom, ← (formalGroup W₂).subst_nsmulSeries (formalSeriesPointHom f) n,
    val_formalSeriesPointHom] at h
  exact h

/-- **Integer scalar multiplication of morphisms corresponds to formal-group multiplication**:
`(n • f).formalSeries = [n]_{Ê₂}(f.formalSeries)` for every `n : ℤ` and `f : Hom W₁ W₂`. -/
@[simp]
theorem formalSeries_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).zsmulSeries n) := by
  have h := congrArg Subtype.val ((formalSeriesPointHom (W₁ := W₁) (W₂ := W₂)).map_zsmul n f)
  rw [val_formalSeriesPointHom, ← (formalGroup W₂).subst_zsmulSeries (formalSeriesPointHom f) n,
    val_formalSeriesPointHom] at h
  exact h

open scoped Classical in
/-- **A morphism `f : Hom W₁ W₂` induces a bundled homomorphism of formal group laws**
`formalGroup W₁ → formalGroup W₂` (`0` when `f = 0`). -/
noncomputable def formalGroupHom (f : Hom W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := f.formalSeries
  zero_constantCoeff := f.constantCoeff_formalSeries
  hom := by
    rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
    · rw [formalSeries_zero]
      exact (FormalGroup.homDefect_eq_zero_iff (formalGroup W₁) (formalGroup W₂)).mp
        FormalGroup.homDefect_zero
    · rw [formalSeries_ofIsogeny]
      exact φ.subst_formalGroup_formalSeries

@[simp]
theorem formalGroupHom_toPowerSeries (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalGroupHom.toPowerSeries = f.formalSeries :=
  (rfl)

@[simp]
theorem formalGroupHom_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalGroupHom = φ.formalGroupHom := by
  ext
  simp

@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Hom.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext
  simp

@[simp]
theorem formalGroupHom_comp {W₃ : WeierstrassCurve K} [W₃.IsElliptic]
    (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalGroupHom = g.formalGroupHom.comp f.formalGroupHom := by
  ext
  simp

/-- **Morphisms in `Hom W₁ W₂` are uniquely determined by their induced formal-group
homomorphisms.** -/
theorem formalGroupHom_injective :
    Function.Injective (formalGroupHom (K := K) (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h ↦ formalSeries_injective (congrArg FormalGroupHom.toPowerSeries h)

-- Fire before `formalGroupHom_comp`/`formalGroupHom_ofIsogeny`/etc. expand the inner hom.
@[simp↓]
theorem formalGroupHom_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalGroupHom = g.formalGroupHom ↔ f = g :=
  formalGroupHom_injective.eq_iff

theorem formalGroupHom_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalGroupHom = ((formalGroup W₂).zsmulHom (-1)).comp f.formalGroupHom := by
  ext
  simp [FormalGroup.zsmulSeries_neg_one, W₂.formalGroup_addInvX]

theorem formalGroupHom_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalGroupHom = ((formalGroup W₂).zsmulHom n).comp f.formalGroupHom := by
  ext
  simp

/-- Composition of morphisms corresponds to applying the outer formal-group homomorphism to the
inner formal-series point. -/
theorem formalSeriesPointHom_comp {W₃ : WeierstrassCurve K} [W₃.IsElliptic]
    (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    formalSeriesPointHom (g.comp f) = g.formalGroupHom.applyPoint (formalSeriesPointHom f) := by
  apply Subtype.ext
  rw [val_formalSeriesPointHom, FormalGroupHom.applyPoint_val, val_formalSeriesPointHom,
    formalGroupHom_toPowerSeries, formalSeries_comp]

end Additive

end Hom

/-! ### The formal series of multiplication by `n` -/

section MulByInt

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The formal series of `[n] : W → W` is the integer multiplication series
`(formalGroup W).zsmulSeries n`.** -/
@[simp]
theorem formalSeries_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  rw [← Hom.formalSeries_ofIsogeny, ofIsogeny_mulByIntIsogeny, Hom.formalSeries_zsmul,
    Hom.formalSeries_id, PowerSeries.X_subst]

/-- **The formal series of `mulByIntIsogenyOfNeZero W.toAffine hn` (`n ≠ 0`) is
`(formalGroup W).zsmulSeries n`.** -/
theorem formalSeries_mulByIntIsogenyOfNeZero {n : ℤ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n :=
  formalSeries_mulByIntIsogeny W
    (psiFunctionField_ne_zero_of_Δ_ne_zero W.toAffine W.isUnit_Δ.ne_zero hn)

/-- **For `n : ℕ` with `ψ_n ≠ 0`, the formal series of `[n] : W → W` is
`(formalGroup W).nsmulSeries n`.** -/
theorem formalSeries_mulByIntIsogeny_natCast {n : ℕ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).nsmulSeries n := by
  rw [formalSeries_mulByIntIsogeny, (formalGroup W).zsmulSeries_natCast]

/-- **The formal-group homomorphism induced by `[n] : W → W` is `(formalGroup W).zsmulHom n`.** -/
@[simp]
theorem formalGroupHom_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalGroupHom = (formalGroup W).zsmulHom n := by
  ext
  simp

/-- **The formal-group homomorphism induced by `mulByIntIsogenyOfNeZero W.toAffine hn` (`n ≠ 0`) is
`(formalGroup W).zsmulHom n`.** -/
theorem formalGroupHom_mulByIntIsogenyOfNeZero {n : ℤ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalGroupHom = (formalGroup W).zsmulHom n :=
  formalGroupHom_mulByIntIsogeny W
    (psiFunctionField_ne_zero_of_Δ_ne_zero W.toAffine W.isUnit_Δ.ne_zero hn)

end MulByInt

end TauCeti.Isogeny

end
