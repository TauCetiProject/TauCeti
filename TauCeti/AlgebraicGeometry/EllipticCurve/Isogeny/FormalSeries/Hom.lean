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
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# Formal-group homomorphisms induced by isogenies and morphisms of elliptic curves

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`, and let `φ.formalSeries` be
the Laurent expansion at infinity of `φ*(-x₂ / y₂)` in the parameter `z₁ = -x₁ / y₁`. This file
proves Silverman IV.4.2(a)–(b):

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

Both parts of Silverman IV.4.2 are proved by comparing rational-point arithmetic on `W`
base-changed to `KK = FractionRing (MvPowerSeries ι K)` with the chord parametrization `θ` of
`FormalGroup/Add/Assoc.lean`. A nonzero multivariate series `q` with zero constant term determines
both a `K`-algebra embedding `evalFracAlgHom W hq hq0 : K(W) →ₐ[K] KK` and the point
`mapThetaPoint W hq hq0` of `W(KK)`, which is the image of `genericPoint W` under
`evalFracAlgHom`. Functoriality of `Hom.pointMap` along field homomorphisms
(`Hom.pointMap_map_algebraMap_map_genericPoint`) then translates curve-point addition on `W(KK)`
into `formalAdd` identities via `thetaPoint_add_of_ne` and `thetaPoint_inj`.

Injectivity of `Isogeny.formalSeries`, its value `W.formalInverse` on `negIsogeny`, and its
compatibility with base change along field homomorphisms require no ellipticity hypothesis and are
proved first.

## Main definitions

* `TauCeti.Isogeny.formalGroupHom`: an isogeny `φ : W₁ → W₂` bundled as a
  `FormalGroupHom (formalGroup W₁) (formalGroup W₂)`.
* `TauCeti.Isogeny.Hom.formalSeries`: the formal series of `f : Hom W₁ W₂` (`0` at `f = 0`).
* `TauCeti.Isogeny.Hom.formalSeriesPointHom`: `Hom.formalSeries` as an additive homomorphism
  `Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit`.
* `TauCeti.Isogeny.Hom.formalGroupHom`: a morphism `f : Hom W₁ W₂` as a
  `FormalGroupHom (formalGroup W₁) (formalGroup W₂)`.

## Main results

* `TauCeti.Isogeny.formalSeries_injective`, `TauCeti.Isogeny.formalSeries_negIsogeny`,
  `TauCeti.Isogeny.formalSeries_map`: injectivity, negation, and base change of
  `Isogeny.formalSeries` for arbitrary Weierstrass curves.
* `TauCeti.Isogeny.subst_formalGroup_formalSeries`: Silverman IV.4.2(a).
* `TauCeti.Isogeny.Hom.formalSeries_add`, `TauCeti.Isogeny.Hom.formalSeries_zsmul`:
  Silverman IV.4.2(b).
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny`,
  `TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`: `[n].formalSeries = [n]_Ê`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4.2.
-/

public section

open WeierstrassCurve HahnSeries MvPowerSeries
open scoped LaurentSeries PowerSeries

namespace WeierstrassCurve

variable {K L : Type*} [Field K] [Field L]

/-- **Naturality of Laurent expansion at infinity under ground-field embeddings.** Carrying a
rational function along `σ : K →+* L` commutes with expanding in `z = -x / y`. -/
theorem mapRingHom_functionFieldLaurentExpansion (W : WeierstrassCurve K) (σ : K →+* L)
    (f : W.toAffine.FunctionField) :
    HahnSeries.mapRingHom σ (W.functionFieldLaurentExpansion f) =
      (W.map σ).functionFieldLaurentExpansion (Affine.FunctionField.map W.toAffine σ f) := by
  let A : W.toAffine.FunctionField →+* L⸨X⸩ :=
    (HahnSeries.mapRingHom σ).comp W.functionFieldLaurentExpansion.toRingHom
  let B : W.toAffine.FunctionField →+* L⸨X⸩ :=
    (W.map σ).functionFieldLaurentExpansion.toRingHom.comp (Affine.FunctionField.map W.toAffine σ)
  have hparam : A (-W.toAffine.genericX / W.toAffine.genericY) =
      B (-W.toAffine.genericX / W.toAffine.genericY) := by
    dsimp only [A, B]
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      W.functionFieldLaurentExpansion_neg_genericX_div_genericY, HahnSeries.mapRingHom_apply,
      HahnSeries.map_ofPowerSeries, PowerSeries.map_X, map_div₀, map_neg,
      Affine.FunctionField.map_genericX, Affine.FunctionField.map_genericY,
      (W.map σ).functionFieldLaurentExpansion_neg_genericX_div_genericY]
  have hw : A (-W.toAffine.genericY⁻¹) = B (-W.toAffine.genericY⁻¹) := by
    dsimp only [A, B]
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      W.functionFieldLaurentExpansion_neg_inv_genericY, HahnSeries.mapRingHom_apply,
      HahnSeries.map_ofPowerSeries, ← map_formalW, map_neg, map_inv₀,
      Affine.FunctionField.map_genericY,
      (W.map σ).functionFieldLaurentExpansion_neg_inv_genericY]
  have hY : A W.toAffine.genericY = B W.toAffine.genericY := by
    simpa only [map_neg, map_inv₀, neg_inj, inv_inj] using hw
  have hX : A W.toAffine.genericX = B W.toAffine.genericX := by
    have hy : B W.toAffine.genericY ≠ 0 :=
      (map_ne_zero_iff B B.injective).mpr W.toAffine.genericY_ne_zero
    simpa only [map_div₀, map_neg, hY, div_left_inj₀ hy, neg_inj] using hparam
  have hAB : A = B := Affine.FunctionField.ringHom_ext (fun c ↦ by
    simp only [A, B, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, Affine.FunctionField.map_algebraMap, HahnSeries.algebraMap_apply',
      PowerSeries.algebraMap_eq, HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries,
      PowerSeries.map_C]) hX hY
  exact RingHom.congr_fun hAB f

end WeierstrassCurve

namespace TauCeti.Isogeny

section General

variable {K L : Type*} [Field K] [Field L] {W₁ W₂ : WeierstrassCurve K}

/-- **An isogeny is uniquely determined by its formal power series**, with no ellipticity
hypothesis on either curve: `φ.formalSeries` determines the Laurent substitution action on `K(W₂)`,
and `functionFieldLaurentExpansion` is injective. -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (K := K) (W₁ := W₁) (W₂ := W₂)) := by
  intro φ ψ h
  have hfp (f : W₂.toAffine.FunctionField) : φ.fieldPullback f = ψ.fieldPullback f := by
    apply W₁.functionFieldLaurentExpansion.injective
    -- `injective` exposes `toRingHom`; restate as `AlgHom` application for `rw`.
    change W₁.functionFieldLaurentExpansion (φ.fieldPullback f) =
      W₁.functionFieldLaurentExpansion (ψ.fieldPullback f)
    rw [φ.functionFieldLaurentExpansion_fieldPullback,
      ψ.functionFieldLaurentExpansion_fieldPullback]
    simp only [h]
  refine Isogeny.ext (AlgHom.ext fun r ↦ ?_)
  have hr := hfp (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField r)
  rwa [fieldPullback_algebraMap, fieldPullback_algebraMap] at hr

@[simp]
theorem formalSeries_inj {φ ψ : Isogeny W₁.toAffine W₂.toAffine} :
    φ.formalSeries = ψ.formalSeries ↔ φ = ψ :=
  formalSeries_injective.eq_iff

private theorem fieldPullback_negIsogeny_genericY_eq (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).fieldPullback W.toAffine.genericY =
      -W.toAffine.genericY *
        (1 - algebraMap K W.toAffine.FunctionField W.a₁ *
            (-W.toAffine.genericX / W.toAffine.genericY) -
          algebraMap K W.toAffine.FunctionField W.a₃ * (-W.toAffine.genericY⁻¹)) := by
  let x := W.toAffine.genericX
  let y := W.toAffine.genericY
  have hy0 : y ≠ 0 := W.toAffine.genericY_ne_zero
  rw [fieldPullback_negIsogeny_genericY]
  -- Unfold `negY` on the base-changed curve `W⁄K(W)` to compare its coefficients.
  change -y - (W.map (algebraMap K W.toAffine.FunctionField)).a₁ * x -
    (W.map (algebraMap K W.toAffine.FunctionField)).a₃ = _
  rw [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  have hx : x = (-x / y) * -y := by rw [mul_neg, div_mul_cancel₀ _ hy0, neg_neg]
  have hw : (1 : W.toAffine.FunctionField) = (-y⁻¹) * -y := by
    rw [neg_mul_neg, inv_mul_cancel₀ hy0]
  calc -y - algebraMap K W.toAffine.FunctionField W.a₁ * x -
        algebraMap K W.toAffine.FunctionField W.a₃
      = -y - algebraMap K W.toAffine.FunctionField W.a₁ * ((-x / y) * -y) -
          algebraMap K W.toAffine.FunctionField W.a₃ * ((-y⁻¹) * -y) := by
        nth_rw 1 [hx]
        rw [← hw, mul_one]
    _ = _ := by ring

/-- **The formal series of `negIsogeny` is the geometric formal inverse `W.formalInverse`**, over
every Weierstrass curve and in every characteristic. -/
@[simp]
theorem formalSeries_negIsogeny (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).formalSeries = W.formalInverse := by
  apply (formalSeries_eq_iff _ _).mpr
  let x := W.toAffine.genericX
  let y := W.toAffine.genericY
  let z := -x / y
  let d := 1 - algebraMap K W.toAffine.FunctionField W.a₁ * z -
    algebraMap K W.toAffine.FunctionField W.a₃ * (-y⁻¹)
  have hnegY : (negIsogeny W.toAffine).fieldPullback y = -y * d :=
    fieldPullback_negIsogeny_genericY_eq W
  have hd0 : d ≠ 0 := right_ne_zero_of_mul <| hnegY ▸
    (map_ne_zero_iff _ (negIsogeny W.toAffine).fieldPullback.injective).mpr
      W.toAffine.genericY_ne_zero
  have hrat : (negIsogeny W.toAffine).fieldPullback z * d = -z := by
    -- Unfold `let z := -x / y` on the LHS only, keeping `-z` intact on the RHS.
    change (negIsogeny W.toAffine).fieldPullback (-x / y) * d = -z
    rw [map_div₀, map_neg, fieldPullback_negIsogeny_genericX, hnegY, ← div_div,
      div_mul_cancel₀ _ hd0, div_neg]
  have hexp := congrArg W.functionFieldLaurentExpansion hrat
  have hd_exp : W.functionFieldLaurentExpansion d = ofPowerSeries ℤ K (formalInverseDenom W) := by
    dsimp only [d, z, x, y]
    rw [map_sub, map_sub, map_one, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes,
      functionFieldLaurentExpansion_neg_genericX_div_genericY,
      functionFieldLaurentExpansion_neg_inv_genericY, HahnSeries.algebraMap_apply',
      HahnSeries.algebraMap_apply', formalInverseDenom_def, map_sub, map_sub, map_one, map_mul,
      map_mul]
    simp only [PowerSeries.algebraMap_eq]
  rw [map_mul, map_neg, hd_exp, W.functionFieldLaurentExpansion_neg_genericX_div_genericY,
    ← (negIsogeny W.toAffine).coe_formalSeries] at hexp
  have hu : ofPowerSeries ℤ K (formalInverseDenom W) *
      ofPowerSeries ℤ K (PowerSeries.invOfUnit (formalInverseDenom W) 1) = 1 := by
    rw [← map_mul, mul_invOfUnit_formalInverseDenom, map_one]
  rw [← (negIsogeny W.toAffine).coe_formalSeries, formalInverse_def, map_neg, map_mul]
  linear_combination -(ofPowerSeries ℤ K (PowerSeries.invOfUnit (formalInverseDenom W) 1)) * hexp +
    ofPowerSeries ℤ K (negIsogeny W.toAffine).formalSeries * hu

/-- **Base change of an isogeny maps the coefficients of its formal series.** -/
@[simp]
theorem formalSeries_map (φ : Isogeny W₁.toAffine W₂.toAffine) (σ : K →+* L) :
    (φ.map σ).formalSeries = PowerSeries.map σ φ.formalSeries := by
  apply ((φ.map σ).formalSeries_eq_iff (W₂ := W₂.map σ) _).mpr
  have h := congrArg (HahnSeries.mapRingHom σ) φ.coe_formalSeries
  rw [HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries,
    W₁.mapRingHom_functionFieldLaurentExpansion σ, ← φ.map_fieldPullback_map σ, map_div₀, map_neg,
    Affine.FunctionField.map_genericX, Affine.FunctionField.map_genericY] at h
  exact h

end General

end TauCeti.Isogeny

namespace WeierstrassCurve

/-- **On an elliptic curve over any field, the formal inverse is distinct from `X`** (including in
characteristic `2`, where `a₁` and `a₃` cannot both vanish without making `Δ = 0`). Indeed,
`negIsogeny` has formal series `formalInverse`, `id` has formal series `X`, and `-1 • id ≠ 1 • id`
in `End(W)`. -/
theorem formalInverse_ne_X {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] :
    W.formalInverse ≠ PowerSeries.X := by
  rw [← TauCeti.Isogeny.formalSeries_negIsogeny, ← TauCeti.Isogeny.formalSeries_id W, Ne,
    TauCeti.Isogeny.formalSeries_inj]
  intro h
  have hhom : (-1 : ℤ) • TauCeti.Isogeny.Hom.id W.toAffine =
      (1 : ℤ) • TauCeti.Isogeny.Hom.id W.toAffine := by
    rw [neg_one_zsmul, one_zsmul, ← TauCeti.Isogeny.Hom.one_def,
      ← TauCeti.Isogeny.Hom.ofIsogeny_negIsogeny, h, ← TauCeti.Isogeny.Hom.id_def,
      ← TauCeti.Isogeny.Hom.one_def]
  exact (by decide : (-1 : ℤ) ≠ 1) (TauCeti.Isogeny.Hom.zsmul_id_injective hhom)

end WeierstrassCurve

namespace TauCeti.Isogeny

/-! ### Evaluating function fields and generic points at multivariate series -/

section ThetaBridge

variable {K : Type*} [Field K]

/-- Substituting a nonzero multivariate power series `q` with zero constant term into a nonzero
univariate power series produces a nonzero series. -/
private theorem subst_mvPowerSeries_ne_zero {ι : Type*} {q : MvPowerSeries ι K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) {f : K⟦X⟧} (hf : f ≠ 0) :
    PowerSeries.subst q f ≠ 0 := by
  have := MvPowerSeries.isDomain_of_isDomain (σ := ι) (R := K)
  have ha : PowerSeries.HasSubst q := .of_constantCoeff_zero hq
  have hg : PowerSeries.subst q f.divXPowOrder ≠ 0 := fun h ↦
    (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hf) <| by
      simpa [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hq] using
        congrArg constantCoeff h
  rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f), PowerSeries.subst_mul ha,
    PowerSeries.subst_pow ha, PowerSeries.subst_X ha]
  exact mul_ne_zero (pow_ne_zero _ hq0) hg

private theorem injective_substFrac_coe {ι : Type*} {q : MvPowerSeries ι K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    Function.Injective
      ((IsScalarTower.toAlgHom K (MvPowerSeries ι K) (FractionRing (MvPowerSeries ι K))).comp
        (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hq))) := by
  have := MvPowerSeries.isDomain_of_isDomain (σ := ι) (R := K)
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    map_eq_zero_iff _ (IsFractionRing.injective (MvPowerSeries ι K) _),
    PowerSeries.coe_substAlgHom] at hf
  by_contra hf0
  exact subst_mvPowerSeries_ne_zero hq hq0 hf0 hf

/-- Substituting a nonzero multivariate series `q` (with `constantCoeff q = 0`) into `K⟦X⟧` lifts
to a `K`-algebra homomorphism `K⸨X⸩ →ₐ[K] FractionRing (MvPowerSeries ι K)`. -/
private noncomputable def laurentSubstFracAlgHom {ι : Type*} {q : MvPowerSeries ι K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    K⸨X⸩ →ₐ[K] FractionRing (MvPowerSeries ι K) :=
  IsFractionRing.liftAlgHom (injective_substFrac_coe hq hq0)

private theorem laurentSubstFracAlgHom_coe {ι : Type*} {q : MvPowerSeries ι K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) (f : K⟦X⟧) :
    laurentSubstFracAlgHom hq hq0 (f : K⸨X⸩) =
      algebraMap (MvPowerSeries ι K) (FractionRing (MvPowerSeries ι K))
        (PowerSeries.subst q f) := by
  rw [laurentSubstFracAlgHom, IsFractionRing.coe_liftAlgHom, ← _root_.LaurentSeries.coe_algebraMap,
    IsFractionRing.lift_algebraMap]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', PowerSeries.coe_substAlgHom]

/-- Evaluating rational functions on `W` at a nonzero multivariate parameter `q` with zero constant
term, via Laurent expansion at infinity followed by `laurentSubstFracAlgHom`. -/
private noncomputable def evalFracAlgHom (W : WeierstrassCurve K) {ι : Type*}
    {q : MvPowerSeries ι K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    W.toAffine.FunctionField →ₐ[K] FractionRing (MvPowerSeries ι K) :=
  (laurentSubstFracAlgHom hq hq0).comp W.functionFieldLaurentExpansion

private theorem evalFracAlgHom_comp_fieldPullback {W₁ W₂ : WeierstrassCurve K}
    (φ : Isogeny W₁.toAffine W₂.toAffine) {ι : Type*} {q : MvPowerSeries ι K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (evalFracAlgHom W₁ hq hq0).comp φ.fieldPullback =
      evalFracAlgHom W₂
        (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)
        (subst_mvPowerSeries_ne_zero hq hq0 φ.formalSeries_ne_zero) := by
  have hcomp : (laurentSubstFracAlgHom hq hq0).comp
      (LaurentSeries.substAlgHom φ.constantCoeff_formalSeries φ.formalSeries_ne_zero) =
      laurentSubstFracAlgHom
        (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)
        (subst_mvPowerSeries_ne_zero hq hq0 φ.formalSeries_ne_zero) := by
    refine AlgHom.toRingHom_injective (IsFractionRing.ringHom_ext (A := K⟦X⟧) fun g ↦ ?_)
    simp only [RingHom.coe_coe, AlgHom.comp_apply, _root_.LaurentSeries.coe_algebraMap,
      LaurentSeries.substAlgHom_coe, laurentSubstFracAlgHom_coe,
      PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero' φ.constantCoeff_formalSeries)
        (.of_constantCoeff_zero hq)]
  apply AlgHom.ext
  intro f
  simp only [evalFracAlgHom, AlgHom.comp_apply, φ.functionFieldLaurentExpansion_fieldPullback,
    ← hcomp]

private theorem fracCurve_eq_map (W : WeierstrassCurve K) (ι : Type*) :
    fracCurve W ι (FractionRing (MvPowerSeries ι K)) =
      W.map (algebraMap K (FractionRing (MvPowerSeries ι K))) := by
  rw [fracCurve_def, ← IsScalarTower.algebraMap_eq]

private def pointCastAddEquiv {M : Type*} [Field M] [DecidableEq M] {C₁ C₂ : WeierstrassCurve M}
    (e : C₁ = C₂) : C₁.toAffine.Point ≃+ C₂.toAffine.Point :=
  e ▸ AddEquiv.refl _

private theorem pointCastAddEquiv_some {M : Type*} [Field M] [DecidableEq M]
    {C₁ C₂ : WeierstrassCurve M} (e : C₁ = C₂) {x y : M} (h : C₁.toAffine.Nonsingular x y) :
    pointCastAddEquiv e (Affine.Point.some x y h) = Affine.Point.some x y (e ▸ h) := by
  subst e
  rfl

/-- The chord-parametrized point `θ(q)` transported to
`(W.toAffine.map (algebraMap K (FractionRing (MvPowerSeries ι K)))).Point`. -/
private noncomputable def mapThetaPoint (W : WeierstrassCurve K) [W.IsElliptic] {ι : Type*}
    [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {q : MvPowerSeries ι K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (W.toAffine.map (algebraMap K (FractionRing (MvPowerSeries ι K)))).Point :=
  pointCastAddEquiv (fracCurve_eq_map W ι)
    (W.thetaPoint (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero) hq hq0)

private theorem mapThetaPoint_inj (W : WeierstrassCurve K) [W.IsElliptic] {ι : Type*}
    [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {q₁ q₂ : MvPowerSeries ι K} (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (h : mapThetaPoint W h₁ hq₁0 = mapThetaPoint W h₂ hq₂0) : q₁ = q₂ := by
  have := MvPowerSeries.isDomain_of_isDomain (σ := ι) (R := K)
  exact W.thetaPoint_inj (KK := FractionRing (MvPowerSeries ι K))
    (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero) h₁ h₂ hq₁0 hq₂0
    ((pointCastAddEquiv (fracCurve_eq_map W ι)).injective h)

private theorem mapThetaPoint_neg (W : WeierstrassCurve K) [W.IsElliptic] {ι : Type*}
    [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {q : MvPowerSeries ι K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    mapThetaPoint W
        (PowerSeries.constantCoeff_subst_eq_zero hq _ W.constantCoeff_formalInverse)
        (subst_mvPowerSeries_ne_zero hq hq0
          (by
            rw [← formalSeries_negIsogeny]
            exact (negIsogeny W.toAffine).formalSeries_ne_zero)) =
      -mapThetaPoint W hq hq0 := by
  simp only [mapThetaPoint, ← map_neg]
  congr 1
  exact W.thetaPoint_neg _ hq hq0 _ _

private theorem subst_pairSubstitution_formalAdd_eq {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) {ι : Type*} {q₁ q₂ : MvPowerSeries ι R}
    (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    MvPowerSeries.subst (pairSubstitution q₁ q₂) (formalAdd W) =
      MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries := by
  have hs : MvPowerSeries.HasSubst ![q₁, q₂] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i <;> assumption
  rw [formalGroup_toPowerSeries, MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _ hs]
  congr 1
  funext s
  rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [pairSubstitution]

private theorem thetaPoint_congr (W : WeierstrassCurve K) {ι : Type*}
    (hΔ : (fracCurve W ι (FractionRing (MvPowerSeries ι K))).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries ι K} (heq : q₁ = q₂)
    (h₁ : constantCoeff q₁ = 0) (hq₁0 : q₁ ≠ 0)
    (h₂ : constantCoeff q₂ = 0) (hq₂0 : q₂ ≠ 0) :
    W.thetaPoint hΔ h₁ hq₁0 = W.thetaPoint hΔ h₂ hq₂0 := by
  subst heq
  rfl

private theorem mapThetaPoint_congr (W : WeierstrassCurve K) [W.IsElliptic] {ι : Type*}
    [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {q₁ q₂ : MvPowerSeries ι K} (heq : q₁ = q₂)
    (h₁ : constantCoeff q₁ = 0) (hq₁0 : q₁ ≠ 0)
    (h₂ : constantCoeff q₂ = 0) (hq₂0 : q₂ ≠ 0) :
    mapThetaPoint W h₁ hq₁0 = mapThetaPoint W h₂ hq₂0 := by
  subst heq
  rfl

private theorem mapThetaPoint_add_of_ne (W : WeierstrassCurve K) [W.IsElliptic] {ι : Type*}
    [DecidableEq (FractionRing (MvPowerSeries ι K))]
    {q₁ q₂ : MvPowerSeries ι K} (h₁ : constantCoeff q₁ = 0)
    (h₂ : constantCoeff q₂ = 0) (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hne₁ : q₁ ≠ q₂) (hne₂ : q₁ ≠ PowerSeries.subst q₂ W.formalInverse)
    (hFc : constantCoeff (MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries) = 0)
    (hF0 : MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries ≠ 0) :
    mapThetaPoint W h₁ hq₁0 + mapThetaPoint W h₂ hq₂0 = mapThetaPoint W hFc hF0 := by
  have hFeq := subst_pairSubstitution_formalAdd_eq W h₁ h₂
  have hFc' : constantCoeff
      (MvPowerSeries.subst (pairSubstitution q₁ q₂) (formalAdd W)) = 0 := hFeq ▸ hFc
  have hF0' : MvPowerSeries.subst (pairSubstitution q₁ q₂) (formalAdd W) ≠ 0 := hFeq ▸ hF0
  simp only [mapThetaPoint, ← map_add]
  rw [W.thetaPoint_add_of_ne (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero)
    h₁ h₂ hq₁0 hq₂0 hne₁ hne₂ hFc' hF0',
    thetaPoint_congr W _ hFeq hFc' hF0' hFc hF0]

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
      laurentSubstFracAlgHom_coe]
  have hY : σ W.toAffine.genericY = -1 / ρ (PowerSeries.subst q (formalW W)) := by
    rw [map_neg, map_inv₀] at hinvY
    rw [← inv_inv (σ W.toAffine.genericY), neg_eq_iff_eq_neg.mp hinvY, inv_neg]
    ring
  have hparam : σ (-W.toAffine.genericX / W.toAffine.genericY) = ρ q := by
    dsimp only [σ, evalFracAlgHom, ρ, KK]
    rw [AlgHom.comp_apply, functionFieldLaurentExpansion_neg_genericX_div_genericY,
      laurentSubstFracAlgHom_coe, PowerSeries.subst_X (.of_constantCoeff_zero hq)]
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
    (fracCurve_eq_map W ι).symm ▸ hns₁
  have hRHS : mapThetaPoint W hq hq0 =
      Affine.Point.some _ _ (fracCurve_eq_map W ι ▸ hns) := by
    rw [mapThetaPoint,
      W.thetaPoint_eq_some (KK := KK) (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero) hq hq0 hns,
      pointCastAddEquiv_some]
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
        (subst_mvPowerSeries_ne_zero hq hq0 φ.formalSeries_ne_zero) := by
  have h₁ := Hom.pointMap_map_algebraMap_map_genericPoint
    (Hom.ofIsogeny φ) (evalFracAlgHom W₁ hq hq0)
  have h₂ := map_evalFracAlgHom_genericPoint W₁ hq hq0
  have h₃ := map_evalFracAlgHom_genericPoint W₂
    (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)
    (subst_mvPowerSeries_ne_zero hq hq0 φ.formalSeries_ne_zero)
  rw [Hom.tautologicalPoint_ofIsogeny, Isogeny.tautologicalPoint_eq_map_genericPoint,
    Affine.Point.map_map, evalFracAlgHom_comp_fieldPullback φ hq hq0] at h₁
  exact (congrArg ((Hom.ofIsogeny φ).map
    (algebraMap K (FractionRing (MvPowerSeries ι K)))).pointMap h₂.symm).trans (h₁.trans h₃)

end ThetaBridge

/-! ### Silverman IV.4.2(a): Isogenies induce formal-group homomorphisms -/

section FormalGroupHom

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K}

private theorem mvSubst_zero {ι : Type*} {g : ι → PowerSeries K} (hg : MvPowerSeries.HasSubst g) :
    MvPowerSeries.subst g (0 : MvPowerSeries ι K) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom hg, map_zero]

private theorem subst_formalGroup_X_zero_X_one (W : WeierstrassCurve K) :
    MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1] (formalGroup W).toPowerSeries =
      (formalGroup W).toPowerSeries := by
  have h : (![(X 0 : MvPowerSeries (Fin 2) K), X 1]) = MvPowerSeries.X := by
    ext i
    fin_cases i <;> rfl
  rw [h, MvPowerSeries.subst_self, id_eq]

/-- Helper for Silverman IV.4.2(a): chord addition of `θ(φ(X₀))` and `θ(φ(X₁))` on `W₂`. -/
private theorem mapThetaPoint_add_formalSeries_coords [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    [DecidableEq (FractionRing (MvPowerSeries (Fin 2) K))] :
    let u : Fin 2 → MvPowerSeries (Fin 2) K := fun i ↦ PowerSeries.subst (X i) φ.formalSeries
    have huc : ∀ i, constantCoeff (u i) = 0 := fun i ↦
      PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ φ.constantCoeff_formalSeries
    have hune : ∀ i, u i ≠ 0 := fun i ↦
      subst_mvPowerSeries_ne_zero (constantCoeff_X i)
        (nonZeroDivisors.ne_zero X_mem_nonZeroDivisors) φ.formalSeries_ne_zero
    ∃ (hF₂c : constantCoeff (MvPowerSeries.subst ![u 0, u 1] (formalGroup W₂).toPowerSeries) = 0)
      (hF₂ne : MvPowerSeries.subst ![u 0, u 1] (formalGroup W₂).toPowerSeries ≠ 0),
      mapThetaPoint W₂ (huc 0) (hune 0) + mapThetaPoint W₂ (huc 1) (hune 1) =
        mapThetaPoint W₂ hF₂c hF₂ne := by
  intro u huc hune
  let g : Fin 2 → PowerSeries K := ![PowerSeries.X, 0]
  have hg : MvPowerSeries.HasSubst g := MvPowerSeries.HasSubst.X_zero (i := ())
  have hgu0 : MvPowerSeries.subst g (u 0) = φ.formalSeries := by
    rw [MvPowerSeries.subst_powerSeriesSubst hg (.of_constantCoeff_zero (constantCoeff_X 0)),
      show MvPowerSeries.subst g (X 0) = PowerSeries.X by simp [g, subst_X hg],
      PowerSeries.X_subst]
  have hgu1 : MvPowerSeries.subst g (u 1) = 0 := by
    rw [MvPowerSeries.subst_powerSeriesSubst hg (.of_constantCoeff_zero (constantCoeff_X 1)),
      show MvPowerSeries.subst g (X 1) = 0 by simp [g, subst_X hg],
      PowerSeries.subst_zero_of_constantCoeff_zero φ.constantCoeff_formalSeries]
  have hu_ne₁ : u 0 ≠ u 1 := fun h ↦ φ.formalSeries_ne_zero (by rw [← hgu0, h, hgu1])
  have hu_ne₂ : u 0 ≠ PowerSeries.subst (u 1) W₂.formalInverse := fun h ↦
    φ.formalSeries_ne_zero <| by
      have hi0 : MvPowerSeries.subst g (PowerSeries.subst (u 1) W₂.formalInverse) = 0 := by
        rw [MvPowerSeries.subst_powerSeriesSubst hg (.of_constantCoeff_zero (huc 1)), hgu1,
          PowerSeries.subst_zero_of_constantCoeff_zero W₂.constantCoeff_formalInverse]
      rw [← hgu0, h, hi0]
  have hF₂c : constantCoeff (MvPowerSeries.subst ![u 0, u 1] (formalGroup W₂).toPowerSeries) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i <;> exact huc _)
      (fun i ↦ by fin_cases i <;> exact huc _) (formalGroup W₂).zero_constantCoeff
  have hF₂ne : MvPowerSeries.subst ![u 0, u 1] (formalGroup W₂).toPowerSeries ≠ 0 := fun h0 ↦
    hu_ne₂ <| by
      rw [← W₂.formalGroup_addInvX]
      exact ((formalGroup W₂).eq_subst_addInvX_iff_subst_left_eq_zero
        (.of_constantCoeff_zero (huc 1)) (.of_constantCoeff_zero (huc 0))).mpr h0
  exact ⟨hF₂c, hF₂ne, mapThetaPoint_add_of_ne W₂ (huc 0) (huc 1) (hune 0) (hune 1)
    hu_ne₁ hu_ne₂ hF₂c hF₂ne⟩

/-- **Silverman IV.4.2(a)**: the formal series of an isogeny `φ : W₁ → W₂` of elliptic curves is a
homomorphism of formal group laws from `formalGroup W₁` to `formalGroup W₂`:
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
    simp [g, subst_X hg]
  have hg1 : MvPowerSeries.subst g (X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp [g, subst_X hg]
  have hF₁eq := subst_formalGroup_X_zero_X_one W₁
  have hF₁c : constantCoeff
      (MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1]
        (formalGroup W₁).toPowerSeries) = 0 := by
    rw [hF₁eq]
    exact (formalGroup W₁).zero_constantCoeff
  have hF₁ne : MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1]
      (formalGroup W₁).toPowerSeries ≠ 0 := by
    rw [← subst_pairSubstitution_formalAdd_eq W₁ h0c h1c]
    exact subst_pair_formalAdd_ne_zero W₁ hg h0c h1c hg0 hg1
  have hadd₁ := mapThetaPoint_add_of_ne W₁ h0c h1c h0ne h1ne
    (ne_of_subst_eq_X_of_subst_eq_zero hg0 hg1)
    (ne_of_subst_eq_X_of_subst_eq_zero hg0 (by
      rw [MvPowerSeries.subst_powerSeriesSubst hg (.of_constantCoeff_zero h1c), hg1,
        PowerSeries.subst_zero_of_constantCoeff_zero W₁.constantCoeff_formalInverse]))
    hF₁c hF₁ne
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
`formalGroup W₁ → formalGroup W₂` (Silverman IV.4.2(a)). -/
noncomputable def formalGroupHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := φ.formalSeries
  zero_constantCoeff := φ.constantCoeff_formalSeries
  hom := φ.subst_formalGroup_formalSeries

@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries :=
  (rfl)

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

end FormalGroupHom

/-! ### Extending `formalSeries` to `Hom W₁ W₂` and Silverman IV.4.2(b) -/

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

@[simp]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

theorem hasSubst_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.HasSubst f.formalSeries :=
  .of_constantCoeff_zero' f.constantCoeff_formalSeries

@[simp]
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

@[simp]
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

/-! ### Doubling and addition of morphisms (Silverman IV.4.2(b)) -/

section Additive

variable {K : Type*} [Field K]

/-- Specializations of `p₀ + p₁` and `p₀ - p₁` along `(X, 0)` and `(0, X)` in `Fin 2`. -/
private theorem subst_sum_and_diff_tautological_fin2 (W : WeierstrassCurve K) :
    let p₀ : (formalGroup W).Point (Fin 2) := ⟨X 0, .of_constantCoeff_zero (constantCoeff_X 0)⟩
    let p₁ : (formalGroup W).Point (Fin 2) := ⟨X 1, .of_constantCoeff_zero (constantCoeff_X 1)⟩
    let g₀ : Fin 2 → PowerSeries K := ![PowerSeries.X, 0]
    let g₁ : Fin 2 → PowerSeries K := ![0, PowerSeries.X]
    MvPowerSeries.subst g₀ (p₀ + p₁).val = PowerSeries.X ∧
      MvPowerSeries.subst g₀ (p₀ + -p₁).val = PowerSeries.X ∧
      MvPowerSeries.subst g₁ (p₀ + p₁).val = PowerSeries.X ∧
      MvPowerSeries.subst g₁ (p₀ + -p₁).val = W.formalInverse := by
  intro p₀ p₁ g₀ g₁
  have h0c : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 0
  have h1c : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 1
  have hg₀ : MvPowerSeries.HasSubst g₀ := MvPowerSeries.HasSubst.X_zero (i := ())
  have hg₁ : MvPowerSeries.HasSubst g₁ := MvPowerSeries.HasSubst.zero_X (i := ())
  let qneg := PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) W.formalInverse
  have hqneg_c : constantCoeff qneg = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h1c _ W.constantCoeff_formalInverse
  have hFm_val : (p₀ + -p₁).val =
      MvPowerSeries.subst ![X 0, qneg] (formalGroup W).toPowerSeries := by
    -- Unfold addition and negation in `(formalGroup W).Point (Fin 2)`.
    change MvPowerSeries.subst ![X 0, PowerSeries.subst (X 1) (formalGroup W).addInvX]
      (formalGroup W).toPowerSeries = _
    rw [W.formalGroup_addInvX]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FormalGroup.add_apply, ← subst_pairSubstitution_formalAdd_eq W h0c h1c]
    exact W.subst_subst_pair_formalAdd_eq_X hg₀ h0c h1c
      (by simp [g₀, subst_X hg₀]) (by simp [g₀, subst_X hg₀])
  · rw [hFm_val, ← subst_pairSubstitution_formalAdd_eq W h0c hqneg_c]
    refine W.subst_subst_pair_formalAdd_eq_X hg₀ h0c hqneg_c (by simp [g₀, subst_X hg₀]) ?_
    rw [MvPowerSeries.subst_powerSeriesSubst hg₀ (.of_constantCoeff_zero h1c),
      show MvPowerSeries.subst g₀ (X 1) = 0 by simp [g₀, subst_X hg₀],
      PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalInverse]
  · rw [add_comm p₀ p₁, FormalGroup.add_apply, ← subst_pairSubstitution_formalAdd_eq W h1c h0c]
    exact W.subst_subst_pair_formalAdd_eq_X hg₁ h1c h0c
      (by simp [g₁, subst_X hg₁]) (by simp [g₁, subst_X hg₁])
  · rw [add_comm p₀ (-p₁)]
    -- Unfold addition and negation in `(formalGroup W).Point (Fin 2)`.
    change MvPowerSeries.subst g₁
      (MvPowerSeries.subst ![PowerSeries.subst (X 1) (formalGroup W).addInvX, X 0]
        (formalGroup W).toPowerSeries) = W.formalInverse
    rw [W.formalGroup_addInvX, ← subst_pairSubstitution_formalAdd_eq W hqneg_c h0c]
    have hg₁_qneg : MvPowerSeries.subst g₁ qneg = W.formalInverse := by
      rw [MvPowerSeries.subst_powerSeriesSubst hg₁ (.of_constantCoeff_zero h1c),
        show MvPowerSeries.subst g₁ (X 1) = PowerSeries.X by simp [g₁, subst_X hg₁],
        PowerSeries.X_subst]
    -- Pointwise `funext` reshape to match `pairSubstitution`.
    rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pair hqneg_c h0c) hg₁,
      show (fun s : Unit ⊕ Unit ↦ MvPowerSeries.subst g₁
          (Sum.elim (fun _ ↦ qneg) (fun _ ↦ X 0) s)) =
        pairSubstitution W.formalInverse (0 : PowerSeries K) from
        funext fun s ↦ by
          rcases s with _ | _
          · exact hg₁_qneg
          · simp [g₁, subst_X hg₁],
      subst_pairSubstitution_formalAdd_eq W W.constantCoeff_formalInverse (map_zero _),
      (formalGroup W).add_zero (.of_constantCoeff_zero' W.constantCoeff_formalInverse)]

/-- Non-vanishing and distinctness of `p₀ + p₁`, `p₀ - p₁`, and their formal sum in `Fin 2`. -/
private theorem sum_and_diff_tautological_ne (W : WeierstrassCurve K) [W.IsElliptic] :
    let p₀ : (formalGroup W).Point (Fin 2) := ⟨X 0, .of_constantCoeff_zero (constantCoeff_X 0)⟩
    let p₁ : (formalGroup W).Point (Fin 2) := ⟨X 1, .of_constantCoeff_zero (constantCoeff_X 1)⟩
    constantCoeff (p₀ + p₁).val = 0 ∧ constantCoeff (p₀ + -p₁).val = 0 ∧
      (p₀ + p₁).val ≠ 0 ∧ (p₀ + -p₁).val ≠ 0 ∧
      (p₀ + p₁).val ≠ (p₀ + -p₁).val ∧
      (p₀ + p₁).val ≠ PowerSeries.subst (p₀ + -p₁).val W.formalInverse ∧
      constantCoeff (MvPowerSeries.subst ![(p₀ + p₁).val, (p₀ + -p₁).val]
        (formalGroup W).toPowerSeries) = 0 ∧
      MvPowerSeries.subst ![(p₀ + p₁).val, (p₀ + -p₁).val] (formalGroup W).toPowerSeries ≠ 0 := by
  intro p₀ p₁
  have h0c : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 0
  have h1c : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 1
  have hg₀ : MvPowerSeries.HasSubst (![PowerSeries.X, 0] : Fin 2 → PowerSeries K) :=
    MvPowerSeries.HasSubst.X_zero (i := ())
  obtain ⟨hg₀_Fp, hg₀_Fm, hg₁_Fp, hg₁_Fm⟩ := subst_sum_and_diff_tautological_fin2 W
  have hqneg_c : constantCoeff (PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K)
      W.formalInverse) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h1c _ W.constantCoeff_formalInverse
  have hFp_c : constantCoeff (p₀ + p₁).val = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i <;> assumption)
      (fun i ↦ by fin_cases i <;> assumption) (formalGroup W).zero_constantCoeff
  have hFm_c : constantCoeff (p₀ + -p₁).val = 0 := by
    -- Unfold addition and negation in `(formalGroup W).Point (Fin 2)`.
    change constantCoeff
      (MvPowerSeries.subst ![X 0, PowerSeries.subst (X 1) (formalGroup W).addInvX]
        (formalGroup W).toPowerSeries) = 0
    rw [W.formalGroup_addInvX]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i <;> assumption)
      (fun i ↦ by fin_cases i <;> assumption) (formalGroup W).zero_constantCoeff
  have hFpm_ne₂ : (p₀ + p₁).val ≠ PowerSeries.subst (p₀ + -p₁).val W.formalInverse := fun h ↦
    W.formalInverse_ne_X <| by
      have hi : MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → PowerSeries K)
          (PowerSeries.subst (p₀ + -p₁).val W.formalInverse) = W.formalInverse := by
        rw [MvPowerSeries.subst_powerSeriesSubst hg₀ (.of_constantCoeff_zero hFm_c),
          hg₀_Fm, PowerSeries.X_subst]
      rw [← hi, ← h, hg₀_Fp]
  refine ⟨hFp_c, hFm_c,
    fun h ↦ PowerSeries.X_ne_zero (by rw [← hg₀_Fp, h, mvSubst_zero hg₀]),
    fun h ↦ PowerSeries.X_ne_zero (by rw [← hg₀_Fm, h, mvSubst_zero hg₀]),
    fun h ↦ W.formalInverse_ne_X (by rw [← hg₁_Fm, ← h, hg₁_Fp]),
    hFpm_ne₂,
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i <;> assumption)
      (fun i ↦ by fin_cases i <;> assumption) (formalGroup W).zero_constantCoeff,
    fun h0 ↦ hFpm_ne₂ <| by
      rw [← W.formalGroup_addInvX]
      exact ((formalGroup W).eq_subst_addInvX_iff_subst_left_eq_zero
        (p₀ + -p₁).prop (p₀ + p₁).prop).mpr h0⟩

/-- Chord subtraction `θ(X₀) + (-θ(X₁)) = θ(F(X₀, [-1]_Ê(X₁)))` in `Fin 2`. -/
private theorem mapThetaPoint_add_neg_X_zero_X_one (W : WeierstrassCurve K) [W.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries (Fin 2) K))]
    (h0c : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0)
    (h1c : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0)
    (h0ne : (X 0 : MvPowerSeries (Fin 2) K) ≠ 0)
    (h1ne : (X 1 : MvPowerSeries (Fin 2) K) ≠ 0)
    (hFm_c' : constantCoeff
      (MvPowerSeries.subst
        ![X 0, PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) W.formalInverse]
        (formalGroup W).toPowerSeries) = 0)
    (hFm_ne' : MvPowerSeries.subst
        ![X 0, PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) W.formalInverse]
        (formalGroup W).toPowerSeries ≠ 0) :
    mapThetaPoint W h0c h0ne + -mapThetaPoint W h1c h1ne = mapThetaPoint W hFm_c' hFm_ne' := by
  let g₀ : Fin 2 → PowerSeries K := ![PowerSeries.X, 0]
  have hg₀ : MvPowerSeries.HasSubst g₀ := MvPowerSeries.HasSubst.X_zero (i := ())
  let qneg := PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) W.formalInverse
  have hqneg_c : constantCoeff qneg = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h1c _ W.constantCoeff_formalInverse
  have hqneg_ne : qneg ≠ 0 := subst_mvPowerSeries_ne_zero h1c h1ne <| by
    rw [← formalSeries_negIsogeny]
    exact (negIsogeny W.toAffine).formalSeries_ne_zero
  have hg₀X0 : MvPowerSeries.subst g₀ (X 0 : MvPowerSeries (Fin 2) K) = PowerSeries.X := by
    simp [g₀, subst_X hg₀]
  have hg₀_qneg : MvPowerSeries.subst g₀ qneg = 0 := by
    rw [MvPowerSeries.subst_powerSeriesSubst hg₀ (.of_constantCoeff_zero h1c),
      show MvPowerSeries.subst g₀ (X 1) = 0 by simp [g₀, subst_X hg₀],
      PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalInverse]
  rw [← mapThetaPoint_neg W h1c h1ne]
  exact mapThetaPoint_add_of_ne W h0c hqneg_c h0ne hqneg_ne
    (ne_of_subst_eq_X_of_subst_eq_zero hg₀X0 hg₀_qneg)
    (ne_of_subst_eq_X_of_subst_eq_zero hg₀X0 (by
      rw [MvPowerSeries.subst_powerSeriesSubst hg₀ (.of_constantCoeff_zero hqneg_c), hg₀_qneg,
        PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalInverse]))
    hFm_c' hFm_ne'

/-- Chord identity `(θ(X₀) + θ(X₁)) + (θ(X₀) - θ(X₁)) = θ([2]_Ê(X₀))` in `Fin 2`. -/
private theorem mapThetaPoint_two_nsmul_X_zero (W : WeierstrassCurve K) [W.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries (Fin 2) K))] :
    let h0c : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 0
    let h0ne : (X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
    ∃ (h2c : constantCoeff (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K)
        ((formalGroup W).nsmulSeries 2)) = 0)
      (h2ne : PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K)
        ((formalGroup W).nsmulSeries 2) ≠ 0),
      (2 : ℕ) • mapThetaPoint W h0c h0ne = mapThetaPoint W h2c h2ne := by
  intro h0c h0ne
  have h1c : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 1
  have h1ne : (X 1 : MvPowerSeries (Fin 2) K) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  let g₀ : Fin 2 → PowerSeries K := ![PowerSeries.X, 0]
  have hg₀ : MvPowerSeries.HasSubst g₀ := MvPowerSeries.HasSubst.X_zero (i := ())
  let p₀ : (formalGroup W).Point (Fin 2) := ⟨X 0, .of_constantCoeff_zero h0c⟩
  let p₁ : (formalGroup W).Point (Fin 2) := ⟨X 1, .of_constantCoeff_zero h1c⟩
  obtain ⟨hFp_c, hFm_c, hFp_ne, hFm_ne, hFpm_ne₁, hFpm_ne₂, hF₂_c, hF₂_ne⟩ :=
    sum_and_diff_tautological_ne W
  have hFm_val : (p₀ + -p₁).val = MvPowerSeries.subst
      ![X 0, PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) W.formalInverse]
      (formalGroup W).toPowerSeries := by
    -- Unfold addition and negation in `(formalGroup W).Point (Fin 2)`.
    change MvPowerSeries.subst ![X 0, PowerSeries.subst (X 1) (formalGroup W).addInvX]
      (formalGroup W).toPowerSeries = _
    rw [W.formalGroup_addInvX]
  have hF₂_eq : MvPowerSeries.subst ![(p₀ + p₁).val, (p₀ + -p₁).val]
      (formalGroup W).toPowerSeries = PowerSeries.subst (X 0) ((formalGroup W).nsmulSeries 2) := by
    -- Express the outer `MvPowerSeries.subst` as addition in `(formalGroup W).Point (Fin 2)`.
    change ((p₀ + p₁) + (p₀ + -p₁)).val = _
    have hgrp : (p₀ + p₁) + (p₀ + -p₁) = 2 • p₀ := by abel
    rw [hgrp, ← (formalGroup W).subst_nsmulSeries p₀ 2]
  have hg₀X0 : MvPowerSeries.subst g₀ (X 0 : MvPowerSeries (Fin 2) K) = PowerSeries.X := by
    simp [g₀, subst_X hg₀]
  have hg₀X1 : MvPowerSeries.subst g₀ (X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp [g₀, subst_X hg₀]
  have e_p := mapThetaPoint_add_of_ne W h0c h1c h0ne h1ne
    (ne_of_subst_eq_X_of_subst_eq_zero hg₀X0 hg₀X1)
    (ne_of_subst_eq_X_of_subst_eq_zero hg₀X0 (by
      rw [MvPowerSeries.subst_powerSeriesSubst hg₀ (.of_constantCoeff_zero h1c), hg₀X1,
        PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalInverse])) hFp_c hFp_ne
  have hFm_c' := hFm_val ▸ hFm_c
  have hFm_ne' := hFm_val ▸ hFm_ne
  have e_m := mapThetaPoint_add_neg_X_zero_X_one W h0c h1c h0ne h1ne hFm_c' hFm_ne'
  have e_2 := mapThetaPoint_add_of_ne W hFp_c hFm_c hFp_ne hFm_ne hFpm_ne₁ hFpm_ne₂ hF₂_c hF₂_ne
  have h2c : constantCoeff (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K)
      ((formalGroup W).nsmulSeries 2)) = 0 := hF₂_eq ▸ hF₂_c
  have h2ne : PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K)
      ((formalGroup W).nsmulSeries 2) ≠ 0 := hF₂_eq ▸ hF₂_ne
  refine ⟨h2c, h2ne, ?_⟩
  rw [← mapThetaPoint_congr W hF₂_eq hF₂_c hF₂_ne h2c h2ne, ← e_2,
    mapThetaPoint_congr W hFm_val hFm_c hFm_ne hFm_c' hFm_ne', ← e_p, ← e_m]
  abel

/-- On an elliptic curve `W`, the formal series of `2 • Hom.id W.toAffine` agrees with the doubling
series `(formalGroup W).nsmulSeries 2`. -/
private theorem formalSeries_two_nsmul_id (W : WeierstrassCurve K) [W.IsElliptic] :
    ((2 : ℕ) • Hom.id W.toAffine).formalSeries = (formalGroup W).nsmulSeries 2 := by
  classical
  let KK := FractionRing (MvPowerSeries (Fin 2) K)
  have h0c : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X 0
  have h0ne : (X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  obtain ⟨h2c, h2ne, htheta2⟩ := mapThetaPoint_two_nsmul_X_zero W
  have h2hom_ne : (2 : ℕ) • Hom.id W.toAffine ≠ 0 := fun h ↦ by
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← zero_zsmul (Hom.id W.toAffine)] at h
    exact (by decide : (2 : ℤ) ≠ 0) (Hom.zsmul_id_injective h)
  have hpt : (((2 : ℕ) • Hom.id W.toAffine).map (algebraMap K KK)).pointMap
      (mapThetaPoint W h0c h0ne) = mapThetaPoint W h2c h2ne := by
    rw [map_nsmul, Hom.id_map, Hom.nsmul_pointMap, Hom.id_pointMap, htheta2]
  have hpt' : (((2 : ℕ) • Hom.id W.toAffine).map (algebraMap K KK)).pointMap
      (mapThetaPoint W h0c h0ne) =
      mapThetaPoint W
        (PowerSeries.constantCoeff_subst_eq_zero h0c _
          (toIsogeny h2hom_ne).constantCoeff_formalSeries)
        (subst_mvPowerSeries_ne_zero h0c h0ne (toIsogeny h2hom_ne).formalSeries_ne_zero) := by
    nth_rw 1 [← ofIsogeny_toIsogeny h2hom_ne]
    exact pointMap_ofIsogeny_mapThetaPoint (toIsogeny h2hom_ne) h0c h0ne
  have hX0 := mapThetaPoint_inj W _ h2c _ h2ne (hpt'.symm.trans hpt)
  let g₀ : Fin 2 → PowerSeries K := ![PowerSeries.X, 0]
  have hg₀ : MvPowerSeries.HasSubst g₀ := MvPowerSeries.HasSubst.X_zero (i := ())
  have hsub := congrArg (MvPowerSeries.subst g₀) hX0
  rw [MvPowerSeries.subst_powerSeriesSubst hg₀ (.of_constantCoeff_zero h0c),
    MvPowerSeries.subst_powerSeriesSubst hg₀ (.of_constantCoeff_zero h0c),
    show MvPowerSeries.subst g₀ (X 0) = PowerSeries.X by simp [g₀, subst_X hg₀],
    PowerSeries.X_subst, PowerSeries.X_subst] at hsub
  rw [← ofIsogeny_toIsogeny h2hom_ne, formalSeries_ofIsogeny]
  exact hsub

variable {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

/-- Generic case of Silverman IV.4.2(b): when `φ ≠ ψ` and `φ + ψ ≠ 0`, the formal series of
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
  have hFc : constantCoeff
      (MvPowerSeries.subst ![φ.formalSeries, ψ.formalSeries] (formalGroup W₂).toPowerSeries) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero
      (PowerSeries.hasSubst_pair φ.constantCoeff_formalSeries ψ.constantCoeff_formalSeries)
      (fun i ↦ by
        fin_cases i
        · exact φ.constantCoeff_formalSeries
        · exact ψ.constantCoeff_formalSeries)
      (formalGroup W₂).zero_constantCoeff
  have hF0 : MvPowerSeries.subst ![φ.formalSeries, ψ.formalSeries]
      (formalGroup W₂).toPowerSeries ≠ 0 := fun h0 ↦
    hne₂ <| by
      rw [← W₂.formalGroup_addInvX]
      exact ((formalGroup W₂).eq_subst_addInvX_iff_subst_left_eq_zero
        (.of_constantCoeff_zero' ψ.constantCoeff_formalSeries)
        (.of_constantCoeff_zero' φ.constantCoeff_formalSeries)).mpr h0
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

/-- **Silverman IV.4.2(b)**: the formal power series of a sum of morphisms `f, g : Hom W₁ W₂` is
the formal-group sum of their formal power series:
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
    rw [h2f, formalSeries_comp, formalSeries_two_nsmul_id, FormalGroup.nsmulSeries_succ,
      FormalGroup.nsmulSeries_one, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply
        (PowerSeries.hasSubst_pair PowerSeries.constantCoeff_X PowerSeries.constantCoeff_X)
        f.hasSubst_formalSeries.const]
    congr 1
    funext i
    fin_cases i <;> simp [← PowerSeries.subst_def, PowerSeries.subst_X f.hasSubst_formalSeries]
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
    · have h0 : (fun i : Fin 2 ↦ (0 : K⟦X⟧).toMvPowerSeries i) = 0 := by
        funext i
        rw [PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.subst_zero]
        rfl
      rw [formalSeries_zero, PowerSeries.subst_zero, h0,
        MvPowerSeries.subst_zero_of_constantCoeff_zero (formalGroup W₂).zero_constantCoeff]
    · rw [formalSeries_ofIsogeny]
      exact φ.subst_formalGroup_formalSeries

@[simp]
theorem formalGroupHom_toPowerSeries (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalGroupHom.toPowerSeries = f.formalSeries :=
  (rfl)

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

end MulByInt

end TauCeti.Isogeny

end
