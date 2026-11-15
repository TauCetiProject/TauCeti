/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny.Differential
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.ThirdPoint
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import TauCeti.RingTheory.FormalGroup.Frobenius.Basic
import TauCeti.RingTheory.LaurentSeries.Substitution.MvPowerSeries
import TauCeti.RingTheory.MvPowerSeries.Rename
import TauCeti.RingTheory.PowerSeries.SubstInv

/-!
# Morphisms of elliptic curves induce homomorphisms of formal group laws

Expanding a morphism `f : Hom W₁ W₂` of elliptic curves in the local parameter `z = -x/y` at
infinity assigns to `f` a power series `f.formalSeries ∈ K⟦X⟧` with zero constant coefficient (`0`
for the zero morphism, `Isogeny.formalSeries` for an isogeny). This file proves the two halves of
Silverman, *The Arithmetic of Elliptic Curves*, Theorem IV.4.2:

1. **Additivity in the morphism** (`TauCeti.Isogeny.Hom.formalPointAddHom`): `f ↦ f.formalPoint`
   is an injective additive group homomorphism
   `Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit`. In particular, for `[n] : W → W`
   with `ψ_n ≠ 0`, `[n].formalSeries = (formalGroup W).zsmulSeries n`
   (`TauCeti.Isogeny.formalSeries_mulByIntIsogeny`).
2. **Compatibility with the formal group laws** (`TauCeti.Isogeny.formalGroupHom`): every isogeny
   `φ : W₁ → W₂` induces a bundled homomorphism `FormalGroupHom (formalGroup W₁) (formalGroup W₂)`
   with underlying power series `φ.formalSeries`, functorially with respect to identity and
   composition.

Both proofs evaluate rational functions on the curve at power-series parameters in the fraction
field of `MvPowerSeries (Fin 2) K` via `TauCeti.LaurentSeries.mvSubstAlgHom`, matching `Point.map`
on generic and tautological points with the chord parametrization `WeierstrassCurve.thetaPoint`.

## Main definitions

* `TauCeti.Isogeny.Hom.formalSeries`: the formal series at infinity of a morphism in `Hom W₁ W₂`.
* `TauCeti.Isogeny.Hom.formalPoint`: the formal-group point in `(formalGroup W₂).Point Unit`
  attached to a morphism.
* `TauCeti.Isogeny.Hom.formalPointAddHom`: `Hom.formalPoint` bundled as an injective additive
  homomorphism when `W₂` is elliptic.
* `TauCeti.Isogeny.formalGroupHom`: the bundled
  `FormalGroupHom (formalGroup W₁) (formalGroup W₂)` induced by an isogeny `φ : W₁ → W₂` when `W₂`
  is elliptic.

## Main results

* `TauCeti.Isogeny.formalSeries_injective` and `TauCeti.Isogeny.Hom.formalSeries_injective`: an
  isogeny (and a morphism) is determined by its formal series.
* `TauCeti.Isogeny.formalSeries_negIsogeny`: `[-1].formalSeries = (formalGroup W).addInvX`.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny` and
  `TauCeti.Isogeny.formalSeries_mulByIntIsogeny_natCast`: `[n].formalSeries =
  (formalGroup W).zsmulSeries n` (and `nsmulSeries n` for natural `n`).
* `TauCeti.Isogeny.formalGroupHom_id`, `TauCeti.Isogeny.formalGroupHom_comp`,
  `TauCeti.Isogeny.formalGroupHom_negIsogeny`, `TauCeti.Isogeny.formalGroupHom_mulByIntIsogeny`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4 (especially IV.4.2).
-/

public section

open HahnSeries MvPowerSeries WeierstrassCurve WeierstrassCurve.Affine
open scoped LaurentSeries PowerSeries nonZeroDivisors

namespace TauCeti.Isogeny

section Basic

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

/-- **An isogeny is determined by its formal power series at infinity**, with no ellipticity
assumption on either curve. -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := by
  intro φ ψ h
  have hparam : φ.fieldPullback (-W₂.toAffine.genericX / W₂.toAffine.genericY) =
      ψ.fieldPullback (-W₂.toAffine.genericX / W₂.toAffine.genericY) := by
    apply W₁.functionFieldLaurentExpansion.injective
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← φ.coe_formalSeries,
      ← ψ.coe_formalSeries] using congrArg (ofPowerSeries ℤ K) h
  have hw : φ.fieldPullback (-W₂.toAffine.genericY⁻¹) =
      ψ.fieldPullback (-W₂.toAffine.genericY⁻¹) := by
    apply W₁.functionFieldLaurentExpansion.injective
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← φ.coe_subst_formalW_formalSeries,
      ← ψ.coe_subst_formalW_formalSeries, h]
  have hY : φ.fieldPullback W₂.toAffine.genericY = ψ.fieldPullback W₂.toAffine.genericY := by
    simpa only [map_neg, map_inv₀, neg_inj, inv_inj] using hw
  have hX : φ.fieldPullback W₂.toAffine.genericX = ψ.fieldPullback W₂.toAffine.genericX := by
    have hy : ψ.fieldPullback W₂.toAffine.genericY ≠ 0 :=
      (map_ne_zero_iff _ ψ.fieldPullback.injective).mpr W₂.toAffine.genericY_ne_zero
    simpa only [map_div₀, map_neg, hY, div_left_inj₀ hy, neg_inj] using hparam
  have hfp : φ.fieldPullback = ψ.fieldPullback :=
    AlgHom.toRingHom_injective (Affine.FunctionField.ringHom_ext (fun c ↦ by simp) hX hY)
  refine Isogeny.ext (AlgHom.ext fun z ↦ ?_)
  rw [← φ.fieldPullback_algebraMap, ← ψ.fieldPullback_algebraMap, hfp]

/-- Two isogenies agree if and only if their formal power series at infinity agree. -/
@[simp]
theorem formalSeries_inj {φ ψ : Isogeny W₁.toAffine W₂.toAffine} :
    φ.formalSeries = ψ.formalSeries ↔ φ = ψ :=
  formalSeries_injective.eq_iff

/-- **The formal series of the negation isogeny is the geometric formal inverse** `W.formalInverse`,
with no ellipticity assumption on `W`. -/
theorem formalSeries_negIsogeny_eq_formalInverse (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).formalSeries = W.formalInverse := by
  apply (formalSeries_eq_iff _ _).mpr
  set q : K⸨X⸩ := ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)
  set w : K⸨X⸩ := (formalW W : K⸨X⸩)
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    rw [← W.functionFieldLaurentExpansion_neg_inv_genericY]
    exact (map_ne_zero_iff W.functionFieldLaurentExpansion
      W.functionFieldLaurentExpansion.injective).mpr
        (neg_ne_zero.mpr (inv_ne_zero W.toAffine.genericY_ne_zero))
  have hmul : (formalInverseDenom W : K⸨X⸩) *
      (PowerSeries.invOfUnit (formalInverseDenom W) 1 : K⸨X⸩) = 1 := by
    simpa only [PowerSeries.coe_mul, PowerSeries.coe_one] using
      congrArg (ofPowerSeries ℤ K) (mul_invOfUnit_formalInverseDenom W)
  have hD0 : (formalInverseDenom W : K⸨X⸩) ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hDeq : (formalInverseDenom W : K⸨X⸩) =
      1 - algebraMap K K⸨X⸩ W.a₁ * q - algebraMap K K⸨X⸩ W.a₃ * w := by
    rw [formalInverseDenom_def]
    simp only [← PowerSeries.algebraMap_eq, ← LaurentSeries.coe_algebraMap, map_sub, map_one,
      map_mul, ← IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩, q, w]
  have hIeq : (W.formalInverse : K⸨X⸩) =
      -(q * (PowerSeries.invOfUnit (formalInverseDenom W) 1 : K⸨X⸩)) := by
    rw [formalInverse_def]; simp only [PowerSeries.coe_neg, PowerSeries.coe_mul, q]
  have hdenom : -(-1 / w) - algebraMap K K⸨X⸩ W.a₁ * (q / w) - algebraMap K K⸨X⸩ W.a₃ =
      (formalInverseDenom W : K⸨X⸩) / w := by
    rw [hDeq]; field_simp
  rw [map_div₀, map_neg, fieldPullback_negIsogeny_genericX, fieldPullback_negIsogeny_genericY,
    Affine.negY]
  simp only [WeierstrassCurve.baseChange, map_a₁, map_a₃, map_div₀, map_sub, map_neg, map_mul,
    AlgHom.commutes]
  have hq_def : ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) = q := rfl
  have hw_def : (formalW W : K⸨X⸩) = w := rfl
  rw [W.functionFieldLaurentExpansion_genericX_eq_div,
    W.functionFieldLaurentExpansion_genericY_eq_div, hq_def, hw_def, hIeq, hdenom]
  field_simp [hw0, hD0]
  linear_combination -q * hmul

/-- **The formal series of the negation isogeny is the inverse series of `formalGroup W`.** -/
@[simp]
theorem formalSeries_negIsogeny (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).formalSeries = (formalGroup W).addInvX := by
  rw [formalSeries_negIsogeny_eq_formalInverse, W.formalGroup_addInvX]

end Basic

/-! ### Series-parameter evaluation into the fraction field of `MvPowerSeries` -/

section SeriesEval

variable {K : Type*} [Field K] {σ : Type*}

/-- Evaluation of the function field of `W` at a nonzero parameter `q` with zero constant
coefficient, by expanding at infinity and evaluating the resulting Laurent series at `q`. -/
private noncomputable def curveEval (W : WeierstrassCurve K) {q : MvPowerSeries σ K}
    (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    W.toAffine.FunctionField →ₐ[K] FractionRing (MvPowerSeries σ K) :=
  (TauCeti.LaurentSeries.mvSubstAlgHom hq hq0).comp W.functionFieldLaurentExpansion

private theorem curveEval_comp_fieldPullback {W₁ W₂ : WeierstrassCurve K}
    (φ : Isogeny W₁.toAffine W₂.toAffine) {q : MvPowerSeries σ K}
    (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    (curveEval W₁ hq hq0).comp φ.fieldPullback =
      curveEval W₂
        (PowerSeries.constantCoeff_subst_eq_zero hq φ.formalSeries φ.constantCoeff_formalSeries)
        (PowerSeries.subst_mvPowerSeries_ne_zero hq hq0 φ.formalSeries_ne_zero) := by
  refine AlgHom.ext fun z ↦ ?_
  simp only [curveEval, AlgHom.comp_apply, φ.functionFieldLaurentExpansion_fieldPullback,
    TauCeti.LaurentSeries.mvSubstAlgHom_comp_substAlgHom_apply]

private theorem toAffine_fracCurve_eq_baseChange (W : WeierstrassCurve K) :
    (fracCurve W σ (FractionRing (MvPowerSeries σ K))).toAffine =
      W.toAffine⁄(FractionRing (MvPowerSeries σ K)) := by
  rw [fracCurve_def, Affine.baseChange, WeierstrassCurve.baseChange,
    ← IsScalarTower.algebraMap_eq K (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))]

private theorem thetaPoint_nonsingular (W : WeierstrassCurve K) [W.IsElliptic]
    {q : MvPowerSeries σ K} (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    (fracCurve W σ (FractionRing (MvPowerSeries σ K))).toAffine.Nonsingular
      (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) q /
        algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
          (PowerSeries.subst q (formalW W)))
      (-1 / algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
        (PowerSeries.subst q (formalW W))) := by
  refine chord_point_nonsingular _ ?_ (W.algebraMap_subst_formalW_ne_zero hq hq0)
    (W.fracCurve_Δ_ne_zero W.toAffine.isUnit_Δ.ne_zero)
  have hw := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)))
    (subst_formalW_wEquation W (.of_constantCoeff_zero hq))
  simpa [fracCurve_def, wEquationRHS_def] using hw

/-- Transport `thetaPoint` along `(fracCurve W σ M).toAffine = W.toAffine⁄M`. -/
private noncomputable def thetaBasePoint (W : WeierstrassCurve K) [W.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries σ K))]
    {q : MvPowerSeries σ K} (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    (W.toAffine⁄(FractionRing (MvPowerSeries σ K))).Point :=
  AddEquiv.cast
    (M := fun V : WeierstrassCurve.Affine (FractionRing (MvPowerSeries σ K)) ↦ V.Point)
    (toAffine_fracCurve_eq_baseChange (σ := σ) W)
    (W.thetaPoint (W.fracCurve_Δ_ne_zero W.toAffine.isUnit_Δ.ne_zero) hq hq0)

private theorem cast_point_some {R : Type*} [Field R] [DecidableEq R]
    {V₁ V₂ : WeierstrassCurve.Affine R} (hV : V₁ = V₂) (x y : R)
    (hns : V₁.Nonsingular x y) :
    AddEquiv.cast (M := fun V : WeierstrassCurve.Affine R ↦ V.Point) hV (Point.some x y hns) =
      Point.some x y (hV ▸ hns) := by
  subst hV; rfl

private theorem thetaBasePoint_inj (W : WeierstrassCurve K) [W.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries σ K))]
    {q₁ q₂ : MvPowerSeries σ K}
    (h₁ : MvPowerSeries.constantCoeff q₁ = 0) (h₂ : MvPowerSeries.constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (h : thetaBasePoint W h₁ hq₁0 = thetaBasePoint W h₂ hq₂0) : q₁ = q₂ := by
  set M := FractionRing (MvPowerSeries σ K)
  set ρ := algebraMap (MvPowerSeries σ K) M with hρ
  have hinj : Function.Injective ρ := IsFractionRing.injective (MvPowerSeries σ K) M
  have hθ := (AddEquiv.cast
    (M := fun V : WeierstrassCurve.Affine M ↦ V.Point)
    (toAffine_fracCurve_eq_baseChange (σ := σ) W)).injective h
  have hΔ := W.fracCurve_Δ_ne_zero (σ := σ) (KK := M) W.toAffine.isUnit_Δ.ne_zero
  rw [W.thetaPoint_eq_some hΔ h₁ hq₁0 (thetaPoint_nonsingular W h₁ hq₁0),
    W.thetaPoint_eq_some hΔ h₂ hq₂0 (thetaPoint_nonsingular W h₂ hq₂0),
    Point.some.injEq] at hθ
  simp only [← hρ] at hθ
  have hw₁0 : ρ (PowerSeries.subst q₁ (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero h₁ hq₁0
  have hw₂0 : ρ (PowerSeries.subst q₂ (formalW W)) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero h₂ hq₂0
  have hw : ρ (PowerSeries.subst q₁ (formalW W)) = ρ (PowerSeries.subst q₂ (formalW W)) :=
    inv_inj.mp (neg_inj.mp (by simpa only [neg_div, one_div] using hθ.2))
  refine hinj ?_
  have h1 := hθ.1
  rw [div_eq_div_iff hw₁0 hw₂0, hw] at h1
  exact mul_right_cancel₀ hw₂0 h1

private theorem subst_pairSubstitution_formalAdd_eq (W : WeierstrassCurve K)
    {a b : MvPowerSeries σ K}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst (pairSubstitution a b) (formalAdd W) =
      MvPowerSeries.subst ![a, b] (formalGroup W).toPowerSeries := by
  rw [formalGroup_toPowerSeries, MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i; exacts [ha, hb])]
  congr 1; funext s; rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp

private theorem thetaBasePoint_add_of_subst_separates (W : WeierstrassCurve K) [W.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries σ K))]
    {g : σ → MvPowerSeries Unit K} (hg : MvPowerSeries.HasSubst g)
    {q₁ q₂ : MvPowerSeries σ K}
    (h₁ : MvPowerSeries.constantCoeff q₁ = 0) (h₂ : MvPowerSeries.constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hg₁ : MvPowerSeries.subst g q₁ = PowerSeries.X)
    (hg₂ : MvPowerSeries.subst g q₂ = 0) :
    thetaBasePoint W h₁ hq₁0 + thetaBasePoint W h₂ hq₂0 =
      thetaBasePoint W (q := MvPowerSeries.subst ![q₁, q₂] (formalGroup W).toPowerSeries)
        (by
          rw [← subst_pairSubstitution_formalAdd_eq W h₁ h₂]
          exact constantCoeff_subst_pair_formalAdd W h₁ h₂)
        (by
          rw [← subst_pairSubstitution_formalAdd_eq W h₁ h₂]
          exact W.subst_pair_formalAdd_ne_zero hg h₁ h₂ hg₁ hg₂) := by
  have hΔ := W.fracCurve_Δ_ne_zero (σ := σ) (KK := FractionRing (MvPowerSeries σ K))
    W.toAffine.isUnit_Δ.ne_zero
  have hF : MvPowerSeries.constantCoeff (MvPowerSeries.subst (pairSubstitution q₁ q₂)
      (formalAdd W)) = 0 := constantCoeff_subst_pair_formalAdd W h₁ h₂
  have hF0 : MvPowerSeries.subst (pairSubstitution q₁ q₂) (formalAdd W) ≠ 0 :=
    W.subst_pair_formalAdd_ne_zero hg h₁ h₂ hg₁ hg₂
  have htheta_congr {a b : MvPowerSeries σ K} (hab : a = b)
      (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0)
      (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
      W.thetaPoint hΔ ha ha0 = W.thetaPoint hΔ hb hb0 := by
    subst hab; rfl
  simp only [thetaBasePoint, ← map_add,
    W.thetaPoint_add_of_subst_separates hΔ hg h₁ h₂ hq₁0 hq₂0 hg₁ hg₂ hF hF0]
  exact congrArg _ (htheta_congr (subst_pairSubstitution_formalAdd_eq W h₁ h₂) hF _ hF0 _)

private theorem map_curveEval_genericPoint (W : WeierstrassCurve K) [W.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries σ K))]
    {q : MvPowerSeries σ K} (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    Point.map (curveEval W hq hq0) W.toAffine.genericPoint = thetaBasePoint W hq hq0 := by
  rw [genericPoint_eq_some, Point.map_some, thetaBasePoint,
    W.thetaPoint_eq_some _ hq hq0 (thetaPoint_nonsingular W hq hq0), cast_point_some,
    Point.some.injEq]
  exact ⟨by
      rw [curveEval, AlgHom.comp_apply, W.functionFieldLaurentExpansion_genericX_eq_div, map_div₀,
        TauCeti.LaurentSeries.mvSubstAlgHom_coe, TauCeti.LaurentSeries.mvSubstAlgHom_coe,
        PowerSeries.subst_X (.of_constantCoeff_zero hq)],
    by
      rw [curveEval, AlgHom.comp_apply, W.functionFieldLaurentExpansion_genericY_eq_div, map_div₀,
        map_neg, map_one, TauCeti.LaurentSeries.mvSubstAlgHom_coe]⟩

private theorem map_curveEval_tautologicalPoint {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries σ K))]
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    {q : MvPowerSeries σ K} (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    Point.map (curveEval W₁ hq hq0) φ.pullback.tautologicalPoint =
      thetaBasePoint W₂
        (PowerSeries.constantCoeff_subst_eq_zero hq φ.formalSeries φ.constantCoeff_formalSeries)
        (PowerSeries.subst_mvPowerSeries_ne_zero hq hq0 φ.formalSeries_ne_zero) := by
  rw [tautologicalPoint_eq_map_genericPoint]
  refine Eq.trans ?_ ((congrArg (fun e ↦ Point.map e W₂.toAffine.genericPoint)
      (curveEval_comp_fieldPullback φ hq hq0)).trans (map_curveEval_genericPoint W₂ _ _))
  rw [genericPoint_eq_some, Point.map_some, Point.map_some, Point.map_some]
  rfl

end SeriesEval

/-! ### Morphisms to formal-group points (`Hom.formalPointAddHom`) -/

namespace Hom

section Carrier

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

open scoped Classical in
/-- The formal power series of a morphism `f : Hom W₁ W₂` in the local parameter `z = -x/y` at
infinity: `0` for the zero morphism, and `Isogeny.formalSeries` for an isogeny. -/
noncomputable def formalSeries (f : Hom W₁.toAffine W₂.toAffine) : K⟦X⟧ :=
  if hf : f = 0 then 0 else (toIsogeny hf).formalSeries

open scoped Classical in
/-- Unfolding equation for `Hom.formalSeries`. -/
theorem formalSeries_def (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalSeries = if hf : f = 0 then 0 else (toIsogeny hf).formalSeries :=
  (rfl)

/-- The formal series of the zero morphism is `0`. -/
@[simp]
theorem formalSeries_zero : (0 : Hom W₁.toAffine W₂.toAffine).formalSeries = 0 :=
  dite_eq_left_of_eq_true (eq_true rfl)

/-- The formal series of `ofIsogeny φ` is `φ.formalSeries`. -/
@[simp]
theorem formalSeries_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalSeries = φ.formalSeries := by
  rw [formalSeries, dite_eq_right_of_eq_false (eq_false (ofIsogeny_ne_zero φ)),
    toIsogeny_ofIsogeny]

/-- The formal series of the identity morphism is `X`. -/
@[simp]
theorem formalSeries_id (W : WeierstrassCurve K) :
    (id W.toAffine).formalSeries = PowerSeries.X := by
  rw [id_def, formalSeries_ofIsogeny, Isogeny.formalSeries_id]

/-- The formal series of `1` in the endomorphism ring is `X`. -/
theorem formalSeries_one (W : WeierstrassCurve K) :
    (1 : Hom W.toAffine W.toAffine).formalSeries = PowerSeries.X :=
  formalSeries_id W

/-- The formal series of any morphism has constant coefficient zero. -/
-- Handle composites and sums before `formalSeries_comp` or `formalSeries_add` unfolds them.
@[simp↓]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

/-- A morphism has zero formal series if and only if it is the zero morphism. -/
@[simp]
theorem formalSeries_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · simp [φ.formalSeries_ne_zero, ofIsogeny_ne_zero]

/-- **A morphism in `Hom W₁ W₂` is determined by its formal series at infinity**, with no
ellipticity assumption on either curve. -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := by
  intro f g h
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · exact (formalSeries_eq_zero_iff.mp (h.symm.trans formalSeries_zero)).symm
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · exact formalSeries_eq_zero_iff.mp (h.trans formalSeries_zero)
  rw [formalSeries_ofIsogeny, formalSeries_ofIsogeny, Isogeny.formalSeries_inj] at h
  rw [h]

/-- Two morphisms agree if and only if their formal series agree. -/
@[simp]
theorem formalSeries_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = g.formalSeries ↔ f = g :=
  formalSeries_injective.eq_iff

/-- Composition of morphisms induces substitution of their formal series. -/
@[simp]
theorem formalSeries_comp (g : Hom W₂.toAffine W₃.toAffine)
    (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalSeries = PowerSeries.subst f.formalSeries g.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · simp
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp [PowerSeries.subst_zero_of_constantCoeff_zero ψ.constantCoeff_formalSeries]
  · simp [Isogeny.formalSeries_comp]

/-- Negating a morphism composes its formal series with the inverse series of `formalGroup W₂`. -/
@[simp]
theorem formalSeries_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalSeries = PowerSeries.subst f.formalSeries (formalGroup W₂).addInvX := by
  rw [neg_def, formalSeries_comp, formalSeries_ofIsogeny, formalSeries_negIsogeny]

/-- The formal-group point in `(formalGroup W₂).Point Unit` attached to a morphism `f : Hom W₁ W₂`.
No ellipticity assumption is needed to form the point itself. -/
noncomputable def formalPoint (f : Hom W₁.toAffine W₂.toAffine) :
    (formalGroup W₂).Point Unit :=
  ⟨f.formalSeries, .of_constantCoeff_zero f.constantCoeff_formalSeries⟩

/-- The underlying power series of `f.formalPoint` is `f.formalSeries`. -/
@[simp]
theorem val_formalPoint (f : Hom W₁.toAffine W₂.toAffine) :
    (f.formalPoint).val = f.formalSeries :=
  (rfl)

/-- The formal-group point of the zero morphism is `0`. -/
@[simp]
theorem formalPoint_zero : (0 : Hom W₁.toAffine W₂.toAffine).formalPoint = 0 :=
  Subtype.ext formalSeries_zero

/-- The formal-group point of the identity morphism is the tautological point `X`. -/
@[simp]
theorem formalPoint_id (W : WeierstrassCurve K) :
    (id W.toAffine).formalPoint = (formalGroup W).tautologicalPoint :=
  Subtype.ext ((formalSeries_id W).trans (formalGroup W).val_tautologicalPoint.symm)

/-- Sending a morphism to its formal-group point is injective. -/
theorem formalPoint_injective :
    Function.Injective (formalPoint (W₁ := W₁) (W₂ := W₂)) := fun _ _ h ↦
  formalSeries_injective (congrArg Subtype.val h)

/-- Two morphisms agree if and only if their formal-group points agree. -/
@[simp]
theorem formalPoint_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalPoint = g.formalPoint ↔ f = g :=
  formalPoint_injective.eq_iff

/-- The formal-group point of `-f` is `-f.formalPoint`. -/
@[simp]
theorem formalPoint_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalPoint = -f.formalPoint :=
  Subtype.ext (formalSeries_neg f)

end Carrier

section Additive

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

/-- Auxiliary parameter separation for `ofIsogeny φ + ofIsogeny ψ = ofIsogeny χ`: push
`χ.tautologicalPoint = φ.tautologicalPoint + ψ.tautologicalPoint` to
`FractionRing (MvPowerSeries (Fin 2) K)` at `X₀`, add `θ(X₁)` on the left so `coordSpecialize 1`
(`X₁ ↦ X`, `X₀ ↦ 0`) separates every pair, and cancel `X₁` in `(formalGroup W₂).Point (Fin 2)`. -/
private theorem formalPoint_of_ofIsogeny_add_ofIsogeny
    {φ ψ χ : Isogeny W₁.toAffine W₂.toAffine}
    (hadd : ofIsogeny φ + ofIsogeny ψ = ofIsogeny χ) :
    χ.formalSeries =
      MvPowerSeries.subst ![φ.formalSeries, ψ.formalSeries] (formalGroup W₂).toPowerSeries := by
  classical
  -- Step 1: evaluate `χ.tautologicalPoint = φ.tautologicalPoint + ψ.tautologicalPoint` at `X₀`
  -- and translate both sides on the left by `θ(X₁)`.
  have htaut : χ.pullback.tautologicalPoint =
      φ.pullback.tautologicalPoint + ψ.pullback.tautologicalPoint := by
    simpa only [tautologicalPoint_add, tautologicalPoint_ofIsogeny] using
      congrArg tautologicalPoint hadd.symm
  set q₀ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0
  set q₁ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1
  have hq₀c : MvPowerSeries.constantCoeff q₀ = 0 := constantCoeff_X 0
  have hq₁c : MvPowerSeries.constantCoeff q₁ = 0 := constantCoeff_X 1
  have hq₀0 : q₀ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hq₁0 : q₁ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hφc := PowerSeries.constantCoeff_subst_eq_zero hq₀c φ.formalSeries
    φ.constantCoeff_formalSeries
  have hψc := PowerSeries.constantCoeff_subst_eq_zero hq₀c ψ.formalSeries
    ψ.constantCoeff_formalSeries
  have hχc := PowerSeries.constantCoeff_subst_eq_zero hq₀c χ.formalSeries
    χ.constantCoeff_formalSeries
  have hpts := congrArg (Point.map (curveEval W₁ hq₀c hq₀0)) htaut
  simp only [_root_.map_add, map_curveEval_tautologicalPoint] at hpts
  have hpts' : thetaBasePoint W₂ hq₁c hq₁0 +
      thetaBasePoint W₂ hχc (PowerSeries.subst_mvPowerSeries_ne_zero hq₀c hq₀0
        χ.formalSeries_ne_zero) =
      (thetaBasePoint W₂ hq₁c hq₁0 +
        thetaBasePoint W₂ hφc (PowerSeries.subst_mvPowerSeries_ne_zero hq₀c hq₀0
          φ.formalSeries_ne_zero)) +
      thetaBasePoint W₂ hψc (PowerSeries.subst_mvPowerSeries_ne_zero hq₀c hq₀0
        ψ.formalSeries_ne_zero) := by
    rw [hpts, ← add_assoc]
  -- Step 2: `coordSpecialize 1` sends `X₁ ↦ X` and `X₀ ↦ 0`, separating all three chord additions.
  set g : Fin 2 → MvPowerSeries Unit K := coordSpecialize (O := K) (1 : Fin 2)
  have hg : MvPowerSeries.HasSubst g := hasSubst_coordSpecialize _
  have hg_q₁ : MvPowerSeries.subst g q₁ = PowerSeries.X :=
    subst_coordSpecialize_X_self (O := K) (1 : Fin 2)
  have hg_q₀ : MvPowerSeries.subst g q₀ = 0 :=
    subst_coordSpecialize_X_of_ne (O := K) (i := (1 : Fin 2)) (j := 0) (by decide)
  have hg_subst (f : K⟦X⟧) (hf : PowerSeries.constantCoeff f = 0) :
      MvPowerSeries.subst g (PowerSeries.subst q₀ f) = 0 := by
    rw [subst_powerSeriesSubst hg (.of_constantCoeff_zero hq₀c), hg_q₀,
      PowerSeries.subst_zero_of_constantCoeff_zero hf]
  have hg_F₁φ : MvPowerSeries.subst g
      (MvPowerSeries.subst ![q₁, PowerSeries.subst q₀ φ.formalSeries]
        (formalGroup W₂).toPowerSeries) = PowerSeries.X := by
    have hsub_pair : MvPowerSeries.HasSubst ![q₁, PowerSeries.subst q₀ φ.formalSeries] :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i; exacts [hq₁c, hφc]
    have hg_pair : (fun i : Fin 2 ↦
        MvPowerSeries.subst g (![q₁, PowerSeries.subst q₀ φ.formalSeries] i)) =
        ![PowerSeries.X, 0] := funext fun i ↦ by
      fin_cases i; exacts [hg_q₁, hg_subst _ φ.constantCoeff_formalSeries]
    rw [MvPowerSeries.subst_comp_subst_apply hsub_pair hg, hg_pair]
    exact (formalGroup W₂).Xzero_eq_X
  rw [thetaBasePoint_add_of_subst_separates W₂ hg hq₁c hχc _ _ hg_q₁
      (hg_subst _ χ.constantCoeff_formalSeries),
    thetaBasePoint_add_of_subst_separates W₂ hg hq₁c hφc _ _ hg_q₁
      (hg_subst _ φ.constantCoeff_formalSeries),
    thetaBasePoint_add_of_subst_separates W₂ hg _ hψc _ _ hg_F₁φ
      (hg_subst _ ψ.constantCoeff_formalSeries)] at hpts'
  -- Step 3: cancel `X₁` in `(formalGroup W₂).Point (Fin 2)` and specialise `(X₀, X₁) ↦ (X, 0)`.
  have hseries := thetaBasePoint_inj W₂ _ _ _ _ hpts'
  let p₁ : (formalGroup W₂).Point (Fin 2) := ⟨q₁, .of_constantCoeff_zero hq₁c⟩
  let pφ : (formalGroup W₂).Point (Fin 2) :=
    ⟨PowerSeries.subst q₀ φ.formalSeries, .of_constantCoeff_zero hφc⟩
  let pψ : (formalGroup W₂).Point (Fin 2) :=
    ⟨PowerSeries.subst q₀ ψ.formalSeries, .of_constantCoeff_zero hψc⟩
  let pχ : (formalGroup W₂).Point (Fin 2) :=
    ⟨PowerSeries.subst q₀ χ.formalSeries, .of_constantCoeff_zero hχc⟩
  have hp : p₁ + pχ = p₁ + (pφ + pψ) := by rw [← add_assoc]; exact Subtype.ext hseries
  have hcancel : pχ.val = (pφ + pψ).val :=
    congrArg (fun p : (formalGroup W₂).Point (Fin 2) ↦ p.val) (add_left_cancel hp)
  rw [FormalGroup.add_apply] at hcancel
  set s₀ : Fin 2 → PowerSeries K := ![PowerSeries.X, 0]
  have hs₀ : MvPowerSeries.HasSubst s₀ := MvPowerSeries.HasSubst.X_zero
  have hs₀_q₀ : MvPowerSeries.subst s₀ q₀ = PowerSeries.X := by
    simp [q₀, s₀, MvPowerSeries.subst_X hs₀]
  have hspec := congrArg (MvPowerSeries.subst s₀) hcancel
  simp only [pχ, pφ, pψ, subst_powerSeriesSubst hs₀ (.of_constantCoeff_zero hq₀c), hs₀_q₀,
    PowerSeries.X_subst] at hspec
  rw [MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i; exacts [hφc, hψc])
    hs₀] at hspec
  refine hspec.trans ?_
  congr 1; funext i; fin_cases i <;>
    simp [subst_powerSeriesSubst hs₀ (.of_constantCoeff_zero hq₀c), hs₀_q₀,
      PowerSeries.X_subst]

/-- **Silverman IV.4.2 (additivity):** the formal-group point of `f + g` is the formal-group sum of
the formal-group points of `f` and `g`. -/
@[simp]
theorem formalPoint_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalPoint = f.formalPoint + g.formalPoint := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · simp
  rcases eq_zero_or_exists_ofIsogeny (ofIsogeny φ + ofIsogeny ψ) with h0 | ⟨χ, hχ⟩
  · have hg : ofIsogeny ψ = -ofIsogeny φ := eq_neg_of_add_eq_zero_right h0
    rw [h0, hg, formalPoint_zero, formalPoint_neg, add_neg_cancel]
  · rw [hχ]
    refine Subtype.ext ?_
    simpa only [FormalGroup.add_apply, val_formalPoint, formalSeries_ofIsogeny] using
      formalPoint_of_ofIsogeny_add_ofIsogeny hχ

/-- **The formal-series expansion of `Hom W₁ W₂` as an injective additive homomorphism** into
the formal group points `(formalGroup W₂).Point Unit` (Silverman IV.4.2). -/
noncomputable def formalPointAddHom :
    Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit where
  toFun := formalPoint
  map_zero' := formalPoint_zero
  map_add' := formalPoint_add

/-- Applying `formalPointAddHom` produces `Hom.formalPoint`. -/
@[simp]
theorem formalPointAddHom_apply (f : Hom W₁.toAffine W₂.toAffine) :
    formalPointAddHom f = f.formalPoint :=
  (rfl)

/-- The additive homomorphism `formalPointAddHom` is injective. -/
theorem formalPointAddHom_injective :
    Function.Injective (formalPointAddHom (W₁ := W₁) (W₂ := W₂)) :=
  formalPoint_injective

/-- **Silverman IV.4.2 (series form):** the formal series of `f + g` is obtained by substituting
`f.formalSeries` and `g.formalSeries` into `(formalGroup W₂).toPowerSeries`. -/
@[simp]
theorem formalSeries_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalSeries =
      MvPowerSeries.subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries :=
  congrArg Subtype.val (formalPoint_add f g)

/-- The formal-group point of `f - g` is `f.formalPoint - g.formalPoint`. -/
@[simp]
theorem formalPoint_sub (f g : Hom W₁.toAffine W₂.toAffine) :
    (f - g).formalPoint = f.formalPoint - g.formalPoint :=
  formalPointAddHom.map_sub f g

/-- The formal-group point of `n • f` (`n : ℕ`) is `n • f.formalPoint`. -/
@[simp]
theorem formalPoint_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalPoint = n • f.formalPoint :=
  _root_.map_nsmul formalPointAddHom n f

/-- The formal-group point of `n • f` (`n : ℤ`) is `n • f.formalPoint`. -/
@[simp]
theorem formalPoint_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalPoint = n • f.formalPoint :=
  _root_.map_zsmul formalPointAddHom n f

/-- Scalar multiplication by `n : ℤ` on a morphism substitutes its formal series into
`(formalGroup W₂).zsmulSeries n`. -/
@[simp]
theorem formalSeries_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries =
      PowerSeries.subst f.formalSeries ((formalGroup W₂).zsmulSeries n) := by
  rw [← val_formalPoint, formalPoint_zsmul,
    ← (formalGroup W₂).subst_zsmulSeries f.formalPoint n, val_formalPoint]

/-- Scalar multiplication by `n : ℕ` on a morphism substitutes its formal series into
`(formalGroup W₂).nsmulSeries n`. -/
@[simp]
theorem formalSeries_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries =
      PowerSeries.subst f.formalSeries ((formalGroup W₂).nsmulSeries n) := by
  rw [← natCast_zsmul f n, formalSeries_zsmul, FormalGroup.zsmulSeries_natCast]

end Additive

end Hom

/-! ### Multiplication-by-`n` and bundled formal-group homomorphisms -/

section MulByInt

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The formal series of multiplication-by-`n` on an elliptic curve is the `n`-multiplication
series of its formal group law** (Silverman IV.4.2). -/
@[simp]
theorem formalSeries_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  rw [← Hom.formalSeries_ofIsogeny, ofIsogeny_mulByIntIsogeny, Hom.formalSeries_zsmul,
    Hom.formalSeries_id, PowerSeries.X_subst]

/-- **The formal series of multiplication-by-`n` (`n : ℕ`) on an elliptic curve is
`(formalGroup W).nsmulSeries n`.** -/
theorem formalSeries_mulByIntIsogeny_natCast {n : ℕ}
    (hn : psiFunctionField W.toAffine (n : ℤ) ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).nsmulSeries n := by
  rw [formalSeries_mulByIntIsogeny, FormalGroup.zsmulSeries_natCast]

end MulByInt

section FormalGroupHom

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

/-- On `K[genericX, genericY] ⊆ F(W₁)`, the second-factor embedding `FunctionField.map` is
bounded by `1` and agrees with `algebraMap` to first order at the diagonal place. -/
private theorem valuation_genericPoint_place_functionFieldMap_sub_lt_one_of_mem_adjoin
    [W₁.IsElliptic]
    (heq : (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).Equation
      W₁.toAffine.genericX W₁.toAffine.genericY)
    {a : W₁.toAffine.FunctionField}
    (ha : a ∈ Algebra.adjoin K {W₁.toAffine.genericX, W₁.toAffine.genericY}) :
    let L := W₁.toAffine.FunctionField
    let ι := algebraMap K L
    let v := (Place.ofPrime L (W₁.toAffine.map ι).FunctionField
      (CoordinateRing.pointPlace heq)).valuation
    v (FunctionField.map W₁.toAffine ι a) ≤ 1 ∧
      v (FunctionField.map W₁.toAffine ι a - algebraMap L _ a) < 1 := by
  set L := W₁.toAffine.FunctionField
  set ι := algebraMap K L
  set v := (Place.ofPrime L (W₁.toAffine.map ι).FunctionField
    (CoordinateRing.pointPlace heq)).valuation
  set w := FunctionField.map W₁.toAffine ι
  set c := algebraMap L (W₁.toAffine.map ι).FunctionField
  have hc_le (b : L) : v (c b) ≤ 1 := Valuation.IsTrivialOn.valuation_algebraMap_le_one v b
  have hgen_le (b : L) (hlt : v (w b - c b) < 1) : v (w b) ≤ 1 ∧ v (w b - c b) < 1 := by
    have hsplit : w b = (w b - c b) + c b := by ring
    exact ⟨hsplit ▸ (v.map_add _ _).trans (max_le hlt.le (hc_le _)), hlt⟩
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
  · rintro b (rfl | rfl)
    · refine hgen_le _ ?_
      have hwX : w W₁.toAffine.genericX = (W₁.toAffine.map ι).genericX :=
        FunctionField.map_genericX W₁.toAffine ι
      rw [hwX]
      exact valuation_pointPlace_genericX_sub_lt_one (W₁.toAffine.map ι) heq
    · refine hgen_le _ ?_
      have hwY : w W₁.toAffine.genericY = (W₁.toAffine.map ι).genericY :=
        FunctionField.map_genericY W₁.toAffine ι
      rw [hwY]
      exact valuation_pointPlace_genericY_sub_lt_one (W₁.toAffine.map ι) heq
  · intro k
    have hk : w (algebraMap K L k) = c (algebraMap K L k) :=
      FunctionField.map_algebraMap W₁.toAffine ι k
    exact ⟨hk ▸ hc_le _, by rw [hk, sub_self, Valuation.map_zero]; exact zero_lt_one⟩
  · intro x y _ _ hx hy
    refine ⟨by rw [map_add]; exact (v.map_add _ _).trans (max_le hx.1 hy.1), ?_⟩
    rw [map_add, map_add, add_sub_add_comm]
    exact (v.map_add _ _).trans_lt (max_lt hx.2 hy.2)
  · intro x y _ _ hx hy
    refine ⟨by rw [map_mul, Valuation.map_mul]; exact mul_le_one' hx.1 hy.1, ?_⟩
    have hmul_sub : w x * w y - c x * c y = (w x - c x) * w y + c x * (w y - c y) := by ring
    rw [map_mul, map_mul, hmul_sub]
    refine (v.map_add _ _).trans_lt (max_lt ?_ ?_)
    · rw [Valuation.map_mul]; exact Left.mul_lt_one_of_lt_of_le hx.2 hy.1
    · rw [Valuation.map_mul]; exact Right.mul_lt_one_of_le_of_lt (hc_le x) hy.2

/-- At the diagonal place of `W₁.genericPoint` on `W₁⁄F(W₁)`, the second-factor embedding
`FunctionField.map W₁ (algebraMap K F(W₁))` agrees with the first-factor scalar embedding
`algebraMap F(W₁) _` to first order on every element of `F(W₁)`. -/
private theorem valuation_genericPoint_place_functionFieldMap_sub_lt_one [W₁.IsElliptic]
    (heq : (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).Equation
      W₁.toAffine.genericX W₁.toAffine.genericY)
    (z : W₁.toAffine.FunctionField) :
    (Place.ofPrime W₁.toAffine.FunctionField
      (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).FunctionField
      (CoordinateRing.pointPlace heq)).valuation
        (FunctionField.map W₁.toAffine (algebraMap K W₁.toAffine.FunctionField) z -
          algebraMap W₁.toAffine.FunctionField _ z) < 1 := by
  obtain ⟨r, s, hs_mem, rfl⟩ :=
    IsFractionRing.div_surjective (A := W₁.toAffine.CoordinateRing) z
  set L := W₁.toAffine.FunctionField
  set ι := algebraMap K L
  set v := (Place.ofPrime L (W₁.toAffine.map ι).FunctionField
    (CoordinateRing.pointPlace heq)).valuation
  set w := FunctionField.map W₁.toAffine ι
  set c := algebraMap L (W₁.toAffine.map ι).FunctionField
  set r' : L := algebraMap W₁.toAffine.CoordinateRing L r
  set s' : L := algebraMap W₁.toAffine.CoordinateRing L s
  have hr := valuation_genericPoint_place_functionFieldMap_sub_lt_one_of_mem_adjoin heq
    (algebraMap_mem_adjoin_genericX_genericY W₁.toAffine r)
  have hs := valuation_genericPoint_place_functionFieldMap_sub_lt_one_of_mem_adjoin heq
    (algebraMap_mem_adjoin_genericX_genericY W₁.toAffine s)
  have hs0 : s' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs_mem
  have hcs : v (c s') = 1 := Valuation.IsTrivialOn.eq_one (v := v) s' hs0
  have hws : v (w s') = 1 := by
    have hsplit : w s' = (w s' - c s') + c s' := by ring
    rw [hsplit, v.map_add_eq_of_lt_right (hs.2.trans_eq hcs.symm), hcs]
  have hws0 : w s' ≠ 0 := fun h ↦ by simp [h] at hws
  have hcs0 : c s' ≠ 0 := (map_ne_zero_iff c c.injective).mpr hs0
  have hquot : w (r' / s') - c (r' / s') =
      ((w r' - c r') * c s' - c r' * (w s' - c s')) / (w s' * c s') := by
    rw [map_div₀, map_div₀]; field_simp [hws0, hcs0]; ring
  rw [hquot, map_div₀, Valuation.map_mul, hws, hcs, mul_one, div_one]
  refine (v.map_sub _ _).trans_lt (max_lt ?_ ?_)
  · rw [Valuation.map_mul, hcs, mul_one]; exact hr.2
  · rw [Valuation.map_mul]
    exact Right.mul_lt_one_of_le_of_lt
      (Valuation.IsTrivialOn.valuation_algebraMap_le_one v r') hs.2

/-- Base-changing a morphism `h : Hom W₁ W₂` to `F(W₁)` and applying `pointMap` to
`W₁.genericPoint` yields `h.tautologicalPoint`. -/
private theorem pointMap_map_algebraMap_genericPoint [W₁.IsElliptic] [W₂.IsElliptic]
    [DecidableEq W₁.toAffine.FunctionField] (h : Hom W₁.toAffine W₂.toAffine) :
    (h.map (algebraMap K W₁.toAffine.FunctionField)).pointMap
        (W₁.toAffine.genericPoint :
          (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).Point) =
      (h.tautologicalPoint :
        (W₂.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).Point) := by
  let P : (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).Point :=
    W₁.toAffine.genericPoint
  have hns : (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).Nonsingular
      W₁.toAffine.genericX W₁.toAffine.genericY := nonsingular_genericX_genericY W₁.toAffine
  have hP : P = Point.some W₁.toAffine.genericX W₁.toAffine.genericY hns :=
    genericPoint_eq_some W₁.toAffine
  rcases Hom.eq_zero_or_exists_ofIsogeny h with rfl | ⟨φ, rfl⟩
  · have h0 : ((0 : Hom W₁.toAffine W₂.toAffine).map
        (algebraMap K W₁.toAffine.FunctionField)).pointMap P = 0 := by
      rw [Hom.zero_map, Hom.zero_pointMap]
    exact h0.trans Hom.tautologicalPoint_zero.symm
  let Q : (W₂.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).Point :=
    φ.pullback.tautologicalPoint
  have hQ0 : Q ≠ 0 := CoordinatePullback.tautologicalPoint_ne_zero φ.pullback
  have hφ : ((Hom.ofIsogeny φ).map (algebraMap K W₁.toAffine.FunctionField)).pointMap P = Q := by
    rw [Hom.ofIsogeny_map, Hom.pointMap_eq_iff, Hom.tautologicalPoint_ofIsogeny,
      ← Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero (φ.map _).pullback),
      ← Point.some_coords hQ0, hP, coe_pointEquivDegreeOnePlace_some,
      Point.equivBaseChangeSelf_some, some_sub_baseChange_mem_polePoints_iff]
    have hxQ : Q.xCoord = φ.pullback.tautologicalPoint.xCoord := rfl
    have hyQ : Q.yCoord = φ.pullback.tautologicalPoint.yCoord := rfl
    rw [hxQ, hyQ]
    simp only [CoordinatePullback.xCoord_tautologicalPoint,
      CoordinatePullback.yCoord_tautologicalPoint, Isogeny.map_pullback,
      CoordinatePullback.map_of_X, CoordinatePullback.map_root]
    exact ⟨valuation_genericPoint_place_functionFieldMap_sub_lt_one hns.1 _,
      valuation_genericPoint_place_functionFieldMap_sub_lt_one hns.1 _⟩
  exact hφ.trans (Hom.tautologicalPoint_ofIsogeny φ).symm

/-- Applying the base-changed `pointMap` of an isogeny `φ` to `thetaBasePoint W₁ hq hq0` produces
`thetaBasePoint W₂` at the substituted parameter `PowerSeries.subst q φ.formalSeries`. -/
private theorem pointMap_ofIsogeny_thetaBasePoint {σ : Type*} [W₁.IsElliptic] [W₂.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries σ K))]
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    {q : MvPowerSeries σ K} (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    ((Hom.ofIsogeny φ).map (algebraMap K (FractionRing (MvPowerSeries σ K)))).pointMap
      (thetaBasePoint W₁ hq hq0) =
      (thetaBasePoint W₂
        (PowerSeries.constantCoeff_subst_eq_zero hq φ.formalSeries φ.constantCoeff_formalSeries)
        (PowerSeries.subst_mvPowerSeries_ne_zero hq hq0 φ.formalSeries_ne_zero) :
        (W₂.toAffine.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).Point) := by
  have : DecidableEq W₁.toAffine.FunctionField := Classical.decEq _
  refine (congrArg _ (map_curveEval_genericPoint W₁ hq hq0).symm).trans ?_
  refine (Hom.pointMap_map_algebraMap_map (W₁ := W₁.toAffine) (W₂ := W₂.toAffine)
    (Hom.ofIsogeny φ) (curveEval W₁ hq hq0) W₁.toAffine.genericPoint).trans ?_
  refine (congrArg (Point.map (curveEval W₁ hq hq0))
    (pointMap_map_algebraMap_genericPoint (Hom.ofIsogeny φ))).trans ?_
  rw [Hom.tautologicalPoint_ofIsogeny]
  exact map_curveEval_tautologicalPoint φ hq hq0

/-- Pushing an addition `thetaBasePoint + thetaBasePoint = thetaBasePoint` on `W₁` forward along
`φ.pointMap` yields the corresponding addition on `W₂` at the `φ.formalSeries`-substituted
parameters. -/
private theorem pointMap_ofIsogeny_thetaBasePoint_add {σ : Type*} [W₁.IsElliptic] [W₂.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries σ K))]
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    {q₀ q₁ q₂ : MvPowerSeries σ K}
    (h₀ : MvPowerSeries.constantCoeff q₀ = 0) (hq₀ : q₀ ≠ 0)
    (h₁ : MvPowerSeries.constantCoeff q₁ = 0) (hq₁ : q₁ ≠ 0)
    (h₂ : MvPowerSeries.constantCoeff q₂ = 0) (hq₂ : q₂ ≠ 0)
    (hadd : thetaBasePoint W₁ h₀ hq₀ + thetaBasePoint W₁ h₁ hq₁ = thetaBasePoint W₁ h₂ hq₂) :
    thetaBasePoint W₂
        (PowerSeries.constantCoeff_subst_eq_zero h₀ φ.formalSeries φ.constantCoeff_formalSeries)
        (PowerSeries.subst_mvPowerSeries_ne_zero h₀ hq₀ φ.formalSeries_ne_zero) +
      thetaBasePoint W₂
        (PowerSeries.constantCoeff_subst_eq_zero h₁ φ.formalSeries φ.constantCoeff_formalSeries)
        (PowerSeries.subst_mvPowerSeries_ne_zero h₁ hq₁ φ.formalSeries_ne_zero) =
      thetaBasePoint W₂
        (PowerSeries.constantCoeff_subst_eq_zero h₂ φ.formalSeries φ.constantCoeff_formalSeries)
        (PowerSeries.subst_mvPowerSeries_ne_zero h₂ hq₂ φ.formalSeries_ne_zero) := by
  set fφ := (Hom.ofIsogeny φ).map (algebraMap K (FractionRing (MvPowerSeries σ K)))
  have himg : fφ.pointMap (thetaBasePoint W₁ h₀ hq₀) + fφ.pointMap (thetaBasePoint W₁ h₁ hq₁) =
      fφ.pointMap (thetaBasePoint W₁ h₂ hq₂) :=
    (Hom.pointMap_add fφ _ _).symm.trans (congrArg fφ.pointMap hadd)
  rw [pointMap_ofIsogeny_thetaBasePoint, pointMap_ofIsogeny_thetaBasePoint,
    pointMap_ofIsogeny_thetaBasePoint] at himg
  exact himg

/-- A separable isogeny induces a formal-group homomorphism: `Hom.pointMap_add` carries
`θ₁(X₀) + θ₁(X₁) = θ₁(F₁(X₀, X₁))` to `θ₂(χ(X₀)) + θ₂(χ(X₁)) = θ₂(χ(F₁(X₀, X₁)))`, and
the compositional inverse of `χ.formalSeries` separates `χ(X₀)` from `χ(X₁)`. -/
private theorem formalSeries_hom_of_isSeparable [W₂.IsElliptic]
    (χ : Isogeny W₁.toAffine W₂.toAffine)
    (hsep : Algebra.IsSeparable χ.fieldPullback.fieldRange W₁.toAffine.FunctionField) :
    PowerSeries.subst (formalGroup W₁).toPowerSeries χ.formalSeries =
      MvPowerSeries.subst (fun i ↦ χ.formalSeries.toMvPowerSeries i)
        (formalGroup W₂).toPowerSeries := by
  have : W₁.IsElliptic := χ.isElliptic
  classical
  -- Step 1: form `θ₁(X₀) + θ₁(X₁) = θ₁(F₁(X₀, X₁))` on `W₁` and push forward along `χ`.
  have hu : IsUnit (PowerSeries.coeff 1 χ.formalSeries) :=
    ((χ.isSeparable_iff_coeff_one_formalSeries_ne_zero).mp hsep).isUnit
  set q₀ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0
  set q₁ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1
  have hq₀c : MvPowerSeries.constantCoeff q₀ = 0 := constantCoeff_X 0
  have hq₁c : MvPowerSeries.constantCoeff q₁ = 0 := constantCoeff_X 1
  have hq₀0 : q₀ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hq₁0 : q₁ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hadd₁ := thetaBasePoint_add_of_subst_separates W₁
    (hasSubst_coordSpecialize (O := K) (0 : Fin 2)) hq₀c hq₁c hq₀0 hq₁0
    (subst_coordSpecialize_X_self (O := K) (0 : Fin 2))
    (subst_coordSpecialize_X_of_ne (O := K) (i := (0 : Fin 2)) (j := 1) (by decide))
  have hxy : MvPowerSeries.subst ![q₀, q₁] (formalGroup W₁).toPowerSeries =
      (formalGroup W₁).toPowerSeries := by
    trans MvPowerSeries.subst MvPowerSeries.X (formalGroup W₁).toPowerSeries
    · congr 1; funext i; fin_cases i <;> rfl
    · exact congrFun MvPowerSeries.subst_self _
  have himg := pointMap_ofIsogeny_thetaBasePoint_add χ hq₀c hq₀0 hq₁c hq₁0 _ _ hadd₁
  -- Step 2: separate `χ(X₀)` from `χ(X₁)` on `W₂` via `(X₀, X₁) ↦ (χ⁻¹(X), 0)`.
  set inv := χ.formalSeries.substInvOfIsUnit hu
  have hinv_c : PowerSeries.constantCoeff inv = 0 := by simp [inv]
  set g : Fin 2 → MvPowerSeries Unit K := ![inv, 0]
  have hg : MvPowerSeries.HasSubst g :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ by
      fin_cases i; exacts [hinv_c, map_zero _]
  have hg_q₀ : MvPowerSeries.subst g q₀ = inv := by simp [q₀, g, MvPowerSeries.subst_X hg]
  have hg_q₁ : MvPowerSeries.subst g q₁ = 0 := by simp [q₁, g, MvPowerSeries.subst_X hg]
  have hg₀ : MvPowerSeries.subst g (PowerSeries.subst q₀ χ.formalSeries) = PowerSeries.X := by
    rw [subst_powerSeriesSubst hg (.of_constantCoeff_zero hq₀c), hg_q₀]
    exact χ.formalSeries.subst_substInvOfIsUnit_right χ.constantCoeff_formalSeries hu
  have hg₁ : MvPowerSeries.subst g (PowerSeries.subst q₁ χ.formalSeries) = 0 := by
    rw [subst_powerSeriesSubst hg (.of_constantCoeff_zero hq₁c), hg_q₁,
      PowerSeries.subst_zero_of_constantCoeff_zero χ.constantCoeff_formalSeries]
  rw [thetaBasePoint_add_of_subst_separates W₂ hg _ _ _ _ hg₀ hg₁] at himg
  have hseries := (thetaBasePoint_inj W₂ _ _ _ _ himg).symm
  rw [hxy] at hseries
  refine hseries.trans ?_
  congr 1; funext i; fin_cases i <;> simp [PowerSeries.toMvPowerSeries_eq_subst, q₀, q₁]

/-- **Every isogeny of elliptic curves induces a homomorphism of their formal group laws**
(Silverman IV.4.2), in arbitrary characteristic and including inseparable isogenies. -/
noncomputable def formalGroupHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := φ.formalSeries
  zero_constantCoeff := φ.constantCoeff_formalSeries
  hom := by
    have : W₁.IsElliptic := φ.isElliptic
    obtain ⟨p, hchar⟩ := ExpChar.exists K
    rcases hchar with _ | ⟨hp⟩
    · exact formalSeries_hom_of_isSeparable φ inferInstance
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨r, χ, hsep, rfl⟩ :=
        exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
      let hχ : FormalGroupHom
          (formalGroup (W₁.map (iterateFrobenius K p r))) (formalGroup W₂) :=
        { toPowerSeries :=
            (χ : Isogeny (W₁.map (iterateFrobenius K p r)).toAffine W₂.toAffine).formalSeries
          zero_constantCoeff :=
            (χ : Isogeny (W₁.map (iterateFrobenius K p r)).toAffine
              W₂.toAffine).constantCoeff_formalSeries
          hom := formalSeries_hom_of_isSeparable χ hsep }
      let hF : FormalGroupHom (formalGroup W₁)
          (formalGroup (W₁.map (iterateFrobenius K p r))) :=
        { toPowerSeries := PowerSeries.X ^ p ^ r
          zero_constantCoeff := by simp [hp.ne_zero]
          hom := by
            rw [W₁.map_formalGroup]
            simpa only [FormalGroup.iterateFrobeniusHom_toPowerSeries] using
              ((formalGroup W₁).iterateFrobeniusHom p r).hom }
      have hcomp := (hχ.comp hF).hom
      have hser : (hχ.comp hF).toPowerSeries =
          (χ.comp (iterateRelativeFrobeniusIsogeny p W₁.toAffine r)).formalSeries := by
        rw [FormalGroupHom.comp_toPowerSeries, formalSeries_comp,
          formalSeries_iterateRelativeFrobeniusIsogeny]
      rwa [hser] at hcomp

/-- The underlying power series of `φ.formalGroupHom` is `φ.formalSeries`. -/
@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries :=
  (rfl)

/-- Sending an isogeny to its bundled `FormalGroupHom` is injective. -/
theorem formalGroupHom_injective [W₂.IsElliptic] :
    Function.Injective (formalGroupHom (W₁ := W₁) (W₂ := W₂)) := fun _ _ h ↦
  formalSeries_injective (congrArg FormalGroupHom.toPowerSeries h)

/-- The identity isogeny induces the identity homomorphism on `formalGroup W`. -/
@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext : 1; simp

/-- Composition of isogenies induces composition of `FormalGroupHom`s. -/
@[simp]
theorem formalGroupHom_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (ψ : Isogeny W₂.toAffine W₃.toAffine) (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).formalGroupHom = ψ.formalGroupHom.comp φ.formalGroupHom := by
  ext : 1; simp

/-- The negation isogeny induces `[-1]` on `formalGroup W`. -/
@[simp]
theorem formalGroupHom_negIsogeny (W : WeierstrassCurve K) [W.IsElliptic] :
    (negIsogeny W.toAffine).formalGroupHom = (formalGroup W).zsmulHom (-1) := by
  ext : 1; simp

/-- Multiplication-by-`n` induces `[n]` (`zsmulHom n`) on `formalGroup W`. -/
@[simp]
theorem formalGroupHom_mulByIntIsogeny (W : WeierstrassCurve K) [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalGroupHom = (formalGroup W).zsmulHom n := by
  ext : 1; simp

end FormalGroupHom

end TauCeti.Isogeny

end
