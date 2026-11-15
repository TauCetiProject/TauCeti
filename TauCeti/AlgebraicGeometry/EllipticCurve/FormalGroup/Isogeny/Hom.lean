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
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
public import TauCeti.RingTheory.FormalGroup.ZSMul
import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
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
import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# Morphisms of elliptic curves induce homomorphisms of formal group laws

Expanding a morphism `f : Hom W₁ W₂` of elliptic curves in the local parameter `z = -x/y` at
infinity assigns to `f` a power series `f.formalSeries ∈ K⟦X⟧` with zero constant coefficient (`0`
for the zero morphism, `Isogeny.formalSeries` for an isogeny). Following Silverman, *The Arithmetic
of Elliptic Curves*, IV.4 and IV.7, this file establishes:

1. **Additivity in the morphism** (`TauCeti.Isogeny.Hom.formalPointAddHom`): `f ↦ f.formalPoint`
   is an injective additive group homomorphism
   `Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit`. In particular, for `[n] : W → W`
   with `ψ_n ≠ 0`, `[n].formalSeries = (formalGroup W).zsmulSeries n`
   (`TauCeti.Isogeny.formalSeries_mulByIntIsogeny`), so `[n]_Ê` has order equal to the inseparable
   degree of `[n]` (`WeierstrassCurve.order_zsmulSeries_formalGroup`).
2. **Compatibility with the formal group laws** (`TauCeti.Isogeny.formalGroupHom` and
   `TauCeti.Isogeny.Hom.formalGroupHom`): every isogeny `φ : W₁ → W₂` and every morphism
   `f : Hom W₁ W₂` induces a bundled homomorphism `FormalGroupHom (formalGroup W₁) (formalGroup W₂)`
   with underlying power series `formalSeries`, functorially with respect to zero, identity,
   composition, and integer multiples.

Both proofs evaluate rational functions on the curve at power-series parameters in the fraction
field of `MvPowerSeries (Fin 2) K` via `TauCeti.LaurentSeries.mvSubstAlgHom`, matching `Point.map`
on generic and tautological points with the chord parametrization `WeierstrassCurve.thetaPoint`.

## Main definitions

* `TauCeti.Isogeny.Hom.formalSeries`: the formal series at infinity of a morphism in `Hom W₁ W₂`.
* `TauCeti.Isogeny.Hom.formalPoint`: the formal-group point in `(formalGroup W₂).Point Unit`
  attached to a morphism.
* `TauCeti.Isogeny.Hom.formalPointAddHom`: `Hom.formalPoint` bundled as an injective additive
  homomorphism when `W₂` is elliptic.
* `TauCeti.Isogeny.formalGroupHom` and `TauCeti.Isogeny.Hom.formalGroupHom`: the bundled
  `FormalGroupHom (formalGroup W₁) (formalGroup W₂)` induced by an isogeny or morphism when `W₂`
  is elliptic.

## Main results

* `TauCeti.Isogeny.Hom.formalSeries_injective`: a morphism in `Hom W₁ W₂` is determined by its
  formal series.
* `TauCeti.Isogeny.formalSeries_negIsogeny`: `[-1].formalSeries = (formalGroup W).addInvX`.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny` and
  `TauCeti.Isogeny.formalSeries_mulByIntIsogeny_natCast`: `[n].formalSeries =
  (formalGroup W).zsmulSeries n` (and `nsmulSeries n` for natural `n`).
* `WeierstrassCurve.order_zsmulSeries_formalGroup` and
  `WeierstrassCurve.order_nsmulSeries_formalGroup`: the order of `[n]_Ê` equals the inseparable
  degree of `[n]` for `n ≠ 0`.
* `TauCeti.Isogeny.formalGroupHom_id`, `TauCeti.Isogeny.formalGroupHom_comp`,
  `TauCeti.Isogeny.formalGroupHom_negIsogeny`, `TauCeti.Isogeny.formalGroupHom_mulByIntIsogeny`,
  and their `TauCeti.Isogeny.Hom` counterparts (`Hom.formalGroupHom_zero`,
  `Hom.formalGroupHom_ofIsogeny`, `Hom.formalGroupHom_id`, `Hom.formalGroupHom_comp`,
  `Hom.formalGroupHom_zsmul`).

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4 and IV.7.
-/

public section

open HahnSeries MvPowerSeries WeierstrassCurve WeierstrassCurve.Affine
open scoped LaurentSeries PowerSeries nonZeroDivisors

namespace TauCeti.Isogeny

section Basic

variable {K : Type*} [Field K]

/-- **The formal series of the negation isogeny is the geometric formal inverse** `W.formalInverse`,
with no ellipticity assumption on `W`. -/
theorem formalSeries_negIsogeny_eq_formalInverse (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).formalSeries = W.formalInverse := by
  apply (formalSeries_eq_iff _ _).mpr
  set q : K⸨X⸩ := ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)
  set w : K⸨X⸩ := (formalW W : K⸨X⸩)
  have hw0 : w ≠ 0 := (map_ne_zero_iff _ ofPowerSeries_injective).mpr W.formalW_ne_zero
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
  (TauCeti.LaurentSeries.mvSubstAlgHom (FractionRing (MvPowerSeries σ K)) hq hq0).comp
    W.functionFieldLaurentExpansion

private theorem curveEval_comp_fieldPullback {W₁ W₂ : WeierstrassCurve K}
    (φ : Isogeny W₁.toAffine W₂.toAffine) {q : MvPowerSeries σ K}
    (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    (curveEval W₁ hq hq0).comp φ.fieldPullback =
      curveEval W₂
        (PowerSeries.constantCoeff_subst_eq_zero hq φ.formalSeries φ.constantCoeff_formalSeries)
        (PowerSeries.subst_ne_zero hq hq0 φ.formalSeries_ne_zero) := by
  refine AlgHom.ext fun z ↦ ?_
  simp only [curveEval, AlgHom.comp_apply, φ.functionFieldLaurentExpansion_fieldPullback,
    TauCeti.LaurentSeries.mvSubstAlgHom_comp_substAlgHom_apply]

private theorem fracCurve_eq_baseChange (W : WeierstrassCurve K) :
    fracCurve W σ (FractionRing (MvPowerSeries σ K)) =
      W⁄(FractionRing (MvPowerSeries σ K)) := by
  rw [fracCurve_def,
    ← IsScalarTower.algebraMap_eq K (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))]
  rfl

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

/-- Transport `thetaPoint` along `fracCurve W σ M = W⁄M`. -/
private noncomputable def thetaBasePoint (W : WeierstrassCurve K) [W.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries σ K))]
    {q : MvPowerSeries σ K} (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    (W.toAffine⁄(FractionRing (MvPowerSeries σ K))).Point :=
  AddEquiv.cast
    (M := fun V : WeierstrassCurve (FractionRing (MvPowerSeries σ K)) ↦ V.toAffine.Point)
    (fracCurve_eq_baseChange (σ := σ) W)
    (W.thetaPoint (W.fracCurve_Δ_ne_zero W.toAffine.isUnit_Δ.ne_zero) hq hq0)

private theorem thetaBasePoint_inj (W : WeierstrassCurve K) [W.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries σ K))]
    {q₁ q₂ : MvPowerSeries σ K}
    (h₁ : MvPowerSeries.constantCoeff q₁ = 0) (h₂ : MvPowerSeries.constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (h : thetaBasePoint W h₁ hq₁0 = thetaBasePoint W h₂ hq₂0) : q₁ = q₂ :=
  W.thetaPoint_inj _ h₁ h₂ hq₁0 hq₂0 ((AddEquiv.cast _).injective h)

private theorem subst_pairSubstitution_formalAdd_eq (W : WeierstrassCurve K)
    {a b : MvPowerSeries σ K}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst (pairSubstitution a b) (formalAdd W) =
      MvPowerSeries.subst ![a, b] (formalGroup W).toPowerSeries := by
  rw [formalGroup_toPowerSeries, MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _
    (MvPowerSeries.hasSubst_finTwo (.of_constantCoeff_zero ha) (.of_constantCoeff_zero hb))]
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
    W.thetaPoint_eq_some _ hq hq0 (thetaPoint_nonsingular W hq hq0), AddEquiv.cast_apply,
    Point.cast_some (fracCurve_eq_baseChange W), Point.some.injEq]
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
        (PowerSeries.subst_ne_zero hq hq0 φ.formalSeries_ne_zero) := by
  rw [tautologicalPoint_eq_map_genericPoint, Point.map_map, curveEval_comp_fieldPullback,
    map_curveEval_genericPoint]

/-- Auxiliary parameter separation for three nonzero series `f₁, f₂, f₃` with zero constant term
whose `thetaBasePoint`s at `X₀ ∈ MvPowerSeries (Fin 2) K` satisfy
`θ(f₃(X₀)) = θ(f₁(X₀)) + θ(f₂(X₀))`: translating on the left by `θ(X₁)` separates all three chord
additions under `coordSpecialize 1` (`X₁ ↦ X`, `X₀ ↦ 0`), and cancelling `X₁` in
`(formalGroup W).Point (Fin 2)` followed by `(X₀, X₁) ↦ (X, 0)` yields `f₃ = F(f₁, f₂)`. -/
private theorem eq_subst_formalGroup_of_thetaBasePoint_add (W : WeierstrassCurve K) [W.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries (Fin 2) K))]
    {f₁ f₂ f₃ : K⟦X⟧}
    (hf₁ : PowerSeries.constantCoeff f₁ = 0) (hf₁0 : f₁ ≠ 0)
    (hf₂ : PowerSeries.constantCoeff f₂ = 0) (hf₂0 : f₂ ≠ 0)
    (hf₃ : PowerSeries.constantCoeff f₃ = 0) (hf₃0 : f₃ ≠ 0)
    (hpts :
      thetaBasePoint W
        (PowerSeries.constantCoeff_subst_eq_zero
          (constantCoeff_X (0 : Fin 2)) f₃ hf₃)
        (PowerSeries.subst_ne_zero (constantCoeff_X (0 : Fin 2))
          (nonZeroDivisors.ne_zero X_mem_nonZeroDivisors) hf₃0) =
      thetaBasePoint W
        (PowerSeries.constantCoeff_subst_eq_zero
          (constantCoeff_X (0 : Fin 2)) f₁ hf₁)
        (PowerSeries.subst_ne_zero (constantCoeff_X (0 : Fin 2))
          (nonZeroDivisors.ne_zero X_mem_nonZeroDivisors) hf₁0) +
      thetaBasePoint W
        (PowerSeries.constantCoeff_subst_eq_zero
          (constantCoeff_X (0 : Fin 2)) f₂ hf₂)
        (PowerSeries.subst_ne_zero (constantCoeff_X (0 : Fin 2))
          (nonZeroDivisors.ne_zero X_mem_nonZeroDivisors) hf₂0)) :
    f₃ = MvPowerSeries.subst ![f₁, f₂] (formalGroup W).toPowerSeries := by
  set q₀ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0
  set q₁ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1
  have hq₀c : MvPowerSeries.constantCoeff q₀ = 0 := constantCoeff_X 0
  have hq₁c : MvPowerSeries.constantCoeff q₁ = 0 := constantCoeff_X 1
  have hq₀0 : q₀ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hq₁0 : q₁ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hf₁c := PowerSeries.constantCoeff_subst_eq_zero hq₀c f₁ hf₁
  have hf₂c := PowerSeries.constantCoeff_subst_eq_zero hq₀c f₂ hf₂
  have hf₃c := PowerSeries.constantCoeff_subst_eq_zero hq₀c f₃ hf₃
  have hpts' : thetaBasePoint W hq₁c hq₁0 +
      thetaBasePoint W hf₃c (PowerSeries.subst_ne_zero hq₀c hq₀0 hf₃0) =
      (thetaBasePoint W hq₁c hq₁0 +
        thetaBasePoint W hf₁c (PowerSeries.subst_ne_zero hq₀c hq₀0 hf₁0)) +
      thetaBasePoint W hf₂c (PowerSeries.subst_ne_zero hq₀c hq₀0 hf₂0) := by
    rw [hpts, ← add_assoc]
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
  have hg_F₁ : MvPowerSeries.subst g
      (MvPowerSeries.subst ![q₁, PowerSeries.subst q₀ f₁] (formalGroup W).toPowerSeries) =
      PowerSeries.X := by
    have hsub_pair := MvPowerSeries.hasSubst_finTwo (.of_constantCoeff_zero hq₁c)
      (.of_constantCoeff_zero hf₁c)
    have hg_pair : (fun i : Fin 2 ↦
        MvPowerSeries.subst g (![q₁, PowerSeries.subst q₀ f₁] i)) =
        ![PowerSeries.X, 0] := funext fun i ↦ by
      fin_cases i; exacts [hg_q₁, hg_subst _ hf₁]
    rw [MvPowerSeries.subst_comp_subst_apply hsub_pair hg, hg_pair]
    exact (formalGroup W).Xzero_eq_X
  rw [thetaBasePoint_add_of_subst_separates W hg hq₁c hf₃c _ _ hg_q₁ (hg_subst _ hf₃),
    thetaBasePoint_add_of_subst_separates W hg hq₁c hf₁c _ _ hg_q₁ (hg_subst _ hf₁),
    thetaBasePoint_add_of_subst_separates W hg _ hf₂c _ _ hg_F₁ (hg_subst _ hf₂)] at hpts'
  have hseries := thetaBasePoint_inj W _ _ _ _ hpts'
  let p₁ : (formalGroup W).Point (Fin 2) := ⟨q₁, .of_constantCoeff_zero hq₁c⟩
  let pf₁ : (formalGroup W).Point (Fin 2) := ⟨PowerSeries.subst q₀ f₁, .of_constantCoeff_zero hf₁c⟩
  let pf₂ : (formalGroup W).Point (Fin 2) := ⟨PowerSeries.subst q₀ f₂, .of_constantCoeff_zero hf₂c⟩
  let pf₃ : (formalGroup W).Point (Fin 2) := ⟨PowerSeries.subst q₀ f₃, .of_constantCoeff_zero hf₃c⟩
  have hp : p₁ + pf₃ = p₁ + (pf₁ + pf₂) := by rw [← add_assoc]; exact Subtype.ext hseries
  have hcancel : pf₃.val = (pf₁ + pf₂).val :=
    congrArg (fun p : (formalGroup W).Point (Fin 2) ↦ p.val) (add_left_cancel hp)
  rw [FormalGroup.add_apply] at hcancel
  let s₀ : Fin 2 → PowerSeries K := ![PowerSeries.X, 0]
  have hs₀ : MvPowerSeries.HasSubst s₀ := MvPowerSeries.HasSubst.X_zero
  have hs₀_subst (f : K⟦X⟧) : MvPowerSeries.subst s₀ (PowerSeries.subst q₀ f) = f := by
    rw [subst_powerSeriesSubst hs₀ (.of_constantCoeff_zero hq₀c), MvPowerSeries.subst_X hs₀]
    dsimp only [s₀]
    rw [Matrix.cons_val_zero, PowerSeries.X_subst]
  have hspec := congrArg (MvPowerSeries.subst s₀) hcancel
  rw [hs₀_subst f₃, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_finTwo (.of_constantCoeff_zero hf₁c) (.of_constantCoeff_zero hf₂c))
    hs₀] at hspec
  refine hspec.trans ?_
  congr 1; funext i; fin_cases i <;> exact hs₀_subst _

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

/-- A morphism has zero formal-group point if and only if it is the zero morphism. -/
@[simp]
theorem formalPoint_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalPoint = 0 ↔ f = 0 := by
  rw [← formalPoint_zero, formalPoint_inj]

/-- The formal-group point of `-f` is `-f.formalPoint`. -/
@[simp]
theorem formalPoint_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalPoint = -f.formalPoint :=
  Subtype.ext (formalSeries_neg f)

end Carrier

section Additive

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

private theorem formalPoint_of_ofIsogeny_add_ofIsogeny
    {φ ψ χ : Isogeny W₁.toAffine W₂.toAffine}
    (hadd : ofIsogeny φ + ofIsogeny ψ = ofIsogeny χ) :
    χ.formalSeries =
      MvPowerSeries.subst ![φ.formalSeries, ψ.formalSeries] (formalGroup W₂).toPowerSeries := by
  classical
  have htaut : χ.pullback.tautologicalPoint =
      φ.pullback.tautologicalPoint + ψ.pullback.tautologicalPoint := by
    simpa only [tautologicalPoint_add, tautologicalPoint_ofIsogeny] using
      congrArg tautologicalPoint hadd.symm
  have hpts := congrArg
    (Point.map (curveEval W₁ (constantCoeff_X (0 : Fin 2))
      (nonZeroDivisors.ne_zero X_mem_nonZeroDivisors))) htaut
  simp only [_root_.map_add, map_curveEval_tautologicalPoint] at hpts
  exact eq_subst_formalGroup_of_thetaBasePoint_add W₂
    φ.constantCoeff_formalSeries φ.formalSeries_ne_zero
    ψ.constantCoeff_formalSeries ψ.formalSeries_ne_zero
    χ.constantCoeff_formalSeries χ.formalSeries_ne_zero hpts

/-- **Silverman IV.4 (additivity):** the formal-group point of `f + g` is the formal-group sum of
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
the formal group points `(formalGroup W₂).Point Unit` (Silverman IV.4). -/
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

/-- **Silverman IV.4 (series form):** the formal series of `f + g` is obtained by substituting
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
series of its formal group law** (Silverman IV.4). -/
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

/-- **The order of `[n]_Ê` is the inseparable degree of `[n]`**: for any elliptic curve over a
field and any nonzero integer `n`, the formal `n`-multiplication series has order equal to the
inseparable degree of the multiplication-by-`n` isogeny. -/
theorem _root_.WeierstrassCurve.order_zsmulSeries_formalGroup {n : ℤ} (hn : n ≠ 0) :
    ((formalGroup W).zsmulSeries n).order =
      ((mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree : ℕ∞) := by
  rw [← formalSeries_mulByIntIsogeny, order_formalSeries_eq_inseparableDegree]

/-- **The order of `[n]_Ê` (`n : ℕ`) is the inseparable degree of `[n]`**, for `n ≠ 0`. -/
theorem _root_.WeierstrassCurve.order_nsmulSeries_formalGroup {n : ℕ} (hn : n ≠ 0) :
    ((formalGroup W).nsmulSeries n).order =
      ((mulByIntIsogenyOfNeZero W.toAffine (Nat.cast_ne_zero.mpr hn)).inseparableDegree : ℕ∞) := by
  rw [← FormalGroup.zsmulSeries_natCast, W.order_zsmulSeries_formalGroup]

end MulByInt

section FormalGroupHom

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

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
        (PowerSeries.subst_ne_zero hq hq0 φ.formalSeries_ne_zero) :
        (W₂.toAffine.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).Point) := by
  refine (congrArg _ (map_curveEval_genericPoint W₁ hq hq0).symm).trans ?_
  refine (Hom.pointMap_map_algebraMap_map (W₁ := W₁.toAffine) (W₂ := W₂.toAffine)
    (Hom.ofIsogeny φ) (curveEval W₁ hq hq0) W₁.toAffine.genericPoint).trans ?_
  refine (congrArg (Point.map (curveEval W₁ hq hq0))
    (Hom.pointMap_map_algebraMap_genericPoint (Hom.ofIsogeny φ))).trans ?_
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
        (PowerSeries.subst_ne_zero h₀ hq₀ φ.formalSeries_ne_zero) +
      thetaBasePoint W₂
        (PowerSeries.constantCoeff_subst_eq_zero h₁ φ.formalSeries φ.constantCoeff_formalSeries)
        (PowerSeries.subst_ne_zero h₁ hq₁ φ.formalSeries_ne_zero) =
      thetaBasePoint W₂
        (PowerSeries.constantCoeff_subst_eq_zero h₂ φ.formalSeries φ.constantCoeff_formalSeries)
        (PowerSeries.subst_ne_zero h₂ hq₂ φ.formalSeries_ne_zero) := by
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
    rw [MvPowerSeries.finTwo_X_eq_X]
    exact congrFun MvPowerSeries.subst_self _
  have himg := pointMap_ofIsogeny_thetaBasePoint_add χ hq₀c hq₀0 hq₁c hq₁0 _ _ hadd₁
  -- Step 2: separate `χ(X₀)` from `χ(X₁)` on `W₂` via `(X₀, X₁) ↦ (χ⁻¹(X), 0)`.
  set inv := χ.formalSeries.substInvOfIsUnit hu
  have hinv_c : PowerSeries.constantCoeff inv = 0 := by simp [inv]
  set g : Fin 2 → MvPowerSeries Unit K := ![inv, 0]
  have hg : MvPowerSeries.HasSubst g :=
    MvPowerSeries.hasSubst_finTwo (.of_constantCoeff_zero' hinv_c) .zero
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
(Silverman IV.4 and IV.7), in arbitrary characteristic and including inseparable isogenies. -/
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
      let hcomp := (hχ.ofSourceEq (W₁.map_formalGroup (iterateFrobenius K p r))).comp
        ((formalGroup W₁).iterateFrobeniusHom p r)
      have hser : hcomp.toPowerSeries =
          (χ.comp (iterateRelativeFrobeniusIsogeny p W₁.toAffine r)).formalSeries := by
        simp [hcomp, hχ, formalSeries_iterateRelativeFrobeniusIsogeny]
      simpa only [hser] using hcomp.hom

/-- The underlying power series of `φ.formalGroupHom` is `φ.formalSeries`. -/
@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries :=
  (rfl)

/-- Sending an isogeny to its bundled `FormalGroupHom` is injective. -/
theorem formalGroupHom_injective [W₂.IsElliptic] :
    Function.Injective (formalGroupHom (W₁ := W₁) (W₂ := W₂)) := fun _ _ h ↦
  formalSeries_injective (congrArg FormalGroupHom.toPowerSeries h)

/-- Two isogenies induce the same `FormalGroupHom` if and only if they are equal. -/
@[simp]
theorem formalGroupHom_inj [W₂.IsElliptic] {φ ψ : Isogeny W₁.toAffine W₂.toAffine} :
    φ.formalGroupHom = ψ.formalGroupHom ↔ φ = ψ :=
  formalGroupHom_injective.eq_iff

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

/-- Evaluating `φ.formalGroupHom` on the formal-group point of a morphism `f` gives the
formal-group point of `(Hom.ofIsogeny φ).comp f`. -/
@[simp]
theorem formalGroupHom_applyPoint_formalPoint {W₀ : WeierstrassCurve K} [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (f : Hom W₀.toAffine W₁.toAffine) :
    φ.formalGroupHom.applyPoint f.formalPoint = ((Hom.ofIsogeny φ).comp f).formalPoint := by
  apply Subtype.ext
  simp

/-- Evaluating `φ.formalGroupHom` at the tautological point gives
`(Hom.ofIsogeny φ).formalPoint`. -/
@[simp]
theorem formalGroupHom_applyPoint_tautologicalPoint [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.applyPoint (formalGroup W₁).tautologicalPoint =
      (Hom.ofIsogeny φ).formalPoint := by
  rw [← Hom.formalPoint_id, formalGroupHom_applyPoint_formalPoint, Hom.comp_id]

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

namespace Hom

/-- **Every morphism `f : Hom W₁ W₂` of elliptic curves induces a homomorphism of their formal
group laws** (Silverman IV.4 and IV.7), with underlying power series `f.formalSeries`. -/
noncomputable def formalGroupHom [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := f.formalSeries
  zero_constantCoeff := f.constantCoeff_formalSeries
  hom := by
    rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
    · simpa only [formalSeries_zero, FormalGroupHom.zero_toPowerSeries] using
        (0 : FormalGroupHom (formalGroup W₁) (formalGroup W₂)).hom
    · simpa only [formalSeries_ofIsogeny, Isogeny.formalGroupHom_toPowerSeries] using
        φ.formalGroupHom.hom

/-- The underlying power series of `f.formalGroupHom` is `f.formalSeries`. -/
@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalGroupHom.toPowerSeries = f.formalSeries :=
  (rfl)

/-- The zero morphism induces the zero `FormalGroupHom`. -/
@[simp]
theorem formalGroupHom_zero [W₂.IsElliptic] :
    (0 : Hom W₁.toAffine W₂.toAffine).formalGroupHom = 0 := by
  ext : 1; simp

/-- On `ofIsogeny φ`, `Hom.formalGroupHom` agrees with `Isogeny.formalGroupHom`. -/
@[simp]
theorem formalGroupHom_ofIsogeny [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalGroupHom = φ.formalGroupHom := by
  ext : 1; simp

/-- The identity morphism induces the identity homomorphism on `formalGroup W`. -/
@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext : 1; simp

/-- Composition of morphisms induces composition of `FormalGroupHom`s, including composites with
zero. -/
@[simp]
theorem formalGroupHom_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalGroupHom = g.formalGroupHom.comp f.formalGroupHom := by
  ext : 1; simp

/-- Sending a morphism in `Hom W₁ W₂` to its `FormalGroupHom` is injective. -/
theorem formalGroupHom_injective [W₂.IsElliptic] :
    Function.Injective (formalGroupHom (W₁ := W₁) (W₂ := W₂)) := fun _ _ h ↦
  formalSeries_injective (congrArg FormalGroupHom.toPowerSeries h)

/-- Two morphisms induce the same `FormalGroupHom` if and only if they are equal. -/
@[simp]
theorem formalGroupHom_inj [W₂.IsElliptic] {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalGroupHom = g.formalGroupHom ↔ f = g :=
  formalGroupHom_injective.eq_iff

/-- A morphism induces the zero `FormalGroupHom` if and only if it is the zero morphism. -/
@[simp]
theorem formalGroupHom_eq_zero_iff [W₂.IsElliptic] {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalGroupHom = 0 ↔ f = 0 := by
  rw [← formalGroupHom_zero, formalGroupHom_inj]

/-- Negating a morphism post-composes its `FormalGroupHom` with `[-1]`. -/
@[simp]
theorem formalGroupHom_neg [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalGroupHom = ((formalGroup W₂).zsmulHom (-1)).comp f.formalGroupHom := by
  ext : 1; simp

/-- Scalar multiplication by `n : ℤ` on a morphism post-composes its `FormalGroupHom` with
`(formalGroup W₂).zsmulHom n`. -/
@[simp]
theorem formalGroupHom_zsmul [W₂.IsElliptic] (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalGroupHom = ((formalGroup W₂).zsmulHom n).comp f.formalGroupHom := by
  ext : 1; simp

/-- Scalar multiplication by `n : ℕ` on a morphism post-composes its `FormalGroupHom` with
`(formalGroup W₂).zsmulHom n`. -/
@[simp]
theorem formalGroupHom_nsmul [W₂.IsElliptic] (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalGroupHom = ((formalGroup W₂).zsmulHom n).comp f.formalGroupHom := by
  ext : 1; simp

/-- Evaluating `f.formalGroupHom` on the formal-group point of `g` gives
`(f.comp g).formalPoint`. -/
@[simp]
theorem formalGroupHom_applyPoint_formalPoint {W₀ : WeierstrassCurve K} [W₂.IsElliptic]
    (f : Hom W₁.toAffine W₂.toAffine) (g : Hom W₀.toAffine W₁.toAffine) :
    f.formalGroupHom.applyPoint g.formalPoint = (f.comp g).formalPoint := by
  apply Subtype.ext
  simp

/-- Evaluating `f.formalGroupHom` at the tautological point gives `f.formalPoint`. -/
@[simp]
theorem formalGroupHom_applyPoint_tautologicalPoint [W₂.IsElliptic]
    (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalGroupHom.applyPoint (formalGroup W₁).tautologicalPoint = f.formalPoint := by
  rw [← formalPoint_id, formalGroupHom_applyPoint_formalPoint, comp_id]

end Hom

end FormalGroupHom

end TauCeti.Isogeny

end
