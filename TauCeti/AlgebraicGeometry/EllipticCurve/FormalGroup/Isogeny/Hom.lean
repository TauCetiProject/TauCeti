/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny.Order
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.RingTheory.FormalGroup.Height.Basic
public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Unit
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors
import TauCeti.RingTheory.MvPowerSeries.Rename
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Formal-group homomorphisms and additivity of formal power series of isogenies

An isogeny `φ : W₁ → W₂` of elliptic curves over a field `K` expands at infinity to a formal power
series `φ.formalSeries : K⟦X⟧` in the local parameter `z = -x / y`. Extending by `0` at the zero
morphism defines `TauCeti.Isogeny.Hom.formalSeries` on the additive group `Hom W₁ W₂`.

This file proves the two fundamental compatibilities between morphisms of elliptic curves and their
formal group laws (Silverman IV.4.2):

1. **Additivity in the morphism** (`TauCeti.Isogeny.Hom.formalSeries_add`): for `f, g : Hom W₁ W₂`,
   `(f + g).formalSeries = F_{W₂}(f.formalSeries, g.formalSeries)`. Bundled into the additive group
   of power-series points `(formalGroup W₂).Point Unit`, this gives
   `TauCeti.Isogeny.Hom.formalSeriesAddHom` and identifies the formal series of `[n] : W → W` with
   `(formalGroup W).zsmulSeries n` for every `n : ℤ`
   (`TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`).
2. **Formal-group homomorphism** (`TauCeti.Isogeny.formalGroupHom`): every isogeny `φ : W₁ → W₂`
   induces a nonzero homomorphism of formal group laws `formalGroup W₁ → formalGroup W₂` with
   underlying series `φ.formalSeries`. Consequently, isogenous elliptic curves have formal group
   laws of the same height (`TauCeti.Isogeny.height_formalGroup_eq`), and a separable isogeny
   induces an isomorphism of formal group laws (`TauCeti.Isogeny.formalGroupIso`) and a coordinate
   change `φ.formalCoordinate • formalGroup W₁ = formalGroup W₂`
   (`TauCeti.Isogeny.formalCoordinate_smul_formalGroup`).

Both statements are proved by passing to the fraction field `KK` of the two-variable power-series
ring `MvPowerSeries (Fin 2) K`, where a nonzero parameter `q` with zero constant coefficient
defines an embedding `K(W) →ₐ[K] KK` sending the generic point of `W` to `W.thetaPoint`, and
comparing chord addition of `thetaPoint`s with the group law of `Hom` and its action on points.

## Main definitions

* `TauCeti.Isogeny.Hom.formalSeries` and `TauCeti.Isogeny.Hom.formalSeriesAddHom`: the formal power
  series of a morphism in `Hom W₁ W₂`, and the additive homomorphism to `(formalGroup W₂).Point`.
* `TauCeti.Isogeny.formalGroupHom`: the homomorphism `formalGroup W₁ → formalGroup W₂` induced by
  an isogeny `φ : W₁ → W₂`.
* `TauCeti.Isogeny.formalCoordinate` and `TauCeti.Isogeny.formalGroupIso`: the formal coordinate
  and formal-group isomorphism induced by a separable isogeny.

## Main results

* `TauCeti.Isogeny.Hom.formalSeries_add`, `TauCeti.Isogeny.Hom.formalSeries_neg`,
  `TauCeti.Isogeny.Hom.formalSeries_sub`, `TauCeti.Isogeny.Hom.formalSeries_nsmul` and
  `TauCeti.Isogeny.Hom.formalSeries_zsmul`: formal-group compatibility of `Hom.formalSeries`.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny` and
  `TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`: `[n].formalSeries =
  (formalGroup W).zsmulSeries n`.
* `TauCeti.Isogeny.formalCoordinate_smul_formalGroup`: for separable `φ`,
  `φ.formalCoordinate • formalGroup W₁ = formalGroup W₂`.
* `TauCeti.Isogeny.height_formalGroup_eq`: isogenous elliptic curves have formal group laws of the
  same height.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and IV.4.
-/

public section

open WeierstrassCurve MvPowerSeries HahnSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.Isogeny

section ParamExpansion

variable {K : Type*} [Field K] {σ : Type*}

private noncomputable def paramExpansion (W : WeierstrassCurve K) {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    W.toAffine.FunctionField →ₐ[K] FractionRing (MvPowerSeries σ K) :=
  (LaurentSeries.mvSubstAlgHom hq hq0).comp W.functionFieldLaurentExpansion

private theorem paramExpansion_comp_fieldPullback {W₁ W₂ : WeierstrassCurve K}
    (φ : Isogeny W₁.toAffine W₂.toAffine) {q : MvPowerSeries σ K} (hq : constantCoeff q = 0)
    (hq0 : q ≠ 0) :
    (paramExpansion W₁ hq hq0).comp φ.fieldPullback =
      paramExpansion W₂
        (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)
        ((PowerSeries.mvPowerSeries_subst_eq_zero_iff hq hq0).not.mpr φ.formalSeries_ne_zero) := by
  refine AlgHom.ext fun z ↦ ?_
  rw [AlgHom.comp_apply, paramExpansion, AlgHom.comp_apply,
    φ.functionFieldLaurentExpansion_fieldPullback, ← AlgHom.comp_apply,
    LaurentSeries.mvSubstAlgHom_comp_substAlgHom, paramExpansion, AlgHom.comp_apply]

private theorem fracCurve_eq_baseChange (W : WeierstrassCurve K) :
    fracCurve W σ (FractionRing (MvPowerSeries σ K)) =
      W⁄(FractionRing (MvPowerSeries σ K)) := by
  rw [fracCurve_def, WeierstrassCurve.baseChange,
    IsScalarTower.algebraMap_eq K (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))]

private theorem map_paramExpansion_genericPoint (W : WeierstrassCurve K) [W.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries σ K))] {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    Affine.Point.map (paramExpansion W hq hq0) W.toAffine.genericPoint =
      AddEquiv.cast (M := fun V : WeierstrassCurve (FractionRing (MvPowerSeries σ K)) ↦
          V.toAffine.Point) (fracCurve_eq_baseChange W)
        (W.thetaPoint (fracCurve_Δ_ne_zero W W.isUnit_Δ.ne_zero) hq hq0) := by
  let KK := FractionRing (MvPowerSeries σ K)
  let ρ := algebraMap (MvPowerSeries σ K) KK
  have hw0 : ρ (PowerSeries.subst q (formalW W)) ≠ 0 := W.algebraMap_subst_formalW_ne_zero hq hq0
  have hYinv : paramExpansion W hq hq0 (-W.toAffine.genericY⁻¹) =
      ρ (PowerSeries.subst q (formalW W)) := by
    rw [paramExpansion, AlgHom.comp_apply, functionFieldLaurentExpansion_neg_inv_genericY,
      LaurentSeries.mvSubstAlgHom_coe]
  have hY : paramExpansion W hq hq0 W.toAffine.genericY =
      -1 / ρ (PowerSeries.subst q (formalW W)) := by
    rw [map_neg, map_inv₀, neg_eq_iff_eq_neg, inv_eq_iff_eq_inv] at hYinv
    rw [hYinv, inv_neg, neg_div, one_div]
  have hXY : paramExpansion W hq hq0 (-W.toAffine.genericX / W.toAffine.genericY) = ρ q := by
    rw [paramExpansion, AlgHom.comp_apply, functionFieldLaurentExpansion_neg_genericX_div_genericY,
      LaurentSeries.mvSubstAlgHom_coe, PowerSeries.subst_X (.of_constantCoeff_zero hq)]
  have hX : paramExpansion W hq hq0 W.toAffine.genericX =
      ρ q / ρ (PowerSeries.subst q (formalW W)) := by
    have hY0 : paramExpansion W hq hq0 W.toAffine.genericY ≠ 0 := by
      rw [hY]
      exact div_ne_zero (by norm_num) hw0
    rw [map_div₀, map_neg, div_eq_iff hY0, hY] at hXY
    linear_combination -hXY
  set P := Affine.Point.map (paramExpansion W hq hq0) W.toAffine.genericPoint
  have hxP : P.xCoord = ρ q / ρ (PowerSeries.subst q (formalW W)) := by
    rw [Affine.Point.xCoord_map, Affine.xCoord_genericPoint, hX]
  have hyP : P.yCoord = -1 / ρ (PowerSeries.subst q (formalW W)) := by
    rw [Affine.Point.yCoord_map, Affine.yCoord_genericPoint, hY]
  have hP0 : P ≠ 0 := by
    rintro h0
    rw [h0, Affine.Point.yCoord_zero] at hyP
    exact div_ne_zero (by norm_num) hw0 hyP.symm
  have hns : (fracCurve W σ KK).toAffine.Nonsingular
      (ρ q / ρ (PowerSeries.subst q (formalW W)))
      (-1 / ρ (PowerSeries.subst q (formalW W))) := by
    rw [fracCurve_eq_baseChange W, ← hxP, ← hyP]
    exact Affine.Point.nonsingular_coords hP0
  rw [W.thetaPoint_eq_some _ hq hq0 hns, AddEquiv.cast_apply,
    Affine.Point.cast_some (fracCurve_eq_baseChange W)]
  exact Affine.Point.eq_of_coords hP0 (Affine.Point.some_ne_zero _)
    (hxP.trans (Affine.Point.xCoord_some _).symm) (hyP.trans (Affine.Point.yCoord_some _).symm)

private theorem map_paramExpansion_tautologicalPoint {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
    [DecidableEq (FractionRing (MvPowerSeries σ K))] (φ : Isogeny W₁.toAffine W₂.toAffine)
    {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    Affine.Point.map (paramExpansion W₁ hq hq0) φ.pullback.tautologicalPoint =
      AddEquiv.cast (M := fun V : WeierstrassCurve (FractionRing (MvPowerSeries σ K)) ↦
          V.toAffine.Point) (fracCurve_eq_baseChange W₂)
        (W₂.thetaPoint (fracCurve_Δ_ne_zero W₂ W₂.isUnit_Δ.ne_zero)
          (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)
          ((PowerSeries.mvPowerSeries_subst_eq_zero_iff hq hq0).not.mpr
            φ.formalSeries_ne_zero)) := by
  rw [tautologicalPoint_eq_map_genericPoint, Affine.Point.map_map,
    paramExpansion_comp_fieldPullback, map_paramExpansion_genericPoint]

private theorem subst_formalGroup_eq_formalAdd (W : WeierstrassCurve K)
    {q₁ q₂ : MvPowerSeries σ K} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) :
    subst ![q₁, q₂] (formalGroup W).toPowerSeries =
      subst (pairSubstitution q₁ q₂) (formalAdd W) := by
  rw [formalGroup_toPowerSeries,
    MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _
      (hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i; exacts [h₁, h₂])]
  congr 1
  funext s
  rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [pairSubstitution]

end ParamExpansion

namespace Hom

section Basic

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

open scoped Classical in
/-- The formal power series of a morphism in `Hom W₁ W₂`, defined to be `0` on the zero morphism
and `φ.formalSeries` on an isogeny `φ`. -/
noncomputable def formalSeries (f : Hom W₁.toAffine W₂.toAffine) : K⟦X⟧ :=
  if hf : f = 0 then 0 else (toIsogeny hf).formalSeries

/-- The zero morphism has formal series `0`. -/
@[simp]
theorem formalSeries_zero : (0 : Hom W₁.toAffine W₂.toAffine).formalSeries = 0 := by
  classical
  simp [formalSeries]

/-- On an isogeny, `Hom.formalSeries` agrees with `Isogeny.formalSeries`. -/
@[simp]
theorem formalSeries_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalSeries = φ.formalSeries := by
  classical
  simp [formalSeries]

/-- A morphism has zero formal series if and only if it is the zero morphism. -/
@[simp]
theorem formalSeries_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · simp [φ.formalSeries_ne_zero]

/-- A nonzero morphism has a nonzero formal series. -/
theorem formalSeries_ne_zero {f : Hom W₁.toAffine W₂.toAffine} (hf : f ≠ 0) :
    f.formalSeries ≠ 0 :=
  formalSeries_eq_zero_iff.not.mpr hf

/-- Every morphism's formal series has zero constant coefficient. -/
@[simp]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

/-- The identity morphism has formal series `X`. -/
@[simp]
theorem formalSeries_id (W : WeierstrassCurve K) :
    (id W.toAffine).formalSeries = PowerSeries.X := by
  simp [id_def]

/-- Composition of morphisms corresponds to substitution of their formal series. -/
@[simp]
theorem formalSeries_comp (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalSeries = PowerSeries.subst f.formalSeries g.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · simp [PowerSeries.subst_zero]
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp [PowerSeries.subst_zero_of_constantCoeff_zero ψ.constantCoeff_formalSeries]
  · simp

end Basic

section Additive

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

/-- Negation of a morphism composes its formal series with the formal-group inverse. -/
@[simp]
theorem formalSeries_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalSeries = PowerSeries.subst f.formalSeries (formalGroup W₂).addInvX := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp [PowerSeries.subst_zero_of_constantCoeff_zero (formalGroup W₂).constantCoeff_addInvX]
  · rw [neg_ofIsogeny, ← ofIsogeny_comp_ofIsogeny, formalSeries_comp, formalSeries_ofIsogeny,
      formalSeries_ofIsogeny, formalSeries_negIsogeny, formalGroup_addInvX]

open scoped Classical in
private theorem thetaPoint_formalSeries_add
    (φ ψ χ : Isogeny W₁.toAffine W₂.toAffine) (hχ : ofIsogeny φ + ofIsogeny ψ = ofIsogeny χ)
    (hX0 : (X 0 : MvPowerSeries (Fin 2) K) ≠ 0) :
    let hΔ := fracCurve_Δ_ne_zero W₂ (σ := Fin 2)
      (KK := FractionRing (MvPowerSeries (Fin 2) K)) W₂.isUnit_Δ.ne_zero
    W₂.thetaPoint hΔ
      (PowerSeries.constantCoeff_subst_eq_zero
        (constantCoeff_X (R := K) (0 : Fin 2)) _ χ.constantCoeff_formalSeries)
      ((PowerSeries.mvPowerSeries_subst_eq_zero_iff
        (constantCoeff_X (R := K) (0 : Fin 2)) hX0).not.mpr χ.formalSeries_ne_zero) =
    W₂.thetaPoint hΔ
      (PowerSeries.constantCoeff_subst_eq_zero
        (constantCoeff_X (R := K) (0 : Fin 2)) _ φ.constantCoeff_formalSeries)
      ((PowerSeries.mvPowerSeries_subst_eq_zero_iff
        (constantCoeff_X (R := K) (0 : Fin 2)) hX0).not.mpr φ.formalSeries_ne_zero) +
    W₂.thetaPoint hΔ
      (PowerSeries.constantCoeff_subst_eq_zero
        (constantCoeff_X (R := K) (0 : Fin 2)) _ ψ.constantCoeff_formalSeries)
      ((PowerSeries.mvPowerSeries_subst_eq_zero_iff
        (constantCoeff_X (R := K) (0 : Fin 2)) hX0).not.mpr ψ.formalSeries_ne_zero) := by
  intro hΔ
  have ht := congrArg
    (Affine.Point.map (paramExpansion W₁ (constantCoeff_X (R := K) (0 : Fin 2)) hX0))
    ((tautologicalPoint_add (ofIsogeny φ) (ofIsogeny ψ)).symm.trans
      (congrArg tautologicalPoint hχ))
  simp only [tautologicalPoint_ofIsogeny, _root_.map_add,
    map_paramExpansion_tautologicalPoint] at ht
  rw [← _root_.map_add (AddEquiv.cast _)] at ht
  exact (AddEquiv.cast _).injective ht.symm

omit [W₂.IsElliptic] in
private theorem eq_subst_formalGroup_of_subst_pair_formalAdd_eq
    {q₁ q₂ q₃ : MvPowerSeries (Fin 2) K}
    (hc₁ : constantCoeff q₁ = 0) (hc₂ : constantCoeff q₂ = 0) (hc₃ : constantCoeff q₃ = 0)
    (heq : subst (pairSubstitution (X 1) q₃) (formalAdd W₂) =
      subst (pairSubstitution (subst (pairSubstitution (X 1) q₁) (formalAdd W₂)) q₂)
        (formalAdd W₂)) :
    q₃ = subst ![q₁, q₂] (formalGroup W₂).toPowerSeries := by
  have hcX1 := constantCoeff_X (R := K) (1 : Fin 2)
  have hcF₁ := constantCoeff_subst_pair_formalAdd W₂ hcX1 hc₁
  let P0 : (formalGroup W₂).Point (Fin 2) := ⟨X 1, .of_constantCoeff_zero hcX1⟩
  let P1 : (formalGroup W₂).Point (Fin 2) := ⟨q₁, .of_constantCoeff_zero hc₁⟩
  let P2 : (formalGroup W₂).Point (Fin 2) := ⟨q₂, .of_constantCoeff_zero hc₂⟩
  let P3 : (formalGroup W₂).Point (Fin 2) := ⟨q₃, .of_constantCoeff_zero hc₃⟩
  have hP : P0 + P3 = (P0 + P1) + P2 := Subtype.ext <| by
    rw [FormalGroup.add_apply, FormalGroup.add_apply, FormalGroup.add_apply]
    simpa only [P0, P1, P2, P3, subst_formalGroup_eq_formalAdd,
      hcX1, hc₁, hc₂, hc₃, hcF₁] using heq
  have hP_eq : P3 = P1 + P2 := add_left_cancel (hP.trans (add_assoc P0 P1 P2))
  exact congrArg Subtype.val hP_eq

private theorem formalSeries_add_of_ne_zero {f g : Hom W₁.toAffine W₂.toAffine}
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    (f + g).formalSeries =
      subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries := by
  classical
  obtain ⟨φ, rfl⟩ := (eq_zero_or_exists_ofIsogeny f).resolve_left hf
  obtain ⟨ψ, rfl⟩ := (eq_zero_or_exists_ofIsogeny g).resolve_left hg
  obtain ⟨χ, hχ⟩ := (eq_zero_or_exists_ofIsogeny (ofIsogeny φ + ofIsogeny ψ)).resolve_left hfg
  have hΔ := fracCurve_Δ_ne_zero W₂ (σ := Fin 2)
    (KK := FractionRing (MvPowerSeries (Fin 2) K)) W₂.isUnit_Δ.ne_zero
  have hX0 : (X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hX1 : (X 1 : MvPowerSeries (Fin 2) K) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hcX0 := constantCoeff_X (R := K) (0 : Fin 2)
  have hcX1 := constantCoeff_X (R := K) (1 : Fin 2)
  have hc₁ := PowerSeries.constantCoeff_subst_eq_zero hcX0 _ φ.constantCoeff_formalSeries
  have hc₂ := PowerSeries.constantCoeff_subst_eq_zero hcX0 _ ψ.constantCoeff_formalSeries
  have hc₃ := PowerSeries.constantCoeff_subst_eq_zero hcX0 _ χ.constantCoeff_formalSeries
  have hq₁0 := (PowerSeries.mvPowerSeries_subst_eq_zero_iff hcX0 hX0).not.mpr φ.formalSeries_ne_zero
  have hq₂0 := (PowerSeries.mvPowerSeries_subst_eq_zero_iff hcX0 hX0).not.mpr ψ.formalSeries_ne_zero
  have hq₃0 := (PowerSeries.mvPowerSeries_subst_eq_zero_iff hcX0 hX0).not.mpr χ.formalSeries_ne_zero
  have hs1 := hasSubst_coordSpecialize (O := K) (1 : Fin 2)
  have hgX1 := subst_coordSpecialize_X_self (O := K) (1 : Fin 2)
  have hg₁ := subst_coordSpecialize_powerSeriesSubst_X_of_ne (O := K) (i := (1 : Fin 2)) (j := 0)
    (by decide) φ.constantCoeff_formalSeries
  have hg₂ := subst_coordSpecialize_powerSeriesSubst_X_of_ne (O := K) (i := (1 : Fin 2)) (j := 0)
    (by decide) ψ.constantCoeff_formalSeries
  have hg₃ := subst_coordSpecialize_powerSeriesSubst_X_of_ne (O := K) (i := (1 : Fin 2)) (j := 0)
    (by decide) χ.constantCoeff_formalSeries
  have hcF₁ := constantCoeff_subst_pair_formalAdd W₂ hcX1 hc₁
  have hF₁0 := subst_pair_formalAdd_ne_zero W₂ hs1 hcX1 hc₁ hgX1 hg₁
  have hgF₁ := W₂.subst_subst_pair_formalAdd_eq_X hs1 hcX1 hc₁ hgX1 hg₁
  have hcL := constantCoeff_subst_pair_formalAdd W₂ hcX1 hc₃
  have hL0 := subst_pair_formalAdd_ne_zero W₂ hs1 hcX1 hc₃ hgX1 hg₃
  have hcR := constantCoeff_subst_pair_formalAdd W₂ hcF₁ hc₂
  have hR0 := subst_pair_formalAdd_ne_zero W₂ hs1 hcF₁ hc₂ hgF₁ hg₂
  have eL := thetaPoint_add_of_subst_separates W₂ hΔ hs1 hcX1 hc₃ hX1 hq₃0 hgX1 hg₃ hcL hL0
  have e₁ := thetaPoint_add_of_subst_separates W₂ hΔ hs1 hcX1 hc₁ hX1 hq₁0 hgX1 hg₁ hcF₁ hF₁0
  have eR := thetaPoint_add_of_subst_separates W₂ hΔ hs1 hcF₁ hc₂ hF₁0 hq₂0 hgF₁ hg₂ hcR hR0
  have hq₃ := eq_subst_formalGroup_of_subst_pair_formalAdd_eq hc₁ hc₂ hc₃
    (thetaPoint_inj W₂ hΔ hcL hcR hL0 hR0
      (by rw [← eL, thetaPoint_formalSeries_add φ ψ χ hχ hX0, ← add_assoc, e₁, eR]))
  have hspec := congrArg (subst (coordSpecialize (O := K) (0 : Fin 2))) hq₃
  rw [subst_coordSpecialize_powerSeriesSubst_X_self] at hspec
  rw [hχ, formalSeries_ofIsogeny, hspec, subst_comp_subst_apply
    (hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i; exacts [hc₁, hc₂])
    (hasSubst_coordSpecialize (O := K) (0 : Fin 2)), formalSeries_ofIsogeny, formalSeries_ofIsogeny]
  congr 1
  funext i
  fin_cases i <;> exact subst_coordSpecialize_powerSeriesSubst_X_self (0 : Fin 2) _

/-- **Additivity of formal power series** (Silverman IV.4.2(a)): the formal series of a sum of
morphisms is the formal-group sum of their formal series. -/
@[simp]
theorem formalSeries_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalSeries =
      subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries := by
  by_cases hf : f = 0
  · rw [hf, zero_add, formalSeries_zero]
    exact ((formalGroup W₂).zero_add (.of_constantCoeff_zero' g.constantCoeff_formalSeries)).symm
  by_cases hg : g = 0
  · rw [hg, add_zero, formalSeries_zero]
    exact ((formalGroup W₂).add_zero (.of_constantCoeff_zero' f.constantCoeff_formalSeries)).symm
  by_cases hfg : f + g = 0
  · have hg' : g = -f := eq_neg_of_add_eq_zero_right hfg
    rw [hfg, formalSeries_zero, hg', formalSeries_neg]
    exact ((formalGroup W₂).subst_self_addInvX_eq_zero
      (.of_constantCoeff_zero' f.constantCoeff_formalSeries)).symm
  exact formalSeries_add_of_ne_zero hf hg hfg

/-- Bundled additive homomorphism sending a morphism in `Hom W₁ W₂` to its formal power series in
the group `(formalGroup W₂).Point Unit`. -/
noncomputable def formalSeriesAddHom :
    Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit where
  toFun f := ⟨f.formalSeries, .of_constantCoeff_zero' f.constantCoeff_formalSeries⟩
  map_zero' := Subtype.ext
    (formalSeries_zero.trans (FormalGroup.zero_apply (F := formalGroup W₂)).symm)
  map_add' f g := Subtype.ext (formalSeries_add f g)

/-- The power series underlying `formalSeriesAddHom f` is `f.formalSeries`. -/
@[simp]
theorem val_formalSeriesAddHom (f : Hom W₁.toAffine W₂.toAffine) :
    (formalSeriesAddHom f).val = f.formalSeries :=
  (rfl)

/-- Subtraction of morphisms corresponds to subtraction in the formal group law. -/
theorem formalSeries_sub (f g : Hom W₁.toAffine W₂.toAffine) :
    (f - g).formalSeries =
      subst ![f.formalSeries, PowerSeries.subst g.formalSeries (formalGroup W₂).addInvX]
        (formalGroup W₂).toPowerSeries := by
  rw [sub_eq_add_neg, formalSeries_add, formalSeries_neg]

/-- Natural-number scalar multiplication of a morphism composes its formal series with the
`n`-series of the target formal group law. -/
@[simp]
theorem formalSeries_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).nsmulSeries n) :=
  (congrArg Subtype.val (_root_.map_nsmul formalSeriesAddHom n f)).trans
    ((formalGroup W₂).subst_nsmulSeries (formalSeriesAddHom f) n).symm

/-- Integer scalar multiplication of a morphism composes its formal series with the integer
multiplication series of the target formal group law. -/
@[simp]
theorem formalSeries_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).zsmulSeries n) :=
  (congrArg Subtype.val (_root_.map_zsmul formalSeriesAddHom n f)).trans
    ((formalGroup W₂).subst_zsmulSeries (formalSeriesAddHom f) n).symm

end Additive

end Hom

section MulByInt

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The formal power series of `[n]` is the formal-group `n`-series** (Silverman IV.4.2): for
every `n : ℤ` with nonvanishing division polynomial, `[n].formalSeries =
(formalGroup W).zsmulSeries n`. -/
@[simp]
theorem formalSeries_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  rw [← Hom.formalSeries_ofIsogeny, ofIsogeny_mulByIntIsogeny, Hom.formalSeries_zsmul,
    Hom.formalSeries_id, PowerSeries.X_subst]

-- Not `@[simp]`: `mulByIntIsogenyOfNeZero` is an `abbrev`, so `formalSeries_mulByIntIsogeny`
-- already simplifies it.
/-- For every nonzero `n : ℤ`, the formal power series of `mulByIntIsogenyOfNeZero` is
`(formalGroup W).zsmulSeries n`. -/
theorem formalSeries_mulByIntIsogenyOfNeZero {n : ℤ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n :=
  formalSeries_mulByIntIsogeny W _

end MulByInt

section FormalGroupHom

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

private theorem valuation_map_sub_algebraMap_coordinateRing_lt_one [W₁.IsElliptic]
    (h : (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).Equation
      W₁.toAffine.genericX W₁.toAffine.genericY)
    (r : W₁.toAffine.CoordinateRing) :
    (Place.ofPrime W₁.toAffine.FunctionField
      (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).FunctionField
      (Affine.CoordinateRing.pointPlace h)).valuation
      (Affine.FunctionField.map W₁.toAffine (algebraMap K W₁.toAffine.FunctionField)
          (algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField r) -
        algebraMap W₁.toAffine.FunctionField
          (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).FunctionField
          (algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField r)) < 1 := by
  let L := W₁.toAffine.FunctionField
  let V := W₁.toAffine.map (algebraMap K L)
  let I := (Affine.CoordinateRing.pointPlace h).asIdeal
  rw [Affine.FunctionField.map_algebraMap_coordinateRing,
    IsScalarTower.algebraMap_apply L V.CoordinateRing V.FunctionField, ← map_sub,
    Place.valuation_ofPrime_algebraMap_lt_one_iff, ← Ideal.Quotient.eq]
  have hhom : (Ideal.Quotient.mk I).comp (Affine.CoordinateRing.map W₁.toAffine (algebraMap K L)) =
      (Ideal.Quotient.mk I).comp
        ((algebraMap L V.CoordinateRing).comp (algebraMap W₁.toAffine.CoordinateRing L)) := by
    apply Affine.CoordinateRing.ringHom_ext W₁.toAffine
    · intro a
      simp only [RingHom.comp_apply, Affine.CoordinateRing.map_algebraMap,
        ← IsScalarTower.algebraMap_apply K W₁.toAffine.CoordinateRing L]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
        Affine.CoordinateRing.map_of_X, Ideal.Quotient.eq,
        ← Place.valuation_ofPrime_algebraMap_lt_one_iff L V.FunctionField
          (Affine.CoordinateRing.pointPlace h),
        map_sub, ← IsScalarTower.algebraMap_apply L V.CoordinateRing V.FunctionField,
        ← AdjoinRoot.algebraMap_eq, ← AdjoinRoot.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply (Polynomial L) V.CoordinateRing V.FunctionField,
        ← IsScalarTower.algebraMap_apply (Polynomial K) W₁.toAffine.CoordinateRing L,
        ← Affine.genericX_eq_algebraMap V, ← Affine.genericX_eq_algebraMap W₁.toAffine]
      exact Affine.valuation_pointPlace_genericX_sub_lt_one V h
    · have hYV : algebraMap V.CoordinateRing V.FunctionField (AdjoinRoot.root V.polynomial) =
          V.genericY := by rw [Affine.genericY_def, AdjoinRoot.mk_X]
      have hY₁ : algebraMap W₁.toAffine.CoordinateRing L
          (AdjoinRoot.root W₁.toAffine.polynomial) = W₁.toAffine.genericY := by
        rw [Affine.genericY_def, AdjoinRoot.mk_X]
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
        Affine.CoordinateRing.map_root, Ideal.Quotient.eq,
        ← Place.valuation_ofPrime_algebraMap_lt_one_iff L V.FunctionField
          (Affine.CoordinateRing.pointPlace h),
        map_sub, ← IsScalarTower.algebraMap_apply L V.CoordinateRing V.FunctionField, hYV, hY₁]
      exact Affine.valuation_pointPlace_genericY_sub_lt_one V h
  exact RingHom.congr_fun hhom r

private theorem valuation_map_sub_algebraMap_lt_one_at_genericPoint [W₁.IsElliptic]
    (h : (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).Equation
      W₁.toAffine.genericX W₁.toAffine.genericY)
    (z : W₁.toAffine.FunctionField) :
    (Place.ofPrime W₁.toAffine.FunctionField
      (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).FunctionField
      (Affine.CoordinateRing.pointPlace h)).valuation
      (Affine.FunctionField.map W₁.toAffine (algebraMap K W₁.toAffine.FunctionField) z -
        algebraMap W₁.toAffine.FunctionField
          (W₁.toAffine.map (algebraMap K W₁.toAffine.FunctionField)).FunctionField z) < 1 := by
  let L := W₁.toAffine.FunctionField
  let V := W₁.toAffine.map (algebraMap K L)
  set v := (Place.ofPrime L V.FunctionField (Affine.CoordinateRing.pointPlace h)).valuation with hv
  let α := Affine.FunctionField.map W₁.toAffine (algebraMap K L)
  let β := algebraMap L V.FunctionField
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W₁.toAffine.CoordinateRing) z
  let x := algebraMap W₁.toAffine.CoordinateRing L a
  let y := algebraMap W₁.toAffine.CoordinateRing L b
  have hy0 : y ≠ 0 := map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective _ L) hb
  have hx_lt : v (α x - β x) < 1 := valuation_map_sub_algebraMap_coordinateRing_lt_one h a
  have hy_lt : v (α y - β y) < 1 := valuation_map_sub_algebraMap_coordinateRing_lt_one h b
  have hx_le : v (α x) ≤ 1 := by
    rw [hv, Affine.FunctionField.map_algebraMap_coordinateRing, Place.valuation_ofPrime]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  have hβy : v (β y) = 1 := Valuation.IsTrivialOn.eq_one y hy0
  have hαy : v (α y) = 1 := by
    have heq : α y = (α y - β y) + β y := (sub_add_cancel _ _).symm
    rw [heq, v.map_add_eq_of_lt_right (hy_lt.trans_eq hβy.symm), hβy]
  have hαy0 : α y ≠ 0 := v.ne_zero_iff.mp (by rw [hαy]; exact one_ne_zero)
  have hβy0 : β y ≠ 0 := v.ne_zero_iff.mp (by rw [hβy]; exact one_ne_zero)
  have hdiv : α (x / y) - β (x / y) = ((α x - β x) * α y - α x * (α y - β y)) / (α y * β y) := by
    rw [map_div₀, map_div₀]
    field_simp
    ring
  rw [hdiv, map_div₀, v.map_mul, hαy, hβy, mul_one, div_one]
  refine v.map_sub_lt ?_ ?_
  · rw [v.map_mul, hαy, mul_one]
    exact hx_lt
  · rw [v.map_mul, mul_comm]
    exact mul_lt_one_of_lt_of_le hy_lt hx_le

private theorem pointMap_map_genericPoint [W₁.IsElliptic] [W₂.IsElliptic]
    [DecidableEq W₁.toAffine.FunctionField] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    ((Hom.ofIsogeny φ).map (algebraMap K W₁.toAffine.FunctionField)).pointMap
        W₁.toAffine.genericPoint =
      φ.pullback.tautologicalPoint := by
  let L := W₁.toAffine.FunctionField
  have hnsP : (W₁.toAffine.map (algebraMap K L)).Nonsingular
      W₁.toAffine.genericX W₁.toAffine.genericY :=
    Affine.nonsingular_genericX_genericY W₁.toAffine
  have hnsQ : (W₂.toAffine.map (algebraMap K L)).Nonsingular
      φ.pullback.tautologicalPoint.xCoord φ.pullback.tautologicalPoint.yCoord :=
    Affine.Point.nonsingular_coords (CoordinatePullback.tautologicalPoint_ne_zero φ.pullback)
  rw [Hom.ofIsogeny_map, Affine.genericPoint_eq_some,
    ← Affine.Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero φ.pullback)]
  -- `WeierstrassCurve.baseChange` is a plain `def` in Mathlib with no unfolding lemma, so align
  -- `(W⁄L).toAffine` with `W.toAffine.map (algebraMap K L)` before `pointMap_eq_iff`.
  change (Hom.ofIsogeny (φ.map (algebraMap K L))).pointMap
      (.some (W' := W₁.toAffine.map (algebraMap K L)) _ _ hnsP) =
    .some (W' := W₂.toAffine.map (algebraMap K L)) _ _ hnsQ
  rw [Hom.pointMap_eq_iff, Hom.tautologicalPoint_ofIsogeny,
    ← Affine.Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero _),
    Affine.coe_pointEquivDegreeOnePlace_some, Affine.Point.equivBaseChangeSelf_some,
    Affine.some_sub_baseChange_mem_polePoints_iff]
  simp only [CoordinatePullback.xCoord_tautologicalPoint,
    CoordinatePullback.yCoord_tautologicalPoint, map_pullback,
    CoordinatePullback.map_of_X, CoordinatePullback.map_root]
  exact ⟨valuation_map_sub_algebraMap_lt_one_at_genericPoint _ _,
    valuation_map_sub_algebraMap_lt_one_at_genericPoint _ _⟩

private theorem pointMap_thetaPoint [W₁.IsElliptic] [W₂.IsElliptic] {σ : Type*}
    [DecidableEq (FractionRing (MvPowerSeries σ K))] (φ : Isogeny W₁.toAffine W₂.toAffine)
    {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    ((Hom.ofIsogeny φ).map (algebraMap K (FractionRing (MvPowerSeries σ K)))).pointMap
      (AddEquiv.cast (M := fun V : WeierstrassCurve (FractionRing (MvPowerSeries σ K)) ↦
          V.toAffine.Point) (fracCurve_eq_baseChange W₁)
        (W₁.thetaPoint (fracCurve_Δ_ne_zero W₁ W₁.isUnit_Δ.ne_zero) hq hq0)) =
      AddEquiv.cast (M := fun V : WeierstrassCurve (FractionRing (MvPowerSeries σ K)) ↦
          V.toAffine.Point) (fracCurve_eq_baseChange W₂)
        (W₂.thetaPoint (fracCurve_Δ_ne_zero W₂ W₂.isUnit_Δ.ne_zero)
          (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)
          ((PowerSeries.mvPowerSeries_subst_eq_zero_iff hq hq0).not.mpr
            φ.formalSeries_ne_zero)) := by
  classical
  rw [← map_paramExpansion_genericPoint W₁ hq hq0, Hom.pointMap_map_algebraMap_map,
    pointMap_map_genericPoint, map_paramExpansion_tautologicalPoint]

private theorem subst_pair_formalSeries_formalAdd_ne_zero
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    subst (pairSubstitution
      (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K) φ.formalSeries)
      (PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) φ.formalSeries)) (formalAdd W₂) ≠ 0 := by
  let q₀ := PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K) φ.formalSeries
  let q₁ := PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) φ.formalSeries
  have hs0 := hasSubst_coordSpecialize (O := K) (0 : Fin 2)
  have hcq₀ := PowerSeries.constantCoeff_subst_eq_zero
    (constantCoeff_X (R := K) (0 : Fin 2)) _ φ.constantCoeff_formalSeries
  have hcq₁ := PowerSeries.constantCoeff_subst_eq_zero
    (constantCoeff_X (R := K) (1 : Fin 2)) _ φ.constantCoeff_formalSeries
  have hgq₀ : subst (coordSpecialize (O := K) (0 : Fin 2)) q₀ = φ.formalSeries :=
    subst_coordSpecialize_powerSeriesSubst_X_self (0 : Fin 2) φ.formalSeries
  have hgq₁ : subst (coordSpecialize (O := K) (0 : Fin 2)) q₁ = 0 :=
    subst_coordSpecialize_powerSeriesSubst_X_of_ne (by decide) φ.constantCoeff_formalSeries
  have hfam : (fun s : Unit ⊕ Unit ↦ subst (coordSpecialize (O := K) (0 : Fin 2))
      (Sum.elim (fun _ ↦ q₀) (fun _ ↦ q₁) s)) =
        Sum.elim (fun _ ↦ φ.formalSeries) (fun _ ↦ 0) :=
    funext fun s ↦ by rcases s with ⟨⟩ | ⟨⟩; exacts [hgq₀, hgq₁]
  intro h0
  apply φ.formalSeries_ne_zero
  have hc := congrArg (subst (coordSpecialize (O := K) (0 : Fin 2))) h0
  rw [← coe_substAlgHom hs0, map_zero, coe_substAlgHom hs0,
    subst_comp_subst_apply (hasSubst_pair hcq₀ hcq₁) hs0, hfam] at hc
  have hunit : subst (Sum.elim (fun _ ↦ φ.formalSeries) (fun _ ↦ 0)) (formalAdd W₂) =
      φ.formalSeries := by
    rw [← subst_formalGroup_eq_formalAdd W₂ φ.constantCoeff_formalSeries rfl]
    exact (formalGroup W₂).add_zero (.of_constantCoeff_zero' φ.constantCoeff_formalSeries)
  exact hunit.symm.trans hc

private theorem formalGroup_toPowerSeries_eq_subst_pair_X (W : WeierstrassCurve K) :
    (formalGroup W).toPowerSeries =
      subst (pairSubstitution (X 0 : MvPowerSeries (Fin 2) K) (X 1)) (formalAdd W) := by
  have h := subst_formalGroup_eq_formalAdd W
    (constantCoeff_X (R := K) (0 : Fin 2)) (constantCoeff_X (R := K) (1 : Fin 2))
  rwa [finTwo_X_eq_X, subst_self, _root_.id] at h

open scoped Classical in
private theorem thetaPoint_add_formalSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
    (hX0 : (X 0 : MvPowerSeries (Fin 2) K) ≠ 0) (hX1 : (X 1 : MvPowerSeries (Fin 2) K) ≠ 0) :
    let hΔ₂ := fracCurve_Δ_ne_zero W₂ (σ := Fin 2)
      (KK := FractionRing (MvPowerSeries (Fin 2) K)) W₂.isUnit_Δ.ne_zero
    let hcX0 := constantCoeff_X (R := K) (0 : Fin 2)
    let hcX1 := constantCoeff_X (R := K) (1 : Fin 2)
    let hcq₀ := PowerSeries.constantCoeff_subst_eq_zero hcX0 _ φ.constantCoeff_formalSeries
    let hcq₁ := PowerSeries.constantCoeff_subst_eq_zero hcX1 _ φ.constantCoeff_formalSeries
    W₂.thetaPoint hΔ₂ hcq₀
        ((PowerSeries.mvPowerSeries_subst_eq_zero_iff hcX0 hX0).not.mpr φ.formalSeries_ne_zero) +
      W₂.thetaPoint hΔ₂ hcq₁
        ((PowerSeries.mvPowerSeries_subst_eq_zero_iff hcX1 hX1).not.mpr φ.formalSeries_ne_zero) =
    W₂.thetaPoint hΔ₂ (constantCoeff_subst_pair_formalAdd W₂ hcq₀ hcq₁)
      (subst_pair_formalSeries_formalAdd_ne_zero φ) := by
  intro hΔ₂ hcX0 hcX1 hcq₀ hcq₁
  let q₀ := PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K) φ.formalSeries
  let q₁ := PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) φ.formalSeries
  have hgq₀ : subst (coordSpecialize (O := K) (0 : Fin 2)) q₀ = φ.formalSeries :=
    subst_coordSpecialize_powerSeriesSubst_X_self (0 : Fin 2) φ.formalSeries
  have hgq₁ : subst (coordSpecialize (O := K) (0 : Fin 2)) q₁ = 0 :=
    subst_coordSpecialize_powerSeriesSubst_X_of_ne (by decide) φ.constantCoeff_formalSeries
  have hne₁ : q₀ ≠ q₁ := fun h ↦ φ.formalSeries_ne_zero (hgq₀.symm.trans (by rw [h, hgq₁]))
  have hne₂ : q₀ ≠ PowerSeries.subst q₁ (formalInverse W₂) := fun h ↦
    φ.formalSeries_ne_zero <| hgq₀.symm.trans <| by
      rw [h, subst_powerSeriesSubst (hasSubst_coordSpecialize (O := K) (0 : Fin 2))
          (.of_constantCoeff_zero hcq₁), hgq₁,
        PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_formalInverse W₂)]
  exact thetaPoint_add_of_ne W₂ hΔ₂ hcq₀ hcq₁
    ((PowerSeries.mvPowerSeries_subst_eq_zero_iff hcX0 hX0).not.mpr φ.formalSeries_ne_zero)
    ((PowerSeries.mvPowerSeries_subst_eq_zero_iff hcX1 hX1).not.mpr φ.formalSeries_ne_zero)
    hne₁ hne₂ (constantCoeff_subst_pair_formalAdd W₂ hcq₀ hcq₁)
    (subst_pair_formalSeries_formalAdd_ne_zero φ)

private theorem formalSeries_hom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    PowerSeries.subst (formalGroup W₁).toPowerSeries φ.formalSeries =
      subst (fun i ↦ φ.formalSeries.toMvPowerSeries i) (formalGroup W₂).toPowerSeries := by
  classical
  have : W₁.IsElliptic := φ.isElliptic
  have hΔ₁ := fracCurve_Δ_ne_zero W₁ (σ := Fin 2)
    (KK := FractionRing (MvPowerSeries (Fin 2) K)) W₁.isUnit_Δ.ne_zero
  have hΔ₂ := fracCurve_Δ_ne_zero W₂ (σ := Fin 2)
    (KK := FractionRing (MvPowerSeries (Fin 2) K)) W₂.isUnit_Δ.ne_zero
  have hX0 : (X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hX1 : (X 1 : MvPowerSeries (Fin 2) K) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hcX0 := constantCoeff_X (R := K) (0 : Fin 2)
  have hcX1 := constantCoeff_X (R := K) (1 : Fin 2)
  have hs0 := hasSubst_coordSpecialize (O := K) (0 : Fin 2)
  have hgX0 := subst_coordSpecialize_X_self (O := K) (0 : Fin 2)
  have hgX1 := subst_coordSpecialize_X_of_ne (O := K) (i := (0 : Fin 2)) (j := 1) (by decide)
  have hcF₁ := constantCoeff_subst_pair_formalAdd W₁ hcX0 hcX1
  have hF₁0 := subst_pair_formalAdd_ne_zero W₁ hs0 hcX0 hcX1 hgX0 hgX1
  have e₁ := thetaPoint_add_of_subst_separates W₁ hΔ₁ hs0 hcX0 hcX1 hX0 hX1 hgX0 hgX1 hcF₁ hF₁0
  have hcq₀ := PowerSeries.constantCoeff_subst_eq_zero hcX0 _ φ.constantCoeff_formalSeries
  have hcq₁ := PowerSeries.constantCoeff_subst_eq_zero hcX1 _ φ.constantCoeff_formalSeries
  have hcF₁φ := PowerSeries.constantCoeff_subst_eq_zero hcF₁ _ φ.constantCoeff_formalSeries
  have hF₁φ0 :=
    (PowerSeries.mvPowerSeries_subst_eq_zero_iff hcF₁ hF₁0).not.mpr φ.formalSeries_ne_zero
  let eW₁ := AddEquiv.cast
    (M := fun V : WeierstrassCurve (FractionRing (MvPowerSeries (Fin 2) K)) ↦ V.toAffine.Point)
    (fracCurve_eq_baseChange W₁)
  let eW₂ := AddEquiv.cast
    (M := fun V : WeierstrassCurve (FractionRing (MvPowerSeries (Fin 2) K)) ↦ V.toAffine.Point)
    (fracCurve_eq_baseChange W₂)
  have hpm : eW₂ (W₂.thetaPoint hΔ₂ hcq₀
        ((PowerSeries.mvPowerSeries_subst_eq_zero_iff hcX0 hX0).not.mpr φ.formalSeries_ne_zero) +
      W₂.thetaPoint hΔ₂ hcq₁
        ((PowerSeries.mvPowerSeries_subst_eq_zero_iff hcX1 hX1).not.mpr φ.formalSeries_ne_zero)) =
    eW₂ (W₂.thetaPoint hΔ₂ hcF₁φ hF₁φ0) := by
    rw [map_add eW₂, ← pointMap_thetaPoint φ hcX0 hX0, ← pointMap_thetaPoint φ hcX1 hX1,
      ← pointMap_thetaPoint φ hcF₁ hF₁0]
    exact (Hom.pointMap_add _ _ _).symm.trans
      (congrArg (((Hom.ofIsogeny φ).map
        (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).pointMap)
        ((map_add eW₁ _ _).symm.trans (congrArg eW₁ e₁)))
  have hinj := thetaPoint_inj W₂ hΔ₂ hcF₁φ (constantCoeff_subst_pair_formalAdd W₂ hcq₀ hcq₁)
    hF₁φ0 (subst_pair_formalSeries_formalAdd_ne_zero φ)
    (eW₂.injective hpm.symm |>.trans (thetaPoint_add_formalSeries φ hX0 hX1))
  rw [formalGroup_toPowerSeries_eq_subst_pair_X W₁, hinj,
    ← subst_formalGroup_eq_formalAdd W₂ hcq₀ hcq₁]
  refine congrArg (subst · (formalGroup W₂).toPowerSeries) (funext fun i ↦ ?_)
  fin_cases i <;> simp [PowerSeries.toMvPowerSeries_eq_subst]

/-- **Every isogeny induces a homomorphism of formal group laws** (Silverman IV.4.2): for
`φ : W₁ → W₂`, `φ.formalSeries` satisfies `φ(F_{W₁}(X, Y)) = F_{W₂}(φ(X), φ(Y))`. -/
noncomputable def formalGroupHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := φ.formalSeries
  zero_constantCoeff := φ.constantCoeff_formalSeries
  hom := formalSeries_hom φ

/-- The underlying power series of `φ.formalGroupHom` is `φ.formalSeries`. -/
@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries :=
  (rfl)

/-- The identity isogeny induces the identity homomorphism of formal group laws. -/
@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext : 1
  simp

/-- Composition of isogenies induces composition of homomorphisms of formal group laws. -/
@[simp]
theorem formalGroupHom_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (ψ : Isogeny W₂.toAffine W₃.toAffine) (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).formalGroupHom = ψ.formalGroupHom.comp φ.formalGroupHom := by
  ext : 1
  simp

/-- **Isogeny invariance of formal-group height**: if there is an isogeny `φ : W₁ → W₂` of elliptic
curves over `K`, then `formalGroup W₁` and `formalGroup W₂` have the same height at every `p`. -/
theorem height_formalGroup_eq [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) (p : ℕ) :
    (formalGroup W₁).height p = (formalGroup W₂).height p :=
  φ.formalGroupHom.height_eq φ.formalSeries_ne_zero p

section Separable

variable [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine)
  [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField]

/-- The formal coordinate with underlying power series `φ.formalSeries` attached to a separable
isogeny `φ : W₁ → W₂`. -/
noncomputable def formalCoordinate : FormalCoordinate K where
  toPowerSeries := φ.formalSeries
  constantCoeff_toPowerSeries := φ.constantCoeff_formalSeries
  isUnit_coeff_one := φ.coeff_one_formalSeries_ne_zero_of_isSeparable.isUnit

/-- The underlying power series of `φ.formalCoordinate` is `φ.formalSeries`. -/
@[simp]
theorem formalCoordinate_toPowerSeries : φ.formalCoordinate.toPowerSeries = φ.formalSeries :=
  (rfl)

/-- **A separable isogeny changes coordinates between the formal group laws**:
`φ.formalCoordinate • formalGroup W₁ = formalGroup W₂`. -/
theorem formalCoordinate_smul_formalGroup :
    φ.formalCoordinate • formalGroup W₁ = formalGroup W₂ :=
  φ.formalGroupHom.smul_eq rfl

/-- **A separable isogeny induces an isomorphism of formal group laws**
`formalGroup W₁ ≃ formalGroup W₂` (Silverman IV.4.2(c)). -/
noncomputable def formalGroupIso : FormalGroupIso (formalGroup W₁) (formalGroup W₂) :=
  φ.formalGroupHom.toIso <| by
    rw [formalGroupHom_toPowerSeries]
    exact φ.coeff_one_formalSeries_ne_zero_of_isSeparable.isUnit

/-- The forward homomorphism of `φ.formalGroupIso` is `φ.formalGroupHom`. -/
@[simp]
theorem formalGroupIso_toHom : φ.formalGroupIso.toHom = φ.formalGroupHom := by
  rw [formalGroupIso, FormalGroupHom.toIso_toHom]

end Separable

end FormalGroupHom

end TauCeti.Isogeny
