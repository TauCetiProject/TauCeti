/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
public import TauCeti.RingTheory.FormalGroup.Height.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.ThirdPoint
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# Formal group homomorphisms and addition of isogenies

An isogeny `φ : W₁ → W₂` of elliptic curves over a field `K` expands at infinity to a power series
`φ.formalSeries ∈ K⟦X⟧` in the local parameter `z = -x / y` (`Isogeny.formalSeries`).

This file proves that:

* every isogeny induces a nonzero homomorphism of formal group laws
  `Isogeny.formalGroupHom : FormalGroupHom (formalGroup W₁) (formalGroup W₂)`, so isogenous
  elliptic curves have formal groups of equal `n`-series order and equal height
  (`Isogeny.order_nsmulSeries_formalGroup_eq`, `Isogeny.height_formalGroup_eq`);
* addition of isogenies in `Hom W₁ W₂` corresponds to formal-group addition of their formal series
  (`Isogeny.formalSeries_eq_subst_of_ofIsogeny_add_eq`).

Both identities are read directly from the action `Hom.pointMap` on points of the base-changed
curves over `FractionRing (MvPowerSeries (Fin 2) K)` applied to the parametrized points
`WeierstrassCurve.thetaPoint`; the doubling case `φ = ψ` is deduced from
`(Q₀ + Q₁) + (Q₀ - Q₁) = Q₀ + Q₀` on `Fin 2` without a tangent formula.

## Main definitions

* `TauCeti.Isogeny.formalGroupHom`: the `FormalGroupHom` induced by an isogeny.

## Main results

* `TauCeti.Isogeny.formalInverse_ne_X`: on an elliptic curve over any field (including
  characteristic `2`), `W.formalInverse ≠ X`.
* `TauCeti.Isogeny.subst_formalGroup_formalSeries`: `φ(F₁(X, Y)) = F₂(φ(X), φ(Y))`.
* `TauCeti.Isogeny.order_nsmulSeries_formalGroup_eq`, `TauCeti.Isogeny.height_formalGroup_eq`:
  isogenous elliptic curves have formal groups of equal `n`-series order and equal height.
* `TauCeti.Isogeny.formalSeries_eq_subst_of_ofIsogeny_add_eq`: if
  `ofIsogeny φ + ofIsogeny ψ = ofIsogeny χ`, then
  `χ.formalSeries = F₂(φ.formalSeries, ψ.formalSeries)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine MvPowerSeries
open scoped LaurentSeries PowerSeries Polynomial.Bivariate

namespace TauCeti.Isogeny

/-- On an elliptic curve over any field (including characteristic `2`), the formal inverse is
distinct from `X`, because `[-1] ≠ [1]` in the torsion-free endomorphism group. -/
theorem formalInverse_ne_X {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] :
    W.formalInverse ≠ PowerSeries.X := by
  intro h
  have hhom : (-1 : ℤ) • Hom.id W.toAffine = (1 : ℤ) • Hom.id W.toAffine := by
    rw [neg_one_zsmul, one_zsmul, ← Hom.one_def, ← Hom.ofIsogeny_negIsogeny, Hom.one_def,
      Hom.id_def, Hom.ofIsogeny_injective.eq_iff, ← formalSeries_inj, formalSeries_negIsogeny,
      formalSeries_id, h]
  exact absurd (Hom.zsmul_id_injective hhom) (by decide)

/-! ### Evaluating Laurent expansions at multivariate power-series parameters -/

section ThetaPoint

variable {K : Type*} [Field K] {σ : Type*}

private theorem subst_mvPowerSeries_injective {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    Function.Injective
      ((algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))).comp
        (PowerSeries.substAlgHom (R := K) (.of_constantCoeff_zero hq)).toRingHom) := by
  have := MvPowerSeries.isDomain_of_isDomain (σ := σ) (R := K)
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  by_contra hf0
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    PowerSeries.coe_substAlgHom,
    map_eq_zero_iff _ (IsFractionRing.injective (MvPowerSeries σ K) _)] at hf
  have hhs : PowerSeries.HasSubst q := .of_constantCoeff_zero hq
  rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f), PowerSeries.subst_mul hhs,
    PowerSeries.subst_pow hhs, PowerSeries.subst_X hhs] at hf
  have hu0 : PowerSeries.subst q f.divXPowOrder ≠ 0 := by
    intro hu
    have hc := congrArg constantCoeff hu
    rw [map_zero, PowerSeries.constantCoeff_subst_of_constantCoeff_zero hq,
      Algebra.algebraMap_self_apply] at hc
    exact (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hf0) hc
  exact mul_ne_zero (pow_ne_zero _ hq0) hu0 hf

/-- Evaluating Laurent series at a nonzero parameter `q ∈ MvPowerSeries σ K` with `q(0) = 0`,
landing in `FractionRing (MvPowerSeries σ K)`. -/
private noncomputable def evalLaurent {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    K⸨X⸩ →+* FractionRing (MvPowerSeries σ K) :=
  IsFractionRing.lift (A := K⟦X⟧) (K := K⸨X⸩) (subst_mvPowerSeries_injective hq hq0)

private theorem evalLaurent_coe {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) (f : K⟦X⟧) :
    evalLaurent hq hq0 (f : K⸨X⸩) =
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
        (PowerSeries.subst q f) := by
  rw [evalLaurent, ← _root_.LaurentSeries.coe_algebraMap,
    IsFractionRing.lift_algebraMap (subst_mvPowerSeries_injective hq hq0),
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, PowerSeries.coe_substAlgHom]

private theorem subst_ne_zero_of_ne_zero {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) {g : K⟦X⟧} (hg0 : g ≠ 0) :
    PowerSeries.subst q g ≠ 0 := fun h ↦
  hg0 <| subst_mvPowerSeries_injective hq hq0 <| by
    simp [PowerSeries.coe_substAlgHom, h]

private theorem evalLaurent_comp_substAlgHom {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) {g : K⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (hg0 : g ≠ 0) :
    (evalLaurent hq hq0).comp (LaurentSeries.substAlgHom hg hg0).toRingHom =
      evalLaurent (PowerSeries.constantCoeff_subst_eq_zero hq g hg)
        (subst_ne_zero_of_ne_zero hq hq0 hg0) := by
  refine IsFractionRing.ringHom_ext (A := K⟦X⟧) fun f ↦ ?_
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    _root_.LaurentSeries.coe_algebraMap, LaurentSeries.substAlgHom_coe, evalLaurent_coe,
    evalLaurent_coe, PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero' hg)
      (.of_constantCoeff_zero hq)]

/-- Evaluating a rational function on `W` at the parametrized point `θ(q)` via its Laurent
expansion at infinity. -/
private noncomputable def thetaEval (W : WeierstrassCurve K) {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    W.toAffine.FunctionField →+* FractionRing (MvPowerSeries σ K) :=
  (evalLaurent hq hq0).comp W.functionFieldLaurentExpansion.toRingHom

private theorem thetaEval_comp_algebraMap (W : WeierstrassCurve K) {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (thetaEval W hq hq0).comp (algebraMap K W.toAffine.FunctionField) =
      (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))).comp
        (algebraMap K (MvPowerSeries σ K)) := by
  ext c
  simp only [thetaEval, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes, _root_.LaurentSeries.algebraMap_apply, ← PowerSeries.coe_C,
    evalLaurent_coe, PowerSeries.subst_C, c_eq_algebraMap]

private theorem thetaEval_genericY (W : WeierstrassCurve K) {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    thetaEval W hq hq0 W.toAffine.genericY =
      -1 / algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
        (PowerSeries.subst q W.formalW) := by
  have hw0 : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
      (PowerSeries.subst q W.formalW) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero hq hq0
  have h := congrArg (evalLaurent hq hq0) W.functionFieldLaurentExpansion_neg_inv_genericY
  rw [evalLaurent_coe] at h
  -- Rewrite the composite application as `thetaEval`.
  change thetaEval W hq hq0 (-W.toAffine.genericY⁻¹) = _ at h
  rw [map_neg, map_inv₀] at h
  have hy0 : thetaEval W hq hq0 W.toAffine.genericY ≠ 0 :=
    (map_ne_zero_iff _ (thetaEval W hq hq0).injective).mpr W.toAffine.genericY_ne_zero
  field_simp at h ⊢
  linear_combination -h

private theorem thetaEval_genericX (W : WeierstrassCurve K) {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    thetaEval W hq hq0 W.toAffine.genericX =
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) q /
        algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
          (PowerSeries.subst q W.formalW) := by
  have hw0 : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
      (PowerSeries.subst q W.formalW) ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero hq hq0
  have h := congrArg (evalLaurent hq hq0) W.functionFieldLaurentExpansion_neg_genericX_div_genericY
  rw [evalLaurent_coe, PowerSeries.subst_X (.of_constantCoeff_zero hq)] at h
  -- Rewrite the composite application as `thetaEval`.
  change thetaEval W hq hq0 (-W.toAffine.genericX / W.toAffine.genericY) = _ at h
  rw [map_div₀, map_neg, thetaEval_genericY W hq hq0] at h
  field_simp at h ⊢
  linear_combination h

private theorem thetaEval_fieldPullback {W₁ W₂ : WeierstrassCurve K}
    (φ : Isogeny W₁.toAffine W₂.toAffine) {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) (f : W₂.toAffine.FunctionField) :
    thetaEval W₁ hq hq0 (φ.fieldPullback f) =
      thetaEval W₂ (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)
        (subst_ne_zero_of_ne_zero hq hq0 φ.formalSeries_ne_zero) f := by
  have hcomp := RingHom.congr_fun (evalLaurent_comp_substAlgHom hq hq0
    φ.constantCoeff_formalSeries φ.formalSeries_ne_zero) (W₂.functionFieldLaurentExpansion f)
  simpa only [thetaEval, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    φ.functionFieldLaurentExpansion_fieldPullback] using hcomp

/-- Along a field homomorphism `E : K(W) →+* L` extending `ι : K →+* L`, every carried rational
function `FunctionField.map W ι z` reduces to `E z` at the place of `(E x, E y)`. -/
private theorem valuation_pointPlace_map_sub_lt_one {L : Type*} [Field L]
    (W : WeierstrassCurve.Affine K) [W.IsElliptic] (ι : K →+* L)
    (E : W.FunctionField →+* L) (hE : E.comp (algebraMap K W.FunctionField) = ι)
    (hpt : (W.map ι).Equation (E W.genericX) (E W.genericY))
    (z : W.FunctionField) :
    (Place.ofPrime L (W.map ι).FunctionField (CoordinateRing.pointPlace hpt)).valuation
      (FunctionField.map W ι z - algebraMap L (W.map ι).FunctionField (E z)) < 1 := by
  let _ : Algebra K L := ι.toAlgebra
  let E₀ : W.CoordinateRing →ₐ[K] L :=
    { E.comp (algebraMap W.CoordinateRing W.FunctionField) with
      commutes' c := by
        -- Unfold the coerced `RingHom` application to compose with `algebraMap`.
        change E (algebraMap W.CoordinateRing W.FunctionField (algebraMap K _ c)) = ι c
        rw [← IsScalarTower.algebraMap_apply K W.CoordinateRing W.FunctionField]
        exact RingHom.congr_fun hE c }
  have heval (p : K[X][Y]) :
      E (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W p)) =
        (p.map (Polynomial.mapRingHom ι)).evalEval (E W.genericX) (E W.genericY) := by
    have h := CoordinateRing.algHom_mk_eq_evalEval E₀ p
    have hx0 : E₀ (AdjoinRoot.of W.polynomial Polynomial.X) = E W.genericX := by
      simp [E₀, genericX_def]
    have hy0 : E₀ (AdjoinRoot.root W.polynomial) = E W.genericY := by simp [E₀, genericY_def]
    rwa [hx0, hy0] at h
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective b
  have hb0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W r) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr
      (nonZeroDivisors.ne_zero hb)
  have hr_eval : (r.map (Polynomial.mapRingHom ι)).evalEval (E W.genericX) (E W.genericY) ≠ 0 :=
    heval r ▸ (map_ne_zero_iff _ E.injective).mpr hb0
  set p' : L[X][Y] := p.map (Polynomial.mapRingHom ι)
  set r' : L[X][Y] := r.map (Polynomial.mapRingHom ι)
  set c : L := E (algebraMap _ _ (CoordinateRing.mk W p) / algebraMap _ _ (CoordinateRing.mk W r))
  have hr'_ne : algebraMap (W.map ι).CoordinateRing (W.map ι).FunctionField
      (CoordinateRing.mk (W.map ι) r') ≠ 0 := by
    rw [← CoordinateRing.map_mk, ← FunctionField.map_algebraMap_coordinateRing]
    exact (map_ne_zero_iff _ (FunctionField.map W ι).injective).mpr hb0
  have hrew : FunctionField.map W ι
        (algebraMap _ _ (CoordinateRing.mk W p) / algebraMap _ _ (CoordinateRing.mk W r)) -
      algebraMap L (W.map ι).FunctionField c =
      algebraMap _ _ (CoordinateRing.mk (W.map ι)
          (p' - Polynomial.C (Polynomial.C c) * r')) /
        algebraMap _ _ (CoordinateRing.mk (W.map ι) r') := by
    rw [map_div₀, FunctionField.map_algebraMap_coordinateRing,
      FunctionField.map_algebraMap_coordinateRing, CoordinateRing.map_mk, CoordinateRing.map_mk,
      map_sub, map_sub, map_mul, map_mul, sub_div, mul_div_cancel_right₀ _ hr'_ne]
    congr 1
  rw [hrew, Place.valuation_ofPrime]
  refine CoordinateRing.valuation_pointPlace_div_lt_one (W.map ι).FunctionField hpt hr_eval ?_
  rw [Polynomial.evalEval_sub, Polynomial.evalEval_mul, Polynomial.evalEval_C, Polynomial.eval_C]
  simp only [c, map_div₀, heval p, heval r, p', r', div_mul_cancel₀ _ hr_eval, sub_self]

/-- The base-change ring map `K → MvPowerSeries σ K → FractionRing (MvPowerSeries σ K)`. -/
private noncomputable def fracBaseHom (K : Type*) [Field K] (σ : Type*) :
    K →+* FractionRing (MvPowerSeries σ K) :=
  (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))).comp
    (algebraMap K (MvPowerSeries σ K))

private instance isElliptic_map_fracBaseHom (W : WeierstrassCurve K) [W.IsElliptic] :
    (W.toAffine.map (fracBaseHom K σ)).IsElliptic := by
  -- `W.toAffine.map ι` is `(W.map ι).toAffine` definitionally.
  change (W.map (fracBaseHom K σ)).IsElliptic
  infer_instance

/-- `WeierstrassCurve.thetaPoint` transported along `fracCurve_def` to
`(W.toAffine.map (fracBaseHom K σ)).Point`. -/
private noncomputable def thetaPointMap (W : WeierstrassCurve K) [W.IsElliptic]
    {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (W.toAffine.map (fracBaseHom K σ)).Point :=
  cast (congrArg (fun V : WeierstrassCurve (FractionRing (MvPowerSeries σ K)) ↦ V.toAffine.Point)
    (fracCurve_def W σ _))
    (W.thetaPoint (W.fracCurve_Δ_ne_zero W.isUnit_Δ.ne_zero) hq hq0)

private theorem nonsingular_cast {L : Type*} [CommRing L] {V V' : WeierstrassCurve L}
    (he : V = V') {x y : L} (h : V.toAffine.Nonsingular x y) :
    V'.toAffine.Nonsingular x y :=
  he ▸ h

private theorem point_cast_neg {L : Type*} [CommRing L] {V V' : WeierstrassCurve L}
    (he : V = V') (P : V.toAffine.Point) :
    cast (congrArg (fun U : WeierstrassCurve L ↦ U.toAffine.Point) he) (-P) =
      -cast (congrArg (fun U : WeierstrassCurve L ↦ U.toAffine.Point) he) P := by
  subst he; rfl

private theorem point_cast_add {L : Type*} [Field L] [DecidableEq L]
    {V V' : WeierstrassCurve L} (he : V = V') (P Q : V.toAffine.Point) :
    cast (congrArg (fun U : WeierstrassCurve L ↦ U.toAffine.Point) he) (P + Q) =
      cast (congrArg (fun U : WeierstrassCurve L ↦ U.toAffine.Point) he) P +
        cast (congrArg (fun U : WeierstrassCurve L ↦ U.toAffine.Point) he) Q := by
  subst he; rfl

private theorem exists_thetaPointMap_eq_some (W : WeierstrassCurve K) [W.IsElliptic]
    {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    ∃ hns : (W.toAffine.map (fracBaseHom K σ)).Nonsingular
        (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) q /
          algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
            (PowerSeries.subst q W.formalW))
        (-1 / algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
          (PowerSeries.subst q W.formalW)),
      thetaPointMap W hq hq0 = Point.some _ _ hns := by
  set KK := FractionRing (MvPowerSeries σ K)
  have hΔ := W.fracCurve_Δ_ne_zero (σ := σ) (KK := KK) W.isUnit_Δ.ne_zero
  have hwq : algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q W.formalW) =
      wEquationRHS (fracCurve W σ KK) (algebraMap (MvPowerSeries σ K) KK q)
        (algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q W.formalW)) := by
    conv_lhs => rw [W.subst_formalW_wEquation (.of_constantCoeff_zero hq)]
    simp [fracCurve_def, wEquationRHS_def]
  have hns₀ := chord_point_nonsingular (fracCurve W σ KK)
    (by simpa [wEquationRHS_def] using hwq)
    (W.algebraMap_subst_formalW_ne_zero hq hq0) hΔ
  refine ⟨nonsingular_cast (fracCurve_def W σ KK) hns₀, ?_⟩
  rw [thetaPointMap, W.thetaPoint_eq_some hΔ hq hq0 hns₀]
  exact Point.cast_some (fracCurve_def W σ KK) hns₀

private theorem thetaPointMap_ne_zero (W : WeierstrassCurve K) [W.IsElliptic]
    {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    thetaPointMap W hq hq0 ≠ 0 := by
  obtain ⟨hns, h⟩ := exists_thetaPointMap_eq_some W hq hq0
  exact h ▸ Point.some_ne_zero hns

private theorem thetaPointMap_neg
    (W : WeierstrassCurve K) [W.IsElliptic] {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0)
    (hi : constantCoeff (PowerSeries.subst q W.formalInverse) = 0)
    (hi0 : PowerSeries.subst q W.formalInverse ≠ 0) :
    thetaPointMap W hi hi0 = -thetaPointMap W hq hq0 := by
  rw [thetaPointMap, thetaPointMap, W.thetaPoint_neg _ hq hq0 hi hi0]
  exact point_cast_neg (fracCurve_def W σ (FractionRing (MvPowerSeries σ K))) _

private theorem thetaPointMap_inj (W : WeierstrassCurve K) [W.IsElliptic]
    {q₁ q₂ : MvPowerSeries σ K} (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (h : thetaPointMap W h₁ hq₁0 = thetaPointMap W h₂ hq₂0) : q₁ = q₂ := by
  have hcast_inj {V V' : WeierstrassCurve (FractionRing (MvPowerSeries σ K))} (he : V = V') :
      Function.Injective
        (cast (congrArg (fun U : WeierstrassCurve _ ↦ U.toAffine.Point) he)) := by
    subst he; exact Function.injective_id
  exact W.thetaPoint_inj _ h₁ h₂ hq₁0 hq₂0
    (hcast_inj (fracCurve_def W σ (FractionRing (MvPowerSeries σ K))) h)

private theorem thetaPointMap_add_of_ne [DecidableEq (FractionRing (MvPowerSeries σ K))]
    (W : WeierstrassCurve K) [W.IsElliptic] {q₁ q₂ : MvPowerSeries σ K}
    (h₁ : constantCoeff q₁ = 0) (h₂ : constantCoeff q₂ = 0) (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (hne₁ : q₁ ≠ q₂) (hne₂ : q₁ ≠ PowerSeries.subst q₂ W.formalInverse)
    (hF : constantCoeff (subst (pairSubstitution q₁ q₂) (formalAdd W)) = 0)
    (hF0 : subst (pairSubstitution q₁ q₂) (formalAdd W) ≠ 0) :
    thetaPointMap W h₁ hq₁0 + thetaPointMap W h₂ hq₂0 = thetaPointMap W hF hF0 := by
  rw [thetaPointMap, thetaPointMap, thetaPointMap,
    ← W.thetaPoint_add_of_ne _ h₁ h₂ hq₁0 hq₂0 hne₁ hne₂ hF hF0]
  exact (point_cast_add (fracCurve_def W σ (FractionRing (MvPowerSeries σ K))) _ _).symm

/-- **An isogeny carries the parametrized point `θ(q)` to `θ(φ(q))`**, through `Hom.pointMap` on
the base-changed curve over `FractionRing (MvPowerSeries σ K)`. -/
private theorem pointMap_ofIsogeny_thetaPointMap [DecidableEq (FractionRing (MvPowerSeries σ K))]
    {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (Hom.ofIsogeny (φ.map (fracBaseHom K σ))).pointMap (thetaPointMap W₁ hq hq0) =
      thetaPointMap W₂
        (PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries)
        (subst_ne_zero_of_ne_zero hq hq0 φ.formalSeries_ne_zero) := by
  set hq' := PowerSeries.constantCoeff_subst_eq_zero hq _ φ.constantCoeff_formalSeries
  set hq'0 := subst_ne_zero_of_ne_zero hq hq0 φ.formalSeries_ne_zero
  obtain ⟨hns₁, hP⟩ := exists_thetaPointMap_eq_some W₁ hq hq0
  obtain ⟨hns₂, hQ⟩ := exists_thetaPointMap_eq_some W₂ hq' hq'0
  rw [hP, hQ, Hom.pointMap_eq_iff, Hom.tautologicalPoint_ofIsogeny,
    Isogeny.tautologicalPoint_eq_map_genericPoint, genericPoint_eq_some, Point.map_some,
    Point.equivBaseChangeSelf_some, some_sub_baseChange_mem_polePoints_iff,
    coe_pointEquivDegreeOnePlace_some]
  have hx₁ := thetaEval_genericX W₁ hq hq0
  have hy₁ := thetaEval_genericY W₁ hq hq0
  have hpt₁ : (W₁.toAffine.map (fracBaseHom K σ)).Equation
      (thetaEval W₁ hq hq0 W₁.toAffine.genericX)
      (thetaEval W₁ hq hq0 W₁.toAffine.genericY) := by
    rw [hx₁, hy₁]
    exact hns₁.1
  have hplace : CoordinateRing.pointPlace hns₁.1 = CoordinateRing.pointPlace hpt₁ := by
    rw [CoordinateRing.pointPlace_eq_iff]
    exact ⟨hx₁.symm, hy₁.symm⟩
  have hpullX : (φ.map (fracBaseHom K σ)).fieldPullback
      (W₂.toAffine.map (fracBaseHom K σ)).genericX =
      FunctionField.map W₁.toAffine (fracBaseHom K σ) (φ.fieldPullback W₂.toAffine.genericX) := by
    rw [← FunctionField.map_genericX W₂.toAffine, φ.map_fieldPullback_map]
  have hpullY : (φ.map (fracBaseHom K σ)).fieldPullback
      (W₂.toAffine.map (fracBaseHom K σ)).genericY =
      FunctionField.map W₁.toAffine (fracBaseHom K σ) (φ.fieldPullback W₂.toAffine.genericY) := by
    rw [← FunctionField.map_genericY W₂.toAffine, φ.map_fieldPullback_map]
  rw [hplace, hpullX, hpullY,
    ← thetaEval_genericX W₂ hq' hq'0, ← thetaEval_genericY W₂ hq' hq'0,
    ← thetaEval_fieldPullback φ hq hq0, ← thetaEval_fieldPullback φ hq hq0]
  exact ⟨valuation_pointPlace_map_sub_lt_one W₁.toAffine _ _ (thetaEval_comp_algebraMap W₁ hq hq0)
      hpt₁ _,
    valuation_pointPlace_map_sub_lt_one W₁.toAffine _ _ (thetaEval_comp_algebraMap W₁ hq hq0)
      hpt₁ _⟩

private theorem subst_finTwo_formalGroup_toPowerSeries (W : WeierstrassCurve K)
    {a b : MvPowerSeries σ K} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    (formalGroup W).toPowerSeries.subst ![a, b] =
      subst (pairSubstitution a b) (formalAdd W) := by
  rw [formalGroup_toPowerSeries, MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _
    (hasSubst_finTwo (.of_constantCoeff_zero ha) (.of_constantCoeff_zero hb))]
  congr 1
  funext s
  rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [pairSubstitution]

/-- If a specialization `sep` sends `a` to a nonzero series `u` and `b` to `0`, then
`θ(a) + θ(b) = θ(F(a, b))` and `F(a, b) ≠ 0`. -/
private theorem thetaPointMap_add_of_sep [DecidableEq (FractionRing (MvPowerSeries (Fin 2) K))]
    (W : WeierstrassCurve K) [W.IsElliptic] {a b : MvPowerSeries (Fin 2) K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    {u : K⟦X⟧} (hu : PowerSeries.constantCoeff u = 0) (hu0 : u ≠ 0)
    (hsa : MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → K⟦X⟧) a = u)
    (hsb : MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → K⟦X⟧) b = 0) :
    ∃ (hFc : constantCoeff ((formalGroup W).toPowerSeries.subst ![a, b]) = 0)
      (hF0 : (formalGroup W).toPowerSeries.subst ![a, b] ≠ 0),
      thetaPointMap W ha ha0 + thetaPointMap W hb hb0 = thetaPointMap W hFc hF0 := by
  let sep : Fin 2 → K⟦X⟧ := ![PowerSeries.X, 0]
  have hsep : MvPowerSeries.HasSubst sep :=
    hasSubst_finTwo PowerSeries.HasSubst.X' (.of_constantCoeff_zero' (map_zero _))
  have hab : MvPowerSeries.HasSubst ![a, b] :=
    hasSubst_finTwo (.of_constantCoeff_zero ha) (.of_constantCoeff_zero hb)
  have hFc : constantCoeff ((formalGroup W).toPowerSeries.subst ![a, b]) = 0 :=
    constantCoeff_subst_eq_zero hab (fun i ↦ by fin_cases i <;> assumption)
      (formalGroup W).zero_constantCoeff
  have hsF : MvPowerSeries.subst sep ((formalGroup W).toPowerSeries.subst ![a, b]) = u := by
    rw [subst_comp_subst_apply hab hsep]
    have hmat : (fun i : Fin 2 ↦ MvPowerSeries.subst sep (![a, b] i)) = ![u, 0] := by
      funext i; fin_cases i <;> simp [sep, hsa, hsb]
    rw [hmat]
    exact (formalGroup W).add_zero (.of_constantCoeff_zero' hu)
  have hF0 : (formalGroup W).toPowerSeries.subst ![a, b] ≠ 0 := fun h ↦ hu0 <| by
    rw [← hsF, h, ← MvPowerSeries.coe_substAlgHom hsep, map_zero]
  have hne₁ : a ≠ b := fun h ↦ hu0 (hsa ▸ h ▸ hsb)
  have hne₂ : a ≠ PowerSeries.subst b W.formalInverse := fun h ↦ by
    have hrhs : MvPowerSeries.subst sep (PowerSeries.subst b W.formalInverse) = 0 := by
      rw [MvPowerSeries.subst_powerSeriesSubst hsep (.of_constantCoeff_zero hb), hsb,
        PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalInverse]
    exact hu0 (hsa ▸ h ▸ hrhs)
  refine ⟨hFc, hF0, ?_⟩
  have hpair := subst_finTwo_formalGroup_toPowerSeries W ha hb
  have htheta : thetaPointMap W hFc hF0 = thetaPointMap W (hpair ▸ hFc) (hpair ▸ hF0) := by
    congr 1
  rw [htheta]
  exact thetaPointMap_add_of_ne W ha hb ha0 hb0 hne₁ hne₂ (hpair ▸ hFc) (hpair ▸ hF0)

end ThetaPoint

/-! ### The formal group homomorphism of an isogeny -/

section FormalGroupHom

variable {K : Type*} [Field K] {W W₁ W₂ W₃ : WeierstrassCurve K}

/-- **The formal series of an isogeny satisfies the formal-group homomorphism identity**
`φ(F₁(X, Y)) = F₂(φ(X), φ(Y))`. -/
theorem subst_formalGroup_formalSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    PowerSeries.subst (formalGroup W₁).toPowerSeries φ.formalSeries =
      subst (fun i ↦ φ.formalSeries.toMvPowerSeries i) (formalGroup W₂).toPowerSeries := by
  classical
  have : W₁.IsElliptic := φ.isElliptic
  have hX0 : constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_X 0
  have hX1 : constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_X 1
  have hX0_ne : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) ≠ 0 :=
    nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hX1_ne : (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) ≠ 0 :=
    nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  let sep : Fin 2 → K⟦X⟧ := ![PowerSeries.X, 0]
  have hsep : MvPowerSeries.HasSubst sep :=
    hasSubst_finTwo PowerSeries.HasSubst.X' (.of_constantCoeff_zero' (map_zero _))
  have hs0 : MvPowerSeries.subst sep (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) =
      PowerSeries.X := by simp [sep, subst_X hsep]
  have hs1 : MvPowerSeries.subst sep (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp [sep, subst_X hsep]
  obtain ⟨hF₁c, hF₁0, hadd₁⟩ := thetaPointMap_add_of_sep W₁ hX0 hX1 hX0_ne hX1_ne
    (PowerSeries.constantCoeff_X (R := K)) (PowerSeries.X_ne_zero (R := K)) hs0 hs1
  set q₀ : MvPowerSeries (Fin 2) K := PowerSeries.subst (MvPowerSeries.X 0) φ.formalSeries
  set q₁ : MvPowerSeries (Fin 2) K := PowerSeries.subst (MvPowerSeries.X 1) φ.formalSeries
  have hsq₀ : MvPowerSeries.subst sep q₀ = φ.formalSeries := by
    rw [MvPowerSeries.subst_powerSeriesSubst hsep (.of_constantCoeff_zero hX0), hs0,
      PowerSeries.X_subst]
  have hsq₁ : MvPowerSeries.subst sep q₁ = 0 := by
    rw [MvPowerSeries.subst_powerSeriesSubst hsep (.of_constantCoeff_zero hX1), hs1,
      PowerSeries.subst_zero_of_constantCoeff_zero φ.constantCoeff_formalSeries]
  obtain ⟨hF₂c, hF₂0, hadd₂⟩ := thetaPointMap_add_of_sep W₂
    (PowerSeries.constantCoeff_subst_eq_zero hX0 _ φ.constantCoeff_formalSeries)
    (PowerSeries.constantCoeff_subst_eq_zero hX1 _ φ.constantCoeff_formalSeries)
    (subst_ne_zero_of_ne_zero hX0 hX0_ne φ.formalSeries_ne_zero)
    (subst_ne_zero_of_ne_zero hX1 hX1_ne φ.formalSeries_ne_zero)
    φ.constantCoeff_formalSeries φ.formalSeries_ne_zero hsq₀ hsq₁
  have hpush := congrArg (Hom.ofIsogeny (φ.map (fracBaseHom K (Fin 2)))).pointMap hadd₁
  rw [Hom.pointMap_add, pointMap_ofIsogeny_thetaPointMap φ hX0 hX0_ne,
    pointMap_ofIsogeny_thetaPointMap φ hX1 hX1_ne,
    pointMap_ofIsogeny_thetaPointMap φ hF₁c hF₁0, hadd₂] at hpush
  have hinj := thetaPointMap_inj W₂ hF₂c _ hF₂0 _ hpush
  have hF₁_self : (formalGroup W₁).toPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1] =
      (formalGroup W₁).toPowerSeries := by
    have hx : (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) =
        MvPowerSeries.X := by funext i; fin_cases i <;> rfl
    rw [hx, subst_self, _root_.id]
  rw [← hF₁_self, ← hinj]
  congr 1; funext i; rw [PowerSeries.toMvPowerSeries_eq_subst]; fin_cases i <;> rfl

/-- **The formal group homomorphism induced by an isogeny** `φ : W₁ → W₂`, sending the parameter
`z₁ = -x₁ / y₁` to `φ.formalSeries`. -/
noncomputable def formalGroupHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := φ.formalSeries
  zero_constantCoeff := φ.constantCoeff_formalSeries
  hom := φ.subst_formalGroup_formalSeries

/-- The underlying power series of `φ.formalGroupHom` is `φ.formalSeries`. -/
@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries :=
  (rfl)

/-- The identity isogeny induces the identity formal group homomorphism. -/
@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Isogeny.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext : 1
  rw [formalGroupHom_toPowerSeries, FormalGroupHom.id_toPowerSeries, formalSeries_id]

/-- Composition of isogenies induces composition of formal group homomorphisms. -/
@[simp]
theorem formalGroupHom_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (ψ : Isogeny W₂.toAffine W₃.toAffine) (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).formalGroupHom = ψ.formalGroupHom.comp φ.formalGroupHom := by
  ext : 1
  rw [formalGroupHom_toPowerSeries, FormalGroupHom.comp_toPowerSeries,
    formalGroupHom_toPowerSeries, formalGroupHom_toPowerSeries, φ.formalSeries_comp ψ]

/-- **Isogenous elliptic curves have formal groups with the same `n`-series order.** -/
theorem order_nsmulSeries_formalGroup_eq [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (n : ℕ) :
    ((formalGroup W₁).nsmulSeries n).order = ((formalGroup W₂).nsmulSeries n).order :=
  φ.formalGroupHom.order_nsmulSeries_eq φ.formalSeries_ne_zero n

/-- **Isogenous elliptic curves have formal groups of the same height.** -/
theorem height_formalGroup_eq [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (p : ℕ) :
    (formalGroup W₁).height p = (formalGroup W₂).height p :=
  φ.formalGroupHom.height_eq φ.formalSeries_ne_zero p

/-! ### Addition of isogenies in `Hom` -/

private theorem point_ext {F : FormalGroup K} {σ : Type*} {x y : F.Point σ}
    (h : x.val = y.val) : x = y :=
  Subtype.ext h

/-- On `Fin 2`, the formal-group chord series `F(X 0, X 1)` and `F(X 0, ι(X 1))` are distinct,
because `W.formalInverse ≠ X`. -/
private theorem formalGroup_finTwo_add_ne_sub (W : WeierstrassCurve K) [W.IsElliptic] :
    (formalGroup W).toPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1] ≠
      (formalGroup W).toPowerSeries.subst
        ![MvPowerSeries.X 0,
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) W.formalInverse] := by
  let x₀ : (formalGroup W).Point (Fin 2) := ⟨MvPowerSeries.X 0, PowerSeries.HasSubst.X 0⟩
  let x₁ : (formalGroup W).Point (Fin 2) := ⟨MvPowerSeries.X 1, PowerSeries.HasSubst.X 1⟩
  intro h
  have hpt : x₀ + x₁ = x₀ + -x₁ := by
    apply point_ext
    rw [FormalGroup.add_apply, FormalGroup.add_apply, FormalGroup.neg_apply, formalGroup_addInvX]
    exact h
  have hx₁_eq : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      PowerSeries.subst (MvPowerSeries.X 1) W.formalInverse := by
    have hc : x₁ = -x₁ := add_left_cancel hpt
    have hc' := congrArg Subtype.val hc
    rwa [FormalGroup.neg_apply, formalGroup_addInvX] at hc'
  let sep₁ : Fin 2 → K⟦X⟧ := ![0, PowerSeries.X]
  have hsep₁ : MvPowerSeries.HasSubst sep₁ :=
    hasSubst_finTwo (.of_constantCoeff_zero' (map_zero _)) PowerSeries.HasSubst.X'
  have hs := congrArg (MvPowerSeries.subst sep₁) hx₁_eq
  rw [MvPowerSeries.subst_powerSeriesSubst hsep₁ (.of_constantCoeff_zero (constantCoeff_X 1))]
    at hs
  have hs1 : MvPowerSeries.subst sep₁ (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      PowerSeries.X := by simp [sep₁, subst_X hsep₁]
  rw [hs1, PowerSeries.X_subst] at hs
  exact formalInverse_ne_X W hs.symm

/-- Formal-group identity `(X 0 +_F X 1) +_F (X 0 -_F X 1) = X 0 +_F X 0` on `Fin 2`. -/
private theorem formalGroup_finTwo_add_add_sub (W : WeierstrassCurve K) :
    (formalGroup W).toPowerSeries.subst
      ![(formalGroup W).toPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1],
        (formalGroup W).toPowerSeries.subst
          ![MvPowerSeries.X 0,
            PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) W.formalInverse]] =
      (formalGroup W).toPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 0] := by
  let x₀ : (formalGroup W).Point (Fin 2) := ⟨MvPowerSeries.X 0, PowerSeries.HasSubst.X 0⟩
  let x₁ : (formalGroup W).Point (Fin 2) := ⟨MvPowerSeries.X 1, PowerSeries.HasSubst.X 1⟩
  have hpt : (x₀ + x₁) + (x₀ + -x₁) = x₀ + x₀ := by abel
  have hval := congrArg Subtype.val hpt
  rw [FormalGroup.add_apply, FormalGroup.add_apply, FormalGroup.add_apply, FormalGroup.add_apply,
    FormalGroup.neg_apply, formalGroup_addInvX] at hval
  exact hval

/-- On `Fin 2`, if `ofIsogeny ψ = id + id`, then
`θ(F(X 0, X 1)) + θ(F(X 0, ι(X 1))) = θ(ψ(X 0))`. -/
private theorem exists_thetaPointMap_chord_double
    [DecidableEq (FractionRing (MvPowerSeries (Fin 2) K))]
    (W : WeierstrassCurve K) [W.IsElliptic] (ψ : Isogeny W.toAffine W.toAffine)
    (hψ : Hom.ofIsogeny ψ = Hom.id W.toAffine + Hom.id W.toAffine) :
    let A : MvPowerSeries (Fin 2) K :=
      (formalGroup W).toPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1]
    let B : MvPowerSeries (Fin 2) K :=
      (formalGroup W).toPowerSeries.subst
        ![MvPowerSeries.X 0, PowerSeries.subst (MvPowerSeries.X 1) W.formalInverse]
    ∃ (hAc : constantCoeff A = 0) (hA0 : A ≠ 0) (hBc : constantCoeff B = 0) (hB0 : B ≠ 0),
      thetaPointMap W hAc hA0 + thetaPointMap W hBc hB0 =
        thetaPointMap W
          (PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X 0) _
            ψ.constantCoeff_formalSeries)
          (subst_ne_zero_of_ne_zero (constantCoeff_X 0)
            (nonZeroDivisors.ne_zero X_mem_nonZeroDivisors) ψ.formalSeries_ne_zero) := by
  intro A B
  have hX0 : constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_X 0
  have hX1 : constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    constantCoeff_X 1
  have hX0_ne : (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) ≠ 0 :=
    nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hX1_ne : (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) ≠ 0 :=
    nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  let sep : Fin 2 → K⟦X⟧ := ![PowerSeries.X, 0]
  have hsep : MvPowerSeries.HasSubst sep :=
    hasSubst_finTwo PowerSeries.HasSubst.X' (.of_constantCoeff_zero' (map_zero _))
  have hs0 : MvPowerSeries.subst sep (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) =
      PowerSeries.X := by simp [sep, subst_X hsep]
  have hs1 : MvPowerSeries.subst sep (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp [sep, subst_X hsep]
  set qn : MvPowerSeries (Fin 2) K := PowerSeries.subst (MvPowerSeries.X 1) W.formalInverse
  have hnx₁c : constantCoeff qn = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hX1 _ W.constantCoeff_formalInverse
  have hnx₁0 : qn ≠ 0 := subst_ne_zero_of_ne_zero hX1 hX1_ne
    (formalSeries_negIsogeny W ▸ (negIsogeny W.toAffine).formalSeries_ne_zero)
  have hsnx₁ : MvPowerSeries.subst sep qn = 0 := by
    rw [MvPowerSeries.subst_powerSeriesSubst hsep (.of_constantCoeff_zero hX1), hs1,
      PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalInverse]
  obtain ⟨hAc, hA0, hQ_add⟩ := thetaPointMap_add_of_sep W hX0 hX1 hX0_ne hX1_ne
    (PowerSeries.constantCoeff_X (R := K)) (PowerSeries.X_ne_zero (R := K)) hs0 hs1
  obtain ⟨hBc, hB0, hQ_sub⟩ := thetaPointMap_add_of_sep W hX0 hnx₁c hX0_ne hnx₁0
    (PowerSeries.constantCoeff_X (R := K)) (PowerSeries.X_ne_zero (R := K)) hs0 hsnx₁
  have hQ_neg : -thetaPointMap W hX1 hX1_ne = thetaPointMap W hnx₁c hnx₁0 :=
    (thetaPointMap_neg W hX1 hX1_ne hnx₁c hnx₁0).symm
  refine ⟨hAc, hA0, hBc, hB0, ?_⟩
  have hab : (thetaPointMap W hX0 hX0_ne + thetaPointMap W hX1 hX1_ne) +
      (thetaPointMap W hX0 hX0_ne + -thetaPointMap W hX1 hX1_ne) =
      thetaPointMap W hX0 hX0_ne + thetaPointMap W hX0 hX0_ne := by abel
  rw [← hQ_add, ← hQ_sub, ← hQ_neg, hab,
    ← pointMap_ofIsogeny_thetaPointMap ψ hX0 hX0_ne, ← Hom.ofIsogeny_map, hψ,
    Hom.map_add, Hom.id_map, Hom.add_pointMap, Hom.id_pointMap]

/-- Two series `a, b` with zero constant coefficient that are not formal-group opposites substitute
into `formalAdd W` to a nonzero series with zero constant coefficient. -/
private theorem constantCoeff_and_ne_zero_subst_formalAdd {σ : Type*}
    (W : WeierstrassCurve K) {a b : MvPowerSeries σ K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (hne : a ≠ PowerSeries.subst b W.formalInverse) :
    constantCoeff (subst (pairSubstitution a b) (formalAdd W)) = 0 ∧
      subst (pairSubstitution a b) (formalAdd W) ≠ 0 := by
  rw [← subst_finTwo_formalGroup_toPowerSeries W ha hb]
  refine ⟨constantCoeff_subst_eq_zero
    (hasSubst_finTwo (.of_constantCoeff_zero ha) (.of_constantCoeff_zero hb))
    (fun i ↦ by fin_cases i <;> assumption) (formalGroup W).zero_constantCoeff, fun h0 ↦ ?_⟩
  have hinv := ((formalGroup W).eq_subst_addInvX_iff_subst_right_eq_zero
    (.of_constantCoeff_zero ha) (.of_constantCoeff_zero hb)).mpr h0
  have hinv' := congrArg (fun u ↦ PowerSeries.subst u (formalGroup W).addInvX) hinv
  rw [← PowerSeries.subst_comp_subst_apply (formalGroup W).hasSubst_addInvX
      (.of_constantCoeff_zero ha),
    (formalGroup W).subst_addInvX_addInvX, PowerSeries.subst_X (.of_constantCoeff_zero ha),
    formalGroup_addInvX] at hinv'
  exact hne hinv'.symm

/-- Doubling the identity endomorphism expands to the formal-group doubling `F(X, X)`. Computed
without a tangent chord formula via `(Q₀ + Q₁) + (Q₀ - Q₁) = Q₀ + Q₀` on `Fin 2`. -/
private theorem exists_ofIsogeny_eq_id_add_id_formalSeries (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ ψ : Isogeny W.toAffine W.toAffine,
      Hom.id W.toAffine + Hom.id W.toAffine = Hom.ofIsogeny ψ ∧
        ψ.formalSeries = (formalGroup W).toPowerSeries.subst ![PowerSeries.X, PowerSeries.X] := by
  classical
  set d := Hom.id W.toAffine + Hom.id W.toAffine
  have hd0 : d ≠ 0 := by
    have hd2 : d = (2 : ℤ) • Hom.id W.toAffine := (two_zsmul _).symm
    rw [hd2, ← zero_zsmul (Hom.id W.toAffine)]
    exact fun h ↦ absurd (Hom.zsmul_id_injective h) (by decide)
  obtain ⟨ψ, hψ⟩ := (Hom.eq_zero_or_exists_ofIsogeny d).resolve_left hd0
  refine ⟨ψ, hψ, ?_⟩
  set A : MvPowerSeries (Fin 2) K :=
    (formalGroup W).toPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 1]
  set B : MvPowerSeries (Fin 2) K :=
    (formalGroup W).toPowerSeries.subst
      ![MvPowerSeries.X 0, PowerSeries.subst (MvPowerSeries.X 1) W.formalInverse]
  obtain ⟨hAc, hA0, hBc, hB0, hsum_curve⟩ := exists_thetaPointMap_chord_double W ψ hψ.symm
  have hAB_inv_ne : A ≠ PowerSeries.subst B W.formalInverse := fun h ↦ by
    have hc' : constantCoeff (PowerSeries.subst B W.formalInverse) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hBc _ W.constantCoeff_formalInverse
    have h0' : PowerSeries.subst B W.formalInverse ≠ 0 := h ▸ hA0
    have hsame : thetaPointMap W hAc hA0 = thetaPointMap W hc' h0' := by congr 1
    rw [hsame, thetaPointMap_neg W hBc hB0 hc' h0', neg_add_cancel] at hsum_curve
    exact thetaPointMap_ne_zero W _ _ hsum_curve.symm
  have hFAB_eq : subst (pairSubstitution A B) (formalAdd W) =
      (formalGroup W).toPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.X 0] := by
    rw [← subst_finTwo_formalGroup_toPowerSeries W hAc hBc]
    exact formalGroup_finTwo_add_add_sub W
  obtain ⟨hFABc, hFAB0⟩ := constantCoeff_and_ne_zero_subst_formalAdd W hAc hBc hAB_inv_ne
  have hQ_total := thetaPointMap_add_of_ne W hAc hBc hA0 hB0 (formalGroup_finTwo_add_ne_sub W)
    hAB_inv_ne hFABc hFAB0
  have hval_eq := thetaPointMap_inj W hFABc _ hFAB0 _ (hQ_total.symm.trans hsum_curve)
  rw [hFAB_eq] at hval_eq
  let sep : Fin 2 → K⟦X⟧ := ![PowerSeries.X, 0]
  have hsep : MvPowerSeries.HasSubst sep :=
    hasSubst_finTwo PowerSeries.HasSubst.X' (.of_constantCoeff_zero' (map_zero _))
  have hs0 : MvPowerSeries.subst sep (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) =
      PowerSeries.X := by simp [sep, subst_X hsep]
  have hfin := congrArg (MvPowerSeries.subst sep) hval_eq.symm
  rw [MvPowerSeries.subst_powerSeriesSubst hsep (.of_constantCoeff_zero (constantCoeff_X 0)),
    hs0, PowerSeries.X_subst,
    subst_comp_subst_apply (hasSubst_finTwo (PowerSeries.HasSubst.X 0) (PowerSeries.HasSubst.X 0))
      hsep] at hfin
  have hmat : (fun i : Fin 2 ↦ MvPowerSeries.subst sep
        (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] i)) =
      ![PowerSeries.X, PowerSeries.X] := by
    funext i; fin_cases i <;> simp [hs0]
  rwa [hmat] at hfin

/-- Generic case of `formalSeries_eq_subst_of_ofIsogeny_add_eq` for two distinct isogenies. -/
private theorem formalSeries_eq_subst_of_ofIsogeny_add_eq_of_ne [W₂.IsElliptic]
    {φ ψ χ : Isogeny W₁.toAffine W₂.toAffine} (heq : φ ≠ ψ)
    (hχ : Hom.ofIsogeny φ + Hom.ofIsogeny ψ = Hom.ofIsogeny χ) :
    χ.formalSeries =
      (formalGroup W₂).toPowerSeries.subst ![φ.formalSeries, ψ.formalSeries] := by
  classical
  have : W₁.IsElliptic := φ.isElliptic
  have hX : constantCoeff (PowerSeries.X : K⟦X⟧) = 0 := PowerSeries.constantCoeff_X
  have hX0 : (PowerSeries.X : K⟦X⟧) ≠ 0 := PowerSeries.X_ne_zero
  set q₁ : MvPowerSeries Unit K := PowerSeries.subst (PowerSeries.X : K⟦X⟧) φ.formalSeries
  set q₂ : MvPowerSeries Unit K := PowerSeries.subst (PowerSeries.X : K⟦X⟧) ψ.formalSeries
  have hne₁ : q₁ ≠ q₂ := by
    simp only [q₁, q₂, PowerSeries.X_subst, Ne, formalSeries_inj]
    exact heq
  have hne₂ : q₁ ≠ PowerSeries.subst q₂ W₂.formalInverse := by
    simp only [q₁, q₂, PowerSeries.X_subst, ← formalSeries_negIsogeny W₂,
      ← ψ.formalSeries_comp (negIsogeny W₂.toAffine), Ne, formalSeries_inj]
    intro hφ
    apply Hom.ofIsogeny_ne_zero χ
    rw [← hχ, hφ, ← Hom.neg_ofIsogeny, neg_add_cancel]
  have hcurve :
      (Hom.ofIsogeny (φ.map (fracBaseHom K Unit))).pointMap (thetaPointMap W₁ hX hX0) +
        (Hom.ofIsogeny (ψ.map (fracBaseHom K Unit))).pointMap (thetaPointMap W₁ hX hX0) =
        (Hom.ofIsogeny (χ.map (fracBaseHom K Unit))).pointMap (thetaPointMap W₁ hX hX0) := by
    rw [← Hom.ofIsogeny_map, ← Hom.ofIsogeny_map, ← Hom.ofIsogeny_map,
      ← Hom.add_pointMap, ← Hom.map_add, hχ]
  rw [pointMap_ofIsogeny_thetaPointMap φ hX hX0, pointMap_ofIsogeny_thetaPointMap ψ hX hX0,
    pointMap_ofIsogeny_thetaPointMap χ hX hX0] at hcurve
  have hq₁c : constantCoeff q₁ = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hX _ φ.constantCoeff_formalSeries
  have hq₂c : constantCoeff q₂ = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hX _ ψ.constantCoeff_formalSeries
  obtain ⟨hFc, hF0⟩ := constantCoeff_and_ne_zero_subst_formalAdd W₂ hq₁c hq₂c hne₂
  have hadd := thetaPointMap_add_of_ne W₂ hq₁c hq₂c
    (subst_ne_zero_of_ne_zero hX hX0 φ.formalSeries_ne_zero)
    (subst_ne_zero_of_ne_zero hX hX0 ψ.formalSeries_ne_zero) hne₁ hne₂ hFc hF0
  rw [hcurve] at hadd
  have hinj := thetaPointMap_inj W₂
    (PowerSeries.constantCoeff_subst_eq_zero hX _ χ.constantCoeff_formalSeries) hFc
    (subst_ne_zero_of_ne_zero hX hX0 χ.formalSeries_ne_zero) hF0 hadd
  rw [← PowerSeries.X_subst (f := χ.formalSeries)]
  exact hinj.trans ((subst_finTwo_formalGroup_toPowerSeries W₂ hq₁c hq₂c).symm.trans <| by
    simp [q₁, q₂, PowerSeries.X_subst])

/-- **Addition of isogenies in `Hom` induces formal-group addition of their formal series**:
if `ofIsogeny φ + ofIsogeny ψ = ofIsogeny χ`, then
`χ.formalSeries = F₂(φ.formalSeries, ψ.formalSeries)`. -/
theorem formalSeries_eq_subst_of_ofIsogeny_add_eq [W₂.IsElliptic]
    {φ ψ χ : Isogeny W₁.toAffine W₂.toAffine}
    (h : Hom.ofIsogeny φ + Hom.ofIsogeny ψ = Hom.ofIsogeny χ) :
    χ.formalSeries =
      (formalGroup W₂).toPowerSeries.subst ![φ.formalSeries, ψ.formalSeries] := by
  by_cases heq : φ = ψ
  · subst heq
    obtain ⟨δ, hδ, hδs⟩ := exists_ofIsogeny_eq_id_add_id_formalSeries W₂
    have hχ : χ = δ.comp φ := Hom.ofIsogeny_injective <| by
      rw [← h, ← Hom.ofIsogeny_comp_ofIsogeny, ← hδ, Hom.add_comp, Hom.id_comp]
    rw [hχ, φ.formalSeries_comp δ, hδs, PowerSeries.subst_def,
      subst_comp_subst_apply
        (PowerSeries.hasSubst_pair PowerSeries.constantCoeff_X PowerSeries.constantCoeff_X)
        (hasSubst_of_constantCoeff_zero fun _ : Unit ↦ φ.constantCoeff_formalSeries)]
    congr 1
    funext i
    fin_cases i <;>
      simp [← PowerSeries.subst_def,
        PowerSeries.subst_X (.of_constantCoeff_zero' φ.constantCoeff_formalSeries)]
  · exact formalSeries_eq_subst_of_ofIsogeny_add_eq_of_ne heq h

end FormalGroupHom

end TauCeti.Isogeny
