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
public import TauCeti.RingTheory.FormalGroup.Hom.Basic
public import TauCeti.RingTheory.FormalGroup.ZSMul
-- Proof-only: rational-function congruences at affine point places.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Place
-- Proof-only: `w(q) ≠ 0` in the fraction field of multivariate power series.
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
-- Proof-only: `constantCoeff_subst_pair_formalAdd`.
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
-- Proof-only: Laurent expansion of the generic coordinates in terms of `formalW`.
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Isogeny.Differential
-- Proof-only: morphisms act additively on points over every field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
-- Proof-only: the source of an isogeny to an elliptic curve is elliptic.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
-- Proof-only: `[n] = n • id` in `Hom W W`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
-- Proof-only: equivalence of projective point representatives and affine points.
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
-- Proof-only: the Bosma–Lenstra addition law at formal parameters.
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.FormalPoint
-- Proof-only: multivariate power series over a domain form a domain.
import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors
-- Proof-only: `subst_rename` on multivariate power series.
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# Formal group homomorphisms and additive formal series of elliptic curve morphisms

Let `W₁` and `W₂` be elliptic Weierstrass curves over a field `K`. Expanding the pulled-back
formal parameter `-x₂ / y₂` at infinity attaches to each isogeny `φ : W₁ → W₂` a formal power
series `φ.formalSeries ∈ K⟦X⟧` (`TauCeti.Isogeny.formalSeries`). Extending this assignment by `0`
on the zero morphism gives `TauCeti.Isogeny.Hom.formalSeries` on the full additive group
`Hom W₁.toAffine W₂.toAffine`.

This file proves two compatibilities between the group laws of `W₁` and `W₂` and the formal group
laws `formalGroup W₁` and `formalGroup W₂`:

1. **Additivity in the morphism (`Hom.formalSeries_add`).** Specialising the Bosma–Lenstra formal
   addition identity `WeierstrassCurve.dblAddXYZ_formalW_eq_smul` along any pair of parameters
   `(q₁, q₂)` with zero constant term identifies formal-group addition on `formalGroup W₂` with
   point addition on `W₂` over the fraction field of the power-series ring, with no case splits on
   coinciding or opposite parameters. Reading the tautological point of `f : Hom W₁ W₂` in
   `K⸨X⸩` therefore turns `Hom.formalSeries` into an additive homomorphism
   `Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit`
   (`TauCeti.Isogeny.Hom.formalSeriesPointHom`). In particular, negation is `formalInverse` and
   multiplication by `n : ℤ` has formal series `(formalGroup W).zsmulSeries n`
   (`TauCeti.Isogeny.formalSeries_mulByIntIsogeny`).
2. **The formal group homomorphism of an isogeny (`Isogeny.formalGroupHom`).** Evaluating `φ` over
   the fraction field of `MvPowerSeries (Fin 2) K` at the generic formal parameters `X 0`, `X 1`,
   and `(formalGroup W₁).toPowerSeries`, where `(φ.map ι).pointMap` is additive by
   `TauCeti.Isogeny.Hom.pointMap_add`, shows that `φ.formalSeries` satisfies the homomorphism
   equation `φ(F₁(X, Y)) = F₂(φ(X), φ(Y))`, packaging every isogeny and morphism as a bundled
   `TauCeti.FormalGroupHom`.

## Main definitions

* `TauCeti.Isogeny.Hom.formalSeries`: the formal series of a morphism (`0` on `0`, `φ.formalSeries`
  on `ofIsogeny φ`).
* `TauCeti.Isogeny.Hom.formalSeriesPointHom`: `Hom W₁.toAffine W₂.toAffine →+
  (formalGroup W₂).Point Unit`.
* `TauCeti.Isogeny.formalGroupHom` and `TauCeti.Isogeny.Hom.formalGroupHom`: the bundled
  `FormalGroupHom (formalGroup W₁) (formalGroup W₂)` induced by an isogeny or morphism.

## Main results

* `TauCeti.Isogeny.formalSeries_injective` and `TauCeti.Isogeny.Hom.formalSeries_injective`: an
  isogeny or morphism is determined by its formal series.
* `TauCeti.Isogeny.Hom.formalSeries_add`, `formalSeries_neg`, `formalSeries_nsmul`,
  `formalSeries_zsmul`: compatibility of `Hom.formalSeries` with the group operations on `Hom`.
* `TauCeti.Isogeny.formalSeries_negIsogeny`: `[-1]` has formal series `W.formalInverse`.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny` and
  `TauCeti.Isogeny.formalSeries_mulByIntIsogeny_natCast`: `[n]` has formal series
  `(formalGroup W).zsmulSeries n` (and `(formalGroup W).nsmulSeries n` for `n : ℕ`).
* `TauCeti.Isogeny.subst_formalGroup_formalSeries`: `φ(F₁(X, Y)) = F₂(φ(X), φ(Y))`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, IV.2, and IV.4.
-/

public section

open MvPowerSeries Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped LaurentSeries PowerSeries Polynomial.Bivariate

namespace TauCeti

section ParamPoint

variable {K : Type*} [Field K] (W : WeierstrassCurve K) {σ : Type*}

private theorem subst_formalGroup_eq_subst_pair {q₁ q₂ : MvPowerSeries σ K}
    (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0) :
    subst ![q₁, q₂] (formalGroup W).toPowerSeries =
      subst (pairSubstitution q₁ q₂) (formalAdd W) := by
  have h12 : HasSubst ![q₁, q₂] := hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i
    · exact hq₁
    · exact hq₂
  rw [formalGroup_toPowerSeries, MvPowerSeries.subst_rename _ _ h12]
  congr 1
  funext s
  rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [pairSubstitution]

private theorem dblAddXYZ_formalW_subst_pair {q₁ q₂ : MvPowerSeries σ K}
    (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0) :
    let P₁ : Fin 3 → MvPowerSeries σ K := ![q₁, -1, PowerSeries.subst q₁ W.formalW]
    let P₂ : Fin 3 → MvPowerSeries σ K := ![q₂, -1, PowerSeries.subst q₂ W.formalW]
    let F₁₂ : MvPowerSeries σ K := subst ![q₁, q₂] (formalGroup W).toPowerSeries
    IsUnit ((W.toProjective.map (algebraMap K (MvPowerSeries σ K))).dblAddY P₁ P₂) ∧
      (W.toProjective.map (algebraMap K (MvPowerSeries σ K))).dblAddXYZ P₁ P₂ =
        -((W.toProjective.map (algebraMap K (MvPowerSeries σ K))).dblAddY P₁ P₂) •
          ![F₁₂, -1, PowerSeries.subst F₁₂ W.formalW] := by
  set S := substAlgHom (R := K) (hasSubst_pair hq₁ hq₂)
  have hS : (S : MvPowerSeries (Unit ⊕ Unit) K →+* MvPowerSeries σ K).comp
      (algebraMap K _) = algebraMap K _ := S.comp_algebraMap
  have hcurve :
      (W.toProjective.map (algebraMap K (MvPowerSeries (Unit ⊕ Unit) K))).map S.toRingHom =
        W.toProjective.map (algebraMap K (MvPowerSeries σ K)) := by
    refine (W.map_map _ _).trans ?_
    rw [AlgHom.toRingHom_eq_coe, hS]
  have hpt (r : MvPowerSeries (Unit ⊕ Unit) K) (hr : constantCoeff r = 0) :
      S.toRingHom ∘ ![r, -1, PowerSeries.subst r W.formalW] =
        ![S r, -1, PowerSeries.subst (S r) W.formalW] := by
    funext k; fin_cases k
    · rfl
    · simp
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Fin.reduceFinMk, Function.comp_apply, Fin.isValue, Matrix.cons_val, PowerSeries.subst_def]
      rw [coe_substAlgHom,
        subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ ↦ hr) (hasSubst_pair hq₁ hq₂)]
  have h₁ := hpt (X (Sum.inl ())) (constantCoeff_X _)
  rw [coe_substAlgHom, subst_X (hasSubst_pair hq₁ hq₂), pairSubstitution, Sum.elim_inl] at h₁
  have h₂ := hpt (X (Sum.inr ())) (constantCoeff_X _)
  rw [coe_substAlgHom, subst_X (hasSubst_pair hq₁ hq₂), pairSubstitution, Sum.elim_inr] at h₂
  have hF₁₂ : subst ![q₁, q₂] (formalGroup W).toPowerSeries = S (formalAdd W) := by
    rw [coe_substAlgHom, ← subst_formalGroup_eq_subst_pair W hq₁ hq₂]
  have hF := hpt (formalAdd W) W.constantCoeff_formalAdd
  rw [← hF₁₂] at hF
  refine ⟨?_, ?_⟩
  · rw [← h₁, ← h₂, ← hcurve, Projective.map_dblAddY]
    exact W.isUnit_dblAddY_formalW.map S.toRingHom
  · rw [← h₁, ← h₂, ← hF, ← hcurve, Projective.map_dblAddXYZ, Projective.map_dblAddY,
      W.dblAddXYZ_formalW_eq_smul]
    funext k
    fin_cases k <;> simp

variable {KK : Type*} [Field KK] [Algebra (MvPowerSeries σ K) KK]

/-- The projective coordinate triple `[q : -1 : w(q)]` in `KK` attached to a series `q`. -/
private noncomputable def paramVec (q : MvPowerSeries σ K) : Fin 3 → KK :=
  algebraMap (MvPowerSeries σ K) KK ∘ ![q, -1, PowerSeries.subst q W.formalW]

variable [Algebra K KK]

/-- The affine point on `W⁄KK` represented by `[q : -1 : w(q)]`. -/
private noncomputable def paramPoint (q : MvPowerSeries σ K) : (W⁄KK).toAffine.Point :=
  Projective.Point.toAffine (W⁄KK).toProjective (paramVec (KK := KK) W q)

private theorem paramPoint_zero : paramPoint (KK := KK) W (0 : MvPowerSeries σ K) = 0 := by
  refine Projective.Point.toAffine_of_Z_eq_zero ?_
  simp [paramVec, PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalW]

variable [W.IsElliptic] [IsScalarTower K (MvPowerSeries σ K) KK]

private theorem nonsingular_paramVec {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) :
    (W⁄KK).toProjective.Nonsingular (paramVec (KK := KK) W q) := by
  refine (Projective.equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero (W⁄KK).isUnit_Δ.ne_zero
    fun h ↦ by simpa [paramVec] using congrFun h 1).mp ?_
  have hmap : W⁄KK =
      (W.map (algebraMap K (MvPowerSeries σ K))).map (algebraMap (MvPowerSeries σ K) KK) := by
    rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]
    rfl
  rw [hmap]
  exact ((W.toProjective.equation_neg_one_iff_wEquation q _).mpr
    (W.subst_formalW_wEquation (.of_constantCoeff_zero hq))).map _

section FractionRing

variable [IsFractionRing (MvPowerSeries σ K) KK]

private theorem paramPoint_eq_some {q : MvPowerSeries σ K} (hq : constantCoeff q = 0)
    (hq0 : q ≠ 0) :
    ∃ h : (W⁄KK).toAffine.Nonsingular
        (algebraMap (MvPowerSeries σ K) KK q /
          algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q W.formalW))
        (-1 / algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q W.formalW)),
      paramPoint (KK := KK) W q = .some _ _ h := by
  have hz : paramVec (KK := KK) W q 2 ≠ 0 := by
    simpa [paramVec] using W.algebraMap_subst_formalW_ne_zero (KK := KK) hq hq0
  have hN := nonsingular_paramVec (KK := KK) W hq
  refine ⟨by simpa [paramVec] using (Projective.nonsingular_of_Z_ne_zero hz).mp hN, ?_⟩
  rw [paramPoint, Projective.Point.toAffine_of_Z_ne_zero hN hz]
  simp [paramVec]

private theorem paramPoint_injective {q₁ q₂ : MvPowerSeries σ K}
    (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0)
    (h : paramPoint (KK := KK) W q₁ = paramPoint (KK := KK) W q₂) : q₁ = q₂ := by
  rcases eq_or_ne q₁ 0 with rfl | hq₁0
  · rcases eq_or_ne q₂ 0 with rfl | hq₂0
    · rfl
    · obtain ⟨_, h₂⟩ := paramPoint_eq_some (KK := KK) W hq₂ hq₂0
      rw [paramPoint_zero, h₂] at h
      cases h
  · rcases eq_or_ne q₂ 0 with rfl | hq₂0
    · obtain ⟨_, h₁⟩ := paramPoint_eq_some (KK := KK) W hq₁ hq₁0
      rw [h₁, paramPoint_zero] at h
      cases h
    · obtain ⟨_, h₁⟩ := paramPoint_eq_some (KK := KK) W hq₁ hq₁0
      obtain ⟨_, h₂⟩ := paramPoint_eq_some (KK := KK) W hq₂ hq₂0
      rw [h₁, h₂, Point.some.injEq] at h
      have hw₁ : algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q₁ W.formalW) ≠ 0 :=
        W.algebraMap_subst_formalW_ne_zero hq₁ hq₁0
      have hw₂ : algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q₂ W.formalW) ≠ 0 :=
        W.algebraMap_subst_formalW_ne_zero hq₂ hq₂0
      have hw : algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q₁ W.formalW) =
          algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q₂ W.formalW) := by
        have hy := h.2
        rw [div_eq_div_iff hw₁ hw₂] at hy
        linear_combination hy
      have hq : algebraMap (MvPowerSeries σ K) KK q₁ =
          algebraMap (MvPowerSeries σ K) KK q₂ := by
        have hx := h.1
        rwa [hw, div_left_inj₀ hw₂] at hx
      exact IsFractionRing.injective (MvPowerSeries σ K) KK hq

end FractionRing

/-- Specialising `dblAddXYZ_formalW_eq_smul` along `(q₁, q₂)` identifies formal-group addition on
`formalGroup W` with point addition on `W⁄KK` unconditionally. -/
private theorem paramPoint_subst_formalGroup [DecidableEq KK] {q₁ q₂ : MvPowerSeries σ K}
    (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0) :
    paramPoint (KK := KK) W (subst ![q₁, q₂] (formalGroup W).toPowerSeries) =
      paramPoint (KK := KK) W q₁ + paramPoint (KK := KK) W q₂ := by
  obtain ⟨hu, hdbl⟩ := dblAddXYZ_formalW_subst_pair W hq₁ hq₂
  set P₁ : Fin 3 → MvPowerSeries σ K := ![q₁, -1, PowerSeries.subst q₁ W.formalW]
  set P₂ : Fin 3 → MvPowerSeries σ K := ![q₂, -1, PowerSeries.subst q₂ W.formalW]
  set F₁₂ : MvPowerSeries σ K := subst ![q₁, q₂] (formalGroup W).toPowerSeries
  set ρ := algebraMap (MvPowerSeries σ K) KK
  have hcurveK : (W.toProjective.map (algebraMap K (MvPowerSeries σ K))).map ρ =
      (W⁄KK).toProjective := by
    rw [Projective.map, Projective.map, WeierstrassCurve.map_map,
      ← IsScalarTower.algebraMap_eq, ← WeierstrassCurve.baseChange, toProjective]
  have hdblK : (W⁄KK).toProjective.dblAddXYZ (paramVec (KK := KK) W q₁)
      (paramVec (KK := KK) W q₂) =
        (-ρ ((W.toProjective.map (algebraMap K (MvPowerSeries σ K))).dblAddY P₁ P₂)) •
          paramVec (KK := KK) W F₁₂ := by
    rw [← hcurveK, paramVec, paramVec,
      Projective.map_dblAddXYZ (W' := W.toProjective.map (algebraMap K (MvPowerSeries σ K)))
        ρ P₁ P₂, hdbl]
    funext k; fin_cases k <;> simp [paramVec, ρ]
  have huK : IsUnit (-ρ ((W.toProjective.map (algebraMap K (MvPowerSeries σ K))).dblAddY P₁ P₂)) :=
    (hu.map ρ).neg
  have hN₁ := nonsingular_paramVec (KK := KK) W hq₁
  have hN₂ := nonsingular_paramVec (KK := KK) W hq₂
  have h0 : (W⁄KK).toProjective.dblAddXYZ (paramVec (KK := KK) W q₁)
      (paramVec (KK := KK) W q₂) ≠ 0 := by
    rw [hdblK]; intro h; exact huK.ne_zero (by simpa [paramVec] using congrFun h 1)
  have heq1 := Projective.dblAddXYZ_equiv_add hN₁ hN₂ h0
  have heq2 := Projective.smul_equiv (paramVec (KK := KK) W F₁₂) huK
  rw [← hdblK] at heq2
  rw [paramPoint, ← Projective.Point.toAffine_of_equiv heq2,
    Projective.Point.toAffine_of_equiv heq1, Projective.Point.toAffine_add hN₁ hN₂,
    paramPoint, paramPoint]

end ParamPoint

namespace Isogeny

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

section LiftLaurentSubst

/-- Substituting a nonzero series `q` with zero constant coefficient into a nonzero univariate
power series over a field produces a nonzero multivariate power series. -/
private theorem subst_ne_zero_of_ne_zero {σ : Type*} {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) {f : K⟦X⟧} (hf : f ≠ 0) :
    PowerSeries.subst q f ≠ 0 := by
  have hc0 : constantCoeff (PowerSeries.subst q f.divXPowOrder) ≠ 0 := by
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hq, Algebra.algebraMap_self_apply]
    exact PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hf
  have hu : PowerSeries.subst q f.divXPowOrder ≠ 0 := fun h ↦ hc0 (by simp [h])
  rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f),
    PowerSeries.subst_mul (.of_constantCoeff_zero hq),
    PowerSeries.subst_pow (.of_constantCoeff_zero hq),
    PowerSeries.subst_X (.of_constantCoeff_zero hq)]
  exact mul_ne_zero (pow_ne_zero _ hq0) hu

private theorem injective_substAlgHom_coe {σ : Type*} {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    Function.Injective
      ((IsScalarTower.toAlgHom K (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))).comp
        (PowerSeries.substAlgHom (R := K) (.of_constantCoeff_zero hq))) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  by_contra hf0
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', PowerSeries.coe_substAlgHom,
    map_eq_zero_iff _ (IsFractionRing.injective (MvPowerSeries σ K)
      (FractionRing (MvPowerSeries σ K)))] at hf
  exact subst_ne_zero_of_ne_zero hq hq0 hf0 hf

/-- Extension of `PowerSeries.subst q` (`q ≠ 0`, `constantCoeff q = 0`) to a `K`-algebra
homomorphism `K⸨X⸩ →ₐ[K] FractionRing (MvPowerSeries σ K)`. -/
private noncomputable def liftLaurentSubst {σ : Type*} {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    K⸨X⸩ →ₐ[K] FractionRing (MvPowerSeries σ K) :=
  IsFractionRing.liftAlgHom (injective_substAlgHom_coe hq hq0)

@[simp]
private theorem liftLaurentSubst_coe {σ : Type*} {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) (f : K⟦X⟧) :
    liftLaurentSubst hq hq0 (f : K⸨X⸩) =
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
        (PowerSeries.subst q f) := by
  rw [liftLaurentSubst, IsFractionRing.coe_liftAlgHom, ← _root_.LaurentSeries.coe_algebraMap,
    IsFractionRing.lift_algebraMap]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', PowerSeries.coe_substAlgHom]

open scoped Classical in
/-- Evaluating the tautological point of `ψ : W₁ → W₂` along `liftLaurentSubst hq hq0 ∘ e₁`
gives `paramPoint W₂ (PowerSeries.subst q ψ.formalSeries)`. -/
private theorem point_map_liftLaurentSubst_tautologicalPoint [W₂.IsElliptic]
    (ψ : Isogeny W₁.toAffine W₂.toAffine) {σ : Type*} {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    Point.map ((liftLaurentSubst hq hq0).comp W₁.functionFieldLaurentExpansion)
        ψ.pullback.tautologicalPoint =
      paramPoint (KK := FractionRing (MvPowerSeries σ K)) W₂
        (PowerSeries.subst q ψ.formalSeries) := by
  have hqc : constantCoeff (PowerSeries.subst q ψ.formalSeries) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hq _ ψ.constantCoeff_formalSeries
  have hqψ0 : PowerSeries.subst q ψ.formalSeries ≠ 0 :=
    subst_ne_zero_of_ne_zero hq hq0 ψ.formalSeries_ne_zero
  obtain ⟨_, hparam⟩ :=
    paramPoint_eq_some (KK := FractionRing (MvPowerSeries σ K)) W₂ hqc hqψ0
  rw [Isogeny.tautologicalPoint_eq_map_genericPoint, Point.map_map, hparam, genericPoint_eq_some,
    Point.map_some]
  refine Point.eq_of_coords (Point.some_ne_zero _) (Point.some_ne_zero _) ?_ ?_
  · simp only [Point.xCoord_some, AlgHom.comp_apply,
      ψ.functionFieldLaurentExpansion_fieldPullback,
      W₂.functionFieldLaurentExpansion_genericX_eq_X_div_formalW, map_div₀,
      LaurentSeries.substAlgHom_coe,
      PowerSeries.subst_X (.of_constantCoeff_zero' ψ.constantCoeff_formalSeries),
      liftLaurentSubst_coe,
      PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero ψ.constantCoeff_formalSeries)
        (.of_constantCoeff_zero hq)]
  · simp only [Point.yCoord_some, AlgHom.comp_apply,
      ψ.functionFieldLaurentExpansion_fieldPullback,
      W₂.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW, map_div₀, map_neg,
      map_one, LaurentSeries.substAlgHom_coe, liftLaurentSubst_coe,
      PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero ψ.constantCoeff_formalSeries)
        (.of_constantCoeff_zero hq)]

end LiftLaurentSubst

/-- **An isogeny is determined by its formal series.** -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := by
  intro φ ψ h
  refine Isogeny.ext (AlgHom.ext fun x ↦ ?_)
  rw [← φ.fieldPullback_algebraMap, ← ψ.fieldPullback_algebraMap]
  apply W₁.functionFieldLaurentExpansion.injective
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [φ.functionFieldLaurentExpansion_fieldPullback, ψ.functionFieldLaurentExpansion_fieldPullback]
  exact congrArg
    (fun s : {s : K⟦X⟧ // PowerSeries.constantCoeff s = 0 ∧ s ≠ 0} ↦
      LaurentSeries.substAlgHom s.2.1 s.2.2 _)
    (Subtype.ext (a1 := ⟨φ.formalSeries, φ.constantCoeff_formalSeries, φ.formalSeries_ne_zero⟩)
      (a2 := ⟨ψ.formalSeries, ψ.constantCoeff_formalSeries, ψ.formalSeries_ne_zero⟩) h)

@[simp]
theorem formalSeries_inj {φ ψ : Isogeny W₁.toAffine W₂.toAffine} :
    φ.formalSeries = ψ.formalSeries ↔ φ = ψ :=
  formalSeries_injective.eq_iff

/-- **Negation `[-1]` has formal series `W.formalInverse`.** -/
@[simp]
theorem formalSeries_negIsogeny (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).formalSeries = W.formalInverse := by
  apply (formalSeries_eq_iff _ _).mpr
  have hw : (formalW W : K⸨X⸩) ≠ 0 := fun hw0 ↦
    (map_ne_zero W.functionFieldLaurentExpansion).mpr W.toAffine.genericY_ne_zero
      (by rw [W.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW, hw0, div_zero])
  have hden_mul : (formalInverseDenom W : K⸨X⸩) *
      (PowerSeries.invOfUnit (formalInverseDenom W) 1 : K⸨X⸩) = 1 := by
    rw [← map_mul, mul_invOfUnit_formalInverseDenom, map_one]
  have hden0 : (formalInverseDenom W : K⸨X⸩) ≠ 0 := left_ne_zero_of_mul_eq_one hden_mul
  have hden : W.functionFieldLaurentExpansion
      ((W.toAffine⁄W.toAffine.FunctionField).toAffine.negY W.toAffine.genericX
        W.toAffine.genericY) =
        (formalInverseDenom W : K⸨X⸩) / (formalW W : K⸨X⸩) := by
    rw [eq_div_iff hw]
    simp only [Affine.negY, WeierstrassCurve.baseChange, map_a₁, map_a₃, map_sub, map_neg, map_mul,
      AlgHom.commutes, W.functionFieldLaurentExpansion_genericX_eq_X_div_formalW,
      W.functionFieldLaurentExpansion_genericY_eq_neg_one_div_formalW, formalInverseDenom_def,
      PowerSeries.coe_one, ← HahnSeries.algebraMap_apply', ← PowerSeries.algebraMap_eq,
      sub_mul, neg_mul, mul_assoc, div_mul_cancel₀ _ hw]
    dsimp only [WeierstrassCurve.toAffine]
    ring
  rw [map_div₀, map_neg, fieldPullback_negIsogeny_genericX, fieldPullback_negIsogeny_genericY,
    map_div₀, map_neg, hden, W.functionFieldLaurentExpansion_genericX_eq_X_div_formalW,
    formalInverse_def, PowerSeries.coe_neg, PowerSeries.coe_mul, eq_div_iff (div_ne_zero hden0 hw)]
  calc
    -(((PowerSeries.X : K⟦X⟧) : K⸨X⸩) * (PowerSeries.invOfUnit (formalInverseDenom W) 1 : K⸨X⸩)) *
        ((formalInverseDenom W : K⸨X⸩) / (formalW W : K⸨X⸩)) =
      -((PowerSeries.X : K⟦X⟧) * ((formalInverseDenom W : K⸨X⸩) *
        (PowerSeries.invOfUnit (formalInverseDenom W) 1 : K⸨X⸩))) / (formalW W : K⸨X⸩) := by ring
    _ = -((PowerSeries.X : K⟦X⟧) / (formalW W : K⸨X⸩)) := by rw [hden_mul, mul_one, neg_div]

namespace Hom

open scoped Classical in
/-- **The formal power series of a morphism**: `0` on the zero morphism, and `φ.formalSeries` on
an isogeny `φ`. -/
noncomputable def formalSeries (f : Hom W₁.toAffine W₂.toAffine) : K⟦X⟧ :=
  if hf : f = 0 then 0 else (toIsogeny hf).formalSeries

@[simp]
theorem formalSeries_zero : (0 : Hom W₁.toAffine W₂.toAffine).formalSeries = 0 :=
  dite_eq_left_of_eq_true (eq_true rfl)

@[simp]
theorem formalSeries_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalSeries = φ.formalSeries := by
  rw [formalSeries, dite_eq_right_of_eq_false (eq_false (ofIsogeny_ne_zero φ)),
    toIsogeny_ofIsogeny]

/-- Every morphism's formal series has zero constant coefficient. -/
@[simp]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

/-- A morphism vanishes if and only if its formal series vanishes. -/
@[simp]
theorem formalSeries_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · simp [φ.formalSeries_ne_zero, ofIsogeny_ne_zero φ]

/-- **A morphism is determined by its formal series.** -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := by
  intro f g h
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · exact (formalSeries_eq_zero_iff.mp (h.symm.trans formalSeries_zero)).symm
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · exact formalSeries_eq_zero_iff.mp (h.trans formalSeries_zero)
  · rw [formalSeries_ofIsogeny, formalSeries_ofIsogeny] at h
    exact congrArg ofIsogeny (Isogeny.formalSeries_injective h)

@[simp]
theorem formalSeries_inj {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = g.formalSeries ↔ f = g :=
  formalSeries_injective.eq_iff

/-- The identity morphism induces the identity formal series `X`. -/
@[simp]
theorem formalSeries_id (W : WeierstrassCurve K) :
    (Hom.id W.toAffine).formalSeries = PowerSeries.X := by
  rw [Hom.id_def, formalSeries_ofIsogeny, Isogeny.formalSeries_id]

/-- Composition of morphisms induces substitution of their formal series. -/
@[simp]
theorem formalSeries_comp (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalSeries = PowerSeries.subst f.formalSeries g.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp [PowerSeries.subst_zero_of_constantCoeff_zero g.constantCoeff_formalSeries]
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · simp [PowerSeries.subst_zero]
  · simp

/-- **The formal series of `-f` is `W₂.formalInverse` composed with `f.formalSeries`.** -/
@[simp]
theorem formalSeries_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalSeries = PowerSeries.subst f.formalSeries W₂.formalInverse := by
  rw [neg_def, formalSeries_comp, formalSeries_ofIsogeny, formalSeries_negIsogeny]

section Add

variable [W₂.IsElliptic]

open scoped Classical in
/-- Reading `W₁.functionFieldLaurentExpansion` in `FractionRing K⟦X⟧` sends the tautological point
of `f` to `paramPoint W₂ f.formalSeries`. -/
private theorem point_map_tautologicalPoint_eq_paramPoint (f : Hom W₁.toAffine W₂.toAffine) :
    Point.map ((liftLaurentSubst (q := (X () : MvPowerSeries Unit K))
        (constantCoeff_X ()) PowerSeries.X_ne_zero).comp
        W₁.functionFieldLaurentExpansion) f.tautologicalPoint =
      paramPoint (KK := FractionRing K⟦X⟧) W₂ f.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [tautologicalPoint_zero, map_zero, formalSeries_zero, paramPoint_zero]
  · rw [tautologicalPoint_ofIsogeny, formalSeries_ofIsogeny,
      point_map_liftLaurentSubst_tautologicalPoint φ (constantCoeff_X ()) PowerSeries.X_ne_zero]
    exact congrArg (paramPoint (KK := FractionRing K⟦X⟧) W₂) (PowerSeries.X_subst _)

open scoped Classical in
/-- **The formal series of a sum of morphisms is the formal-group sum of their series.** -/
theorem formalSeries_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalSeries =
      subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries := by
  have hc : constantCoeff
      (subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries) = 0 := by
    rw [subst_formalGroup_eq_subst_pair W₂ f.constantCoeff_formalSeries
      g.constantCoeff_formalSeries]
    exact constantCoeff_subst_pair_formalAdd W₂ f.constantCoeff_formalSeries
      g.constantCoeff_formalSeries
  refine paramPoint_injective (KK := FractionRing K⟦X⟧) W₂ (f + g).constantCoeff_formalSeries hc ?_
  rw [← point_map_tautologicalPoint_eq_paramPoint, tautologicalPoint_add, (Point.map _).map_add,
    point_map_tautologicalPoint_eq_paramPoint, point_map_tautologicalPoint_eq_paramPoint,
    paramPoint_subst_formalGroup (KK := FractionRing K⟦X⟧) W₂ f.constantCoeff_formalSeries
      g.constantCoeff_formalSeries]

/-- **`Hom.formalSeries` as an additive homomorphism into `(formalGroup W₂).Point Unit`.** -/
noncomputable def formalSeriesPointHom :
    Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit where
  toFun f := ⟨f.formalSeries, .of_constantCoeff_zero f.constantCoeff_formalSeries⟩
  map_zero' := Subtype.ext formalSeries_zero
  map_add' f g := Subtype.ext (formalSeries_add f g)

@[simp]
theorem val_formalSeriesPointHom (f : Hom W₁.toAffine W₂.toAffine) :
    (formalSeriesPointHom f).val = f.formalSeries := (rfl)

/-- `Hom.formalSeriesPointHom` is injective. -/
theorem formalSeriesPointHom_injective :
    Function.Injective (formalSeriesPointHom (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h ↦ formalSeries_injective (congrArg Subtype.val h)

/-- **The formal series of `n • f` (`n : ℕ`) is `[n]_{formalGroup W₂}` composed with
`f.formalSeries`.** -/
@[simp]
theorem formalSeries_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).nsmulSeries n) := by
  have h := congrArg Subtype.val (formalSeriesPointHom.map_nsmul n f)
  rwa [val_formalSeriesPointHom, ← (formalGroup W₂).subst_nsmulSeries (formalSeriesPointHom f) n,
    val_formalSeriesPointHom] at h

/-- **The formal series of `n • f` (`n : ℤ`) is `[n]_{formalGroup W₂}` composed with
`f.formalSeries`.** -/
@[simp]
theorem formalSeries_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).zsmulSeries n) := by
  have h := congrArg Subtype.val (formalSeriesPointHom.map_zsmul n f)
  rwa [val_formalSeriesPointHom, ← (formalGroup W₂).subst_zsmulSeries (formalSeriesPointHom f) n,
    val_formalSeriesPointHom] at h

end Add

end Hom

/-- **Multiplication by `n : ℤ` has formal series `(formalGroup W).zsmulSeries n`.** -/
@[simp]
theorem formalSeries_mulByIntIsogeny (W : WeierstrassCurve K) [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  rw [← Hom.formalSeries_ofIsogeny, ofIsogeny_mulByIntIsogeny, Hom.formalSeries_zsmul,
    Hom.formalSeries_id, PowerSeries.X_subst]

/-- **Multiplication by `n : ℕ` has formal series `(formalGroup W).nsmulSeries n`.** -/
theorem formalSeries_mulByIntIsogeny_natCast (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).nsmulSeries n := by
  rw [formalSeries_mulByIntIsogeny, FormalGroup.zsmulSeries_natCast]

-- Not `@[simp]`: `mulByIntIsogenyOfNeZero` is an `abbrev` for `mulByIntIsogeny`.
/-- **Multiplication by a nonzero integer `n` has formal series `(formalGroup W).zsmulSeries n`.**
-/
theorem formalSeries_mulByIntIsogenyOfNeZero (W : WeierstrassCurve K) [W.IsElliptic] {n : ℤ}
    (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n :=
  formalSeries_mulByIntIsogeny W _

/-- **Multiplication by a nonzero natural `n` has formal series `(formalGroup W).nsmulSeries n`.**
-/
theorem formalSeries_mulByIntIsogenyOfNeZero_natCast (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : ℤ) ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = (formalGroup W).nsmulSeries n :=
  formalSeries_mulByIntIsogeny_natCast W _

/-! ### Every isogeny and morphism induces a formal group homomorphism -/

section FormalGroupHom

/-- Evaluating a mapped bivariate polynomial at `(E genericX, E genericY)` agrees with applying `E`
to its coordinate-ring class. -/
private theorem evalEval_map_genericX_genericY {KK : Type*} [Field KK] [Algebra K KK]
    (E : W₁.toAffine.FunctionField →ₐ[K] KK) (p : K[X][Y]) :
    (p.map (mapRingHom (algebraMap K KK))).evalEval
        (E W₁.toAffine.genericX) (E W₁.toAffine.genericY) =
      E (algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
        (CoordinateRing.mk W₁.toAffine p)) := by
  rw [genericX_def, genericY_def]
  exact (CoordinateRing.algHom_mk_eq_evalEval
    (E.comp (IsScalarTower.toAlgHom K W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField)) p).symm

/-- For any `K`-algebra homomorphism `E : K(W₁) →ₐ[K] KK` into a field, every carried rational
function `FunctionField.map W₁ ι w` reduces to `E w` at the place of `(E x₁, E y₁)`. -/
private theorem valuation_pointPlace_map_sub_lt_one [W₁.IsElliptic] {KK : Type*} [Field KK]
    [Algebra K KK] (E : W₁.toAffine.FunctionField →ₐ[K] KK)
    (h₁ : (W₁.toAffine.map (algebraMap K KK)).Equation
      (E W₁.toAffine.genericX) (E W₁.toAffine.genericY))
    (w : W₁.toAffine.FunctionField) :
    (CoordinateRing.pointPlace h₁).valuation
        (W₁.toAffine.map (algebraMap K KK)).FunctionField
        (FunctionField.map W₁.toAffine (algebraMap K KK) w -
          algebraMap KK _ (E w)) < 1 := by
  set ι := algebraMap K KK
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors W₁.toAffine.CoordinateRing) w
  dsimp only at hab
  obtain ⟨pa, rfl⟩ := AdjoinRoot.mk_surjective a
  obtain ⟨pb, hb⟩ := AdjoinRoot.mk_surjective b.1
  have hb' : CoordinateRing.mk W₁.toAffine pb = b.1 := hb
  have hb0 : algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
      (CoordinateRing.mk W₁.toAffine pb) ≠ 0 := by
    rw [hb', map_ne_zero_iff _ (IsFractionRing.injective _ _)]
    exact nonZeroDivisors.ne_zero b.2
  have hbw : w = algebraMap _ _ (CoordinateRing.mk W₁.toAffine pa) /
      algebraMap _ _ (CoordinateRing.mk W₁.toAffine pb) := by
    rw [eq_div_iff hb0, hb', ← hab]
  have hEb0 : E (algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
      (CoordinateRing.mk W₁.toAffine pb)) ≠ 0 :=
    (map_ne_zero E).mpr hb0
  have hD : algebraMap (W₁.toAffine.map ι).CoordinateRing
      (W₁.toAffine.map ι).FunctionField
      (CoordinateRing.mk (W₁.toAffine.map ι) (pb.map (mapRingHom ι))) ≠ 0 := by
    rw [← CoordinateRing.map_mk, ← FunctionField.map_algebraMap_coordinateRing]
    exact (map_ne_zero (FunctionField.map W₁.toAffine ι)).mpr hb0
  have heq : FunctionField.map W₁.toAffine ι w - algebraMap KK _ (E w) =
      algebraMap _ _
        (CoordinateRing.mk (W₁.toAffine.map ι)
          (pa.map (mapRingHom ι) - Polynomial.C (Polynomial.C (E w)) * pb.map (mapRingHom ι))) /
        algebraMap _ _
          (CoordinateRing.mk (W₁.toAffine.map ι) (pb.map (mapRingHom ι))) := by
    nth_rw 1 [hbw]
    rw [map_div₀, FunctionField.map_algebraMap_coordinateRing,
      FunctionField.map_algebraMap_coordinateRing, CoordinateRing.map_mk, CoordinateRing.map_mk,
      eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, map_sub, map_sub, map_mul, map_mul,
      IsScalarTower.algebraMap_apply KK (W₁.toAffine.map ι).CoordinateRing,
      CoordinateRing.mk_C_eq_algebraMap (W := W₁.toAffine.map ι) (Polynomial.C (E w)),
      IsScalarTower.algebraMap_apply KK KK[X] (W₁.toAffine.map ι).CoordinateRing,
      Polynomial.algebraMap_eq]
  rw [heq]
  refine CoordinateRing.valuation_pointPlace_div_lt_one _ h₁
    (by rwa [evalEval_map_genericX_genericY]) ?_
  rw [evalEval_sub, evalEval_mul, evalEval_C, eval_C, evalEval_map_genericX_genericY,
    evalEval_map_genericX_genericY, hbw, map_div₀, div_mul_cancel₀ _ hEb0, sub_self]

/-- For any `K`-algebra homomorphism `E : K(W₁) →ₐ[K] KK` into a field, the base-changed isogeny
`φ.baseChange KK` acts on `Point.map E W₁.genericPoint` by `Point.map E φ.tautologicalPoint`.
Because `E` is injective on `K(W₁)`, no denominator in `K[W₁]` vanishes at `(E x₁, E y₁)`. -/
private theorem pointMap_ofIsogeny_map_genericPoint [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {KK : Type*} [Field KK] [DecidableEq KK] [Algebra K KK]
    (E : W₁.toAffine.FunctionField →ₐ[K] KK) :
    (Hom.ofIsogeny (φ.baseChange KK)).pointMap (Point.map E W₁.toAffine.genericPoint) =
      Point.map E φ.pullback.tautologicalPoint := by
  let ι := algebraMap K KK
  have hP₁ : (W₁.toAffine.map ι).Nonsingular (E W₁.toAffine.genericX)
      (E W₁.toAffine.genericY) := by
    rw [genericX_def, genericY_def]
    exact equation_iff_nonsingular.mp (CoordinateRing.equation_of_algHom
      (E.comp (IsScalarTower.toAlgHom K W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField)))
  have hP₂ : (W₂.toAffine.map ι).Nonsingular
      (E (φ.fieldPullback W₂.toAffine.genericX)) (E (φ.fieldPullback W₂.toAffine.genericY)) := by
    rw [genericX_def, genericY_def]
    exact equation_iff_nonsingular.mp (CoordinateRing.equation_of_algHom
      ((E.comp φ.fieldPullback).comp
        (IsScalarTower.toAlgHom K W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField)))
  have hsrc : Point.map E W₁.toAffine.genericPoint =
      (Point.some (E W₁.toAffine.genericX) (E W₁.toAffine.genericY) hP₁ :
        (W₁.toAffine.map ι).Point) := by
    rw [genericPoint_eq_some, Point.map_some]; rfl
  have hdst : Point.map E φ.pullback.tautologicalPoint =
      (Point.some (E (φ.fieldPullback W₂.toAffine.genericX))
        (E (φ.fieldPullback W₂.toAffine.genericY)) hP₂ : (W₂.toAffine.map ι).Point) := by
    rw [Isogeny.tautologicalPoint_eq_map_genericPoint, Point.map_map, genericPoint_eq_some,
      Point.map_some]; rfl
  -- `Isogeny.baseChange` (`abbrev` for `φ.map ι`) is typed over the semireducible `def`
  -- `WeierstrassCurve.baseChange`, which `dsimp`/`rw` do not unfold inside `Hom.ofIsogeny`'s
  -- implicit curve parameters under `implicit` transparency.
  change (Hom.ofIsogeny (φ.map ι)).pointMap (Point.map E W₁.toAffine.genericPoint) =
    Point.map E φ.pullback.tautologicalPoint
  rw [hsrc, hdst, Hom.pointMap_eq_iff, Hom.tautologicalPoint_ofIsogeny,
    Isogeny.tautologicalPoint_eq_map_genericPoint, genericPoint_eq_some, Point.map_some,
    Point.equivBaseChangeSelf_some, some_sub_baseChange_mem_polePoints_iff,
    coe_pointEquivDegreeOnePlace_some]
  refine ⟨?_, ?_⟩
  · rw [← FunctionField.map_genericX W₂.toAffine ι, map_fieldPullback_map, Place.valuation_ofPrime]
    exact valuation_pointPlace_map_sub_lt_one E _ _
  · rw [← FunctionField.map_genericY W₂.toAffine ι, map_fieldPullback_map, Place.valuation_ofPrime]
    exact valuation_pointPlace_map_sub_lt_one E _ _

open scoped Classical in
private theorem pointMap_ofIsogeny_paramPoint [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {σ : Type*} {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (Hom.ofIsogeny (φ.baseChange (FractionRing (MvPowerSeries σ K)))).pointMap
        (paramPoint (KK := FractionRing (MvPowerSeries σ K)) W₁ q) =
      paramPoint (KK := FractionRing (MvPowerSeries σ K)) W₂
        (PowerSeries.subst q φ.formalSeries) := by
  have hid := point_map_liftLaurentSubst_tautologicalPoint (Isogeny.id W₁.toAffine) hq hq0
  rw [Isogeny.id_pullback, CoordinatePullback.tautologicalPoint_id, Isogeny.formalSeries_id,
    PowerSeries.subst_X (.of_constantCoeff_zero hq)] at hid
  rw [← hid, pointMap_ofIsogeny_map_genericPoint,
    point_map_liftLaurentSubst_tautologicalPoint φ hq hq0]

open scoped Classical in
/-- **Every isogeny's formal series satisfies the formal-group homomorphism equation**
`φ(F₁(X, Y)) = F₂(φ(X), φ(Y))`. -/
theorem subst_formalGroup_formalSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    PowerSeries.subst (formalGroup W₁).toPowerSeries φ.formalSeries =
      subst (fun i ↦ φ.formalSeries.toMvPowerSeries i) (formalGroup W₂).toPowerSeries := by
  have := φ.isElliptic
  let KK := FractionRing (MvPowerSeries (Fin 2) K)
  set X₀ : MvPowerSeries (Fin 2) K := X 0
  set X₁ : MvPowerSeries (Fin 2) K := X 1
  have hX0c : constantCoeff X₀ = 0 := constantCoeff_X 0
  have hX1c : constantCoeff X₁ = 0 := constantCoeff_X 1
  have hX0 : X₀ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hX1 : X₁ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hF₁c : constantCoeff (formalGroup W₁).toPowerSeries = 0 :=
    (formalGroup W₁).zero_constantCoeff
  have hF₁0 : (formalGroup W₁).toPowerSeries ≠ 0 := by
    intro h0
    have hlin := (formalGroup W₁).lin_coeff_X
    rw [h0, map_zero] at hlin
    exact one_ne_zero hlin.symm
  have hL : constantCoeff (PowerSeries.subst (formalGroup W₁).toPowerSeries φ.formalSeries) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hF₁c _ φ.constantCoeff_formalSeries
  set φ₀ : MvPowerSeries (Fin 2) K := PowerSeries.subst X₀ φ.formalSeries
  set φ₁ : MvPowerSeries (Fin 2) K := PowerSeries.subst X₁ φ.formalSeries
  have hφ0c : constantCoeff φ₀ = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hX0c _ φ.constantCoeff_formalSeries
  have hφ1c : constantCoeff φ₁ = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hX1c _ φ.constantCoeff_formalSeries
  have hpair : (fun i : Fin 2 ↦ φ.formalSeries.toMvPowerSeries i) = ![φ₀, φ₁] := by
    funext i; fin_cases i <;> simp [φ₀, φ₁, X₀, X₁, PowerSeries.toMvPowerSeries_eq_subst]
  rw [hpair]
  have hR : constantCoeff (subst ![φ₀, φ₁] (formalGroup W₂).toPowerSeries) = 0 := by
    rw [subst_formalGroup_eq_subst_pair W₂ hφ0c hφ1c]
    exact constantCoeff_subst_pair_formalAdd W₂ hφ0c hφ1c
  refine paramPoint_injective (KK := KK) W₂ hL hR ?_
  have hF₁_self : (formalGroup W₁).toPowerSeries =
      subst ![X₀, X₁] (formalGroup W₁).toPowerSeries := by
    have hXX : (![X₀, X₁] : Fin 2 → MvPowerSeries (Fin 2) K) = MvPowerSeries.X := by
      funext i; fin_cases i <;> rfl
    rw [hXX, subst_self, id_eq]
  rw [← pointMap_ofIsogeny_paramPoint φ hF₁c hF₁0,
    paramPoint_subst_formalGroup (KK := KK) W₂ hφ0c hφ1c,
    ← pointMap_ofIsogeny_paramPoint φ hX0c hX0, ← pointMap_ofIsogeny_paramPoint φ hX1c hX1,
    ← Hom.pointMap_add, ← paramPoint_subst_formalGroup (KK := KK) W₁ hX0c hX1c, ← hF₁_self]

/-- **The formal group homomorphism induced by an isogeny.** -/
noncomputable def formalGroupHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := φ.formalSeries
  zero_constantCoeff := φ.constantCoeff_formalSeries
  hom := φ.subst_formalGroup_formalSeries

@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries := (rfl)

/-- `Isogeny.formalGroupHom` is injective. -/
theorem formalGroupHom_injective [W₂.IsElliptic] :
    Function.Injective (formalGroupHom (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h ↦ formalSeries_injective (congrArg FormalGroupHom.toPowerSeries h)

@[simp]
theorem formalGroupHom_inj [W₂.IsElliptic] {φ ψ : Isogeny W₁.toAffine W₂.toAffine} :
    φ.formalGroupHom = ψ.formalGroupHom ↔ φ = ψ :=
  formalGroupHom_injective.eq_iff

/-- The identity isogeny induces the identity formal group homomorphism. -/
@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Isogeny.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext
  simp

/-- Composition of isogenies induces composition of formal group homomorphisms. -/
@[simp]
theorem formalGroupHom_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (ψ : Isogeny W₂.toAffine W₃.toAffine) (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).formalGroupHom = ψ.formalGroupHom.comp φ.formalGroupHom := by
  ext
  simp

/-- **The formal group homomorphism induced by an elliptic-curve morphism `Hom W₁ W₂`.** -/
noncomputable def Hom.formalGroupHom [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) :=
  FormalGroupHom.ofHomDefectEqZero f.constantCoeff_formalSeries <| by
    rcases Hom.eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
    · simp
    · simpa using φ.formalGroupHom.homDefect_toPowerSeries

@[simp]
theorem Hom.formalGroupHom_toPowerSeries [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalGroupHom.toPowerSeries = f.formalSeries :=
  FormalGroupHom.ofHomDefectEqZero_toPowerSeries _ _

/-- `Hom.formalGroupHom` is injective. -/
theorem Hom.formalGroupHom_injective [W₂.IsElliptic] :
    Function.Injective (Hom.formalGroupHom (W₁ := W₁) (W₂ := W₂)) :=
  fun _ _ h ↦ Hom.formalSeries_injective (by simpa using congrArg FormalGroupHom.toPowerSeries h)

@[simp]
theorem Hom.formalGroupHom_inj [W₂.IsElliptic] {f g : Hom W₁.toAffine W₂.toAffine} :
    f.formalGroupHom = g.formalGroupHom ↔ f = g :=
  Hom.formalGroupHom_injective.eq_iff

/-- On an isogeny, `Hom.formalGroupHom` agrees with `Isogeny.formalGroupHom`. -/
@[simp]
theorem Hom.formalGroupHom_ofIsogeny [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (Hom.ofIsogeny φ).formalGroupHom = φ.formalGroupHom := by
  ext
  simp

/-- The identity morphism induces the identity formal group homomorphism. -/
@[simp]
theorem Hom.formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Hom.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext
  simp

/-- Composition of morphisms induces composition of formal group homomorphisms. -/
@[simp]
theorem Hom.formalGroupHom_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalGroupHom = g.formalGroupHom.comp f.formalGroupHom := by
  ext
  simp

end FormalGroupHom

end Isogeny

end TauCeti

end
