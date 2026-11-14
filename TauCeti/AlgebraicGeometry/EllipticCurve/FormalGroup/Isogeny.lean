/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Basic
public import TauCeti.RingTheory.FormalGroup.Hom.Basic
public import TauCeti.RingTheory.FormalGroup.ZSMul
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.FormalPoint
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# Formal-group homomorphisms induced by isogenies and morphisms

An isogeny `φ : W₁ → W₂` of Weierstrass curves over a field `K` expands at the point at infinity,
in the local parameter `z = -x / y`, to a nonzero power series `φ.formalSeries ∈ K⟦X⟧` with zero
constant coefficient (`TauCeti.Isogeny.formalSeries`). This file connects that local expansion to
the formal group laws `formalGroup W₁` and `formalGroup W₂`, to the inseparable degree of `φ`, and
to the additive group `Hom W₁ W₂` of pointed morphisms.

1. **Base change and relative Frobenius.** Base change along a field homomorphism `σ : K →+* L`
   applies `σ` to the coefficients of `φ.formalSeries` (`TauCeti.Isogeny.formalSeries_map`), and
   the `n`-fold relative Frobenius `W → W⁽ᵖⁿ⁾` in exponential characteristic `p` induces the
   monomial `X ^ p ^ n` (`TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny`), with no
   ellipticity assumption on `W`.

2. **Order and inseparable degree.** When `W₂` is elliptic, a separable isogeny is unramified at
   infinity (`TauCeti.Isogeny.ramificationIdx_eq_one`), so `φ.formalSeries` has order `1`. Factoring
   an arbitrary isogeny as `φ = χ ∘ F^r` with `χ` separable and `p ^ r = deg_i φ`
   (`TauCeti.Isogeny.exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq`) gives
   `φ.formalSeries.order = φ.inseparableDegree` (`TauCeti.Isogeny.order_formalSeries`), in all
   characteristics and without assuming `K` is perfect. In particular `φ` is separable if and only
   if the linear coefficient of `φ.formalSeries` is nonzero
   (`TauCeti.Isogeny.coeff_one_formalSeries_ne_zero_iff_isSeparable`).

3. **Addition of morphisms and multiplication by `n`.** Extending `formalSeries` by `0` to the
   additive group `Hom W₁ W₂` (`TauCeti.Isogeny.Hom.formalSeries`), the Bosma–Lenstra projective
   addition law `dblAddXYZ` evaluated at the formal points `[q : -1 : w(q)]` over `K⸨X⸩` shows that
   `(f + g).formalSeries` is the formal-group sum of `f.formalSeries` and `g.formalSeries` in
   `formalGroup W₂` (`TauCeti.Isogeny.Hom.formalSeries_add`). Thus `Hom.toFormalGroupPoint` is an
   additive homomorphism `Hom W₁ W₂ →+ (formalGroup W₂).Point Unit`, identifying `[n].formalSeries`
   with `(formalGroup W).zsmulSeries n` (`TauCeti.Isogeny.formalSeries_mulByIntIsogeny`) and the
   order of `[n]` on the formal group with the inseparable degree of multiplication by `n`
   (`WeierstrassCurve.order_nsmulSeries_formalGroup`).

4. **Formal-group homomorphisms.** Evaluating the base change of `φ` to the fraction field of
   `K⟦z₁, z₂⟧` on the generic formal points shows that `φ.formalSeries` is a homomorphism of formal
   group laws `formalGroup W₁ → formalGroup W₂` (`TauCeti.Isogeny.formalGroupHom`), and similarly
   for every `f : Hom W₁ W₂` (`TauCeti.Isogeny.Hom.formalGroupHom`).

## Main definitions

* `TauCeti.Isogeny.Hom.formalSeries`: the formal power series of a morphism `f : Hom W₁ W₂`,
  stipulating `0` for the zero morphism.
* `TauCeti.Isogeny.Hom.toFormalGroupPoint`: the additive homomorphism sending `f : Hom W₁ W₂` to
  `f.formalSeries` as a `1`-variable point of `formalGroup W₂`.
* `TauCeti.Isogeny.formalGroupHom` and `TauCeti.Isogeny.Hom.formalGroupHom`: the bundled
  `FormalGroupHom (formalGroup W₁) (formalGroup W₂)` induced by an isogeny or morphism.

## Main results

* `TauCeti.Isogeny.formalSeries_map`: `(φ.map σ).formalSeries = PowerSeries.map σ φ.formalSeries`.
* `TauCeti.Isogeny.formalSeries_relativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny`: relative Frobenius induces `X ^ p`
  and `X ^ p ^ n`.
* `TauCeti.Isogeny.order_formalSeries`: `φ.formalSeries.order = φ.inseparableDegree`.
* `TauCeti.Isogeny.order_formalSeries_eq_one_iff_isSeparable` and
  `TauCeti.Isogeny.coeff_one_formalSeries_ne_zero_iff_isSeparable`: formal criteria for
  separability.
* `TauCeti.Isogeny.Hom.formalSeries_add`, `TauCeti.Isogeny.Hom.formalSeries_neg`,
  `TauCeti.Isogeny.Hom.formalSeries_nsmul`, `TauCeti.Isogeny.Hom.formalSeries_zsmul`: compatibility
  of `Hom.formalSeries` with the formal group law of `W₂`.
* `TauCeti.Isogeny.formalSeries_mulByIntIsogeny` and
  `TauCeti.Isogeny.formalSeries_mulByIntIsogenyOfNeZero`: `[n]` induces
  `(formalGroup W).zsmulSeries n`.
* `WeierstrassCurve.order_zsmulSeries_formalGroup` and
  `WeierstrassCurve.order_nsmulSeries_formalGroup`: the order of `[n]` on `formalGroup W` equals
  the inseparable degree of multiplication by `n`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11–12, III.4.10,
  IV.2 and IV.4.
-/

public section

open WeierstrassCurve HahnSeries MvPowerSeries
open scoped LaurentSeries PowerSeries WithZero Polynomial.Bivariate

namespace TauCeti.Isogeny

/-! ### Base change and relative Frobenius -/

section BaseChangeAndFrobenius

variable {K L : Type*} [Field K] [Field L]

-- Laurent expansion at infinity commutes with base change along a field homomorphism.
private theorem functionFieldLaurentExpansion_map (W : WeierstrassCurve K) (σ : K →+* L)
    (f : W.toAffine.FunctionField) :
    (W.map σ).functionFieldLaurentExpansion (Affine.FunctionField.map W.toAffine σ f) =
      HahnSeries.mapRingHom σ (W.functionFieldLaurentExpansion f) := by
  let A : W.toAffine.FunctionField →+* L⸨X⸩ :=
    ((W.map σ).functionFieldLaurentExpansion : (W.map σ).toAffine.FunctionField →+* L⸨X⸩).comp
      (Affine.FunctionField.map W.toAffine σ)
  let B : W.toAffine.FunctionField →+* L⸨X⸩ :=
    (HahnSeries.mapRingHom σ).comp
      (W.functionFieldLaurentExpansion : W.toAffine.FunctionField →+* K⸨X⸩)
  have hparam : A (-W.toAffine.genericX / W.toAffine.genericY) =
      B (-W.toAffine.genericX / W.toAffine.genericY) := by
    simp only [A, B, RingHom.comp_apply, RingHom.coe_coe]
    have hgen : Affine.FunctionField.map W.toAffine σ
        (-W.toAffine.genericX / W.toAffine.genericY) =
        -(W.map σ).toAffine.genericX / (W.map σ).toAffine.genericY := by
      rw [map_div₀, map_neg, Affine.FunctionField.map_genericX, Affine.FunctionField.map_genericY]
    rw [hgen, functionFieldLaurentExpansion_neg_genericX_div_genericY,
      functionFieldLaurentExpansion_neg_genericX_div_genericY,
      HahnSeries.mapRingHom_apply, map_ofPowerSeries, PowerSeries.map_X]
  have hw : A (-W.toAffine.genericY⁻¹) = B (-W.toAffine.genericY⁻¹) := by
    have h1 : (W.map σ).functionFieldLaurentExpansion
        (-(Affine.FunctionField.map W.toAffine σ W.toAffine.genericY)⁻¹) =
        HahnSeries.mapRingHom σ
          (W.functionFieldLaurentExpansion (-W.toAffine.genericY⁻¹)) := by
      rw [Affine.FunctionField.map_genericY, functionFieldLaurentExpansion_neg_inv_genericY,
        functionFieldLaurentExpansion_neg_inv_genericY, HahnSeries.mapRingHom_apply,
        map_ofPowerSeries, map_formalW]
    simpa only [A, B, RingHom.comp_apply, RingHom.coe_coe, map_neg, map_inv₀] using h1
  have hY : A W.toAffine.genericY = B W.toAffine.genericY := by
    simpa only [map_neg, map_inv₀, neg_inj, inv_inj] using hw
  have hX : A W.toAffine.genericX = B W.toAffine.genericX := by
    have hy : B W.toAffine.genericY ≠ 0 :=
      (map_ne_zero_iff B B.injective).mpr W.toAffine.genericY_ne_zero
    simpa only [map_div₀, map_neg, hY, div_left_inj₀ hy, neg_inj] using hparam
  have hAB : A = B := Affine.FunctionField.ringHom_ext
    (fun c ↦ by
      ext g
      by_cases hg : g = 0 <;>
        simp [hg, A, B, Affine.FunctionField.map_algebraMap,
          _root_.LaurentSeries.algebraMap_apply, HahnSeries.C_apply])
    hX hY
  exact RingHom.congr_fun hAB f

/-- **Base change of an isogeny maps the coefficients of its formal series.** -/
@[simp]
theorem formalSeries_map {W₁ W₂ : WeierstrassCurve K} (φ : Isogeny W₁.toAffine W₂.toAffine)
    (σ : K →+* L) :
    (φ.map σ).formalSeries = PowerSeries.map σ φ.formalSeries := by
  apply (formalSeries_eq_iff _ _).mpr
  have hgen : -(W₂.map σ).toAffine.genericX / (W₂.map σ).toAffine.genericY =
      Affine.FunctionField.map W₂.toAffine σ (-W₂.toAffine.genericX / W₂.toAffine.genericY) := by
    rw [map_div₀, map_neg, Affine.FunctionField.map_genericX, Affine.FunctionField.map_genericY]
  rw [hgen, map_fieldPullback_map, functionFieldLaurentExpansion_map, ← φ.coe_formalSeries,
    HahnSeries.mapRingHom_apply, map_ofPowerSeries]

/-- **The `n`-fold relative Frobenius induces `X ^ p ^ n` on the formal parameter.** -/
@[simp]
theorem formalSeries_iterateRelativeFrobeniusIsogeny (p : ℕ) [ExpChar K p]
    (W : WeierstrassCurve K) (n : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W.toAffine n).formalSeries = PowerSeries.X ^ p ^ n := by
  apply (formalSeries_eq_iff _ _).mpr
  have hgen : -(W.map (iterateFrobenius K p n)).toAffine.genericX /
        (W.map (iterateFrobenius K p n)).toAffine.genericY =
      Affine.FunctionField.map W.toAffine (iterateFrobenius K p n)
        (-W.toAffine.genericX / W.toAffine.genericY) := by
    rw [map_div₀, map_neg, Affine.FunctionField.map_genericX, Affine.FunctionField.map_genericY]
  rw [hgen, fieldPullback_iterateRelativeFrobeniusIsogeny_map, map_pow, map_pow,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- **The relative Frobenius isogeny induces `X ^ p` on the formal parameter.** -/
@[simp]
theorem formalSeries_relativeFrobeniusIsogeny (p : ℕ) [ExpChar K p] (W : WeierstrassCurve K) :
    (relativeFrobeniusIsogeny p W.toAffine).formalSeries = PowerSeries.X ^ p := by
  apply (formalSeries_eq_iff _ _).mpr
  have hgen : -(W.map (frobenius K p)).toAffine.genericX /
        (W.map (frobenius K p)).toAffine.genericY =
      Affine.FunctionField.map W.toAffine (frobenius K p)
        (-W.toAffine.genericX / W.toAffine.genericY) := by
    rw [map_div₀, map_neg, Affine.FunctionField.map_genericX, Affine.FunctionField.map_genericY]
  rw [hgen, fieldPullback_relativeFrobeniusIsogeny_map, map_pow, map_pow,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

end BaseChangeAndFrobenius

/-! ### Order and inseparable degree -/

section Order

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **A separable isogeny has formal series of order `1`**, since it is unramified at infinity. -/
theorem order_formalSeries_eq_one_of_isSeparable
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalSeries.order = 1 := by
  have := φ.isElliptic
  let _ : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    φ.fieldPullback.toRingHom.toAlgebra
  have hfp : ∀ z, algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField z =
      φ.fieldPullback z := fun _ ↦ rfl
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback hfp
  have := φ.finiteDimensional_functionField hfp
  have hrest : (Place.infinity W₁.toAffine).restrict K W₂.toAffine.FunctionField =
      Place.infinity W₂.toAffine := by
    rw [Place.restrict_eq_iff_isEquiv_comap, Place.valuation_infinity, Place.valuation_infinity]
    exact φ.isEquiv_comap_infinityPlace
  have hval := Place.valuation_algebraMap_restrict K W₂.toAffine.FunctionField
    (Place.infinity W₁.toAffine) (-W₂.toAffine.genericX / W₂.toAffine.genericY)
  rw [hfp, hrest, φ.ramificationIdx_eq_one hfp (Place.infinity W₁.toAffine), pow_one,
    Place.valuation_infinity, Place.valuation_infinity,
    Affine.infinityPlace_neg_genericX_div_genericY,
    ← W₁.valuation_functionFieldLaurentExpansion, ← φ.coe_formalSeries,
    TauCeti.LaurentSeries.valuation_coe φ.formalSeries_ne_zero] at hval
  have hord : φ.formalSeries.order.toNat = 1 := by
    have hinj := WithZero.exp_inj.mp hval
    omega
  rw [← PowerSeries.coe_toNat_order φ.formalSeries_ne_zero, hord, Nat.cast_one]

/-- **The order of an isogeny's formal power series equals its inseparable degree**
(Silverman II.2.12 and IV.4.2). -/
@[simp]
theorem order_formalSeries : φ.formalSeries.order = φ.inseparableDegree := by
  set p := ringExpChar K
  obtain ⟨r, χ, hsep, hχ⟩ := exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  rw [φ.inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ, ← hχ,
    formalSeries_comp (iterateRelativeFrobeniusIsogeny p W₁.toAffine r) χ,
    PowerSeries.order_subst
      (iterateRelativeFrobeniusIsogeny p W₁.toAffine r).constantCoeff_formalSeries,
    formalSeries_iterateRelativeFrobeniusIsogeny, χ.order_formalSeries_eq_one_of_isSeparable,
    mul_one, PowerSeries.order_X_pow]

/-- **An isogeny has formal series of order `1` if and only if it is separable.** -/
theorem order_formalSeries_eq_one_iff_isSeparable :
    φ.formalSeries.order = 1 ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField := by
  rw [φ.order_formalSeries, ← Nat.cast_one, Nat.cast_inj,
    φ.inseparableDegree_eq_one_iff_isSeparable]

/-- **An isogeny is separable if and only if the linear coefficient of its formal series is
nonzero** (Silverman III.5.5 and IV.4.2(b)). -/
theorem coeff_one_formalSeries_ne_zero_iff_isSeparable :
    PowerSeries.coeff 1 φ.formalSeries ≠ 0 ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField := by
  rw [← φ.order_formalSeries_eq_one_iff_isSeparable]
  constructor
  · intro h1
    refine le_antisymm ?_ (PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
      φ.constantCoeff_formalSeries)
    exact PowerSeries.order_le (n := 1) h1
  · intro hord
    have hto : φ.formalSeries.order.toNat = 1 := by simp [hord]
    exact hto ▸ PowerSeries.coeff_order φ.formalSeries_ne_zero

end Order

/-! ### Formal projective points and the Bosma–Lenstra addition law -/

section FormalPoint

private theorem nonsingular_algebraMap_formalPoint {O : Type*} [CommRing O]
    (W : WeierstrassCurve O) {σ : Type*} {KK : Type*} [Field KK]
    [Algebra (MvPowerSeries σ O) KK] (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) :
    (fracCurve W σ KK).toProjective.Nonsingular
      (algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, PowerSeries.subst q W.formalW]) := by
  refine (Projective.equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero hΔ
    fun h ↦ by simpa using congrFun h 1).mp ?_
  rw [fracCurve_def, ← WeierstrassCurve.map_map]
  exact ((W.toProjective.equation_neg_one_iff_wEquation q _).mpr
    (W.subst_formalW_wEquation (PowerSeries.HasSubst.of_constantCoeff_zero hq))).map _

-- The affine point `[q : -1 : w(q)]` on `fracCurve W σ KK`, defined uniformly for `q = 0` and
-- `q ≠ 0`.
private noncomputable def formalThetaPoint {K : Type*} [Field K] (W : WeierstrassCurve K)
    {σ : Type*} (KK : Type*) [Field KK] [Algebra (MvPowerSeries σ K) KK]
    (q : MvPowerSeries σ K) : (fracCurve W σ KK).toAffine.Point :=
  Projective.Point.toAffine (fracCurve W σ KK).toProjective
    (algebraMap (MvPowerSeries σ K) KK ∘ ![q, -1, PowerSeries.subst q W.formalW])

private theorem formalThetaPoint_zero {K : Type*} [Field K] (W : WeierstrassCurve K)
    {σ : Type*} (KK : Type*) [Field KK] [Algebra (MvPowerSeries σ K) KK] :
    formalThetaPoint W KK (0 : MvPowerSeries σ K) = 0 := by
  have hw0 : PowerSeries.subst (0 : MvPowerSeries σ K) W.formalW = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalW
  exact Projective.Point.toAffine_of_Z_eq_zero (by simp [hw0])

private theorem formalThetaPoint_eq_some {K : Type*} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] {σ : Type*} (KK : Type*) [Field KK] [Algebra (MvPowerSeries σ K) KK]
    [IsFractionRing (MvPowerSeries σ K) KK] {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    ∃ hns : (fracCurve W σ KK).toAffine.Nonsingular
      (algebraMap (MvPowerSeries σ K) KK q /
        algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q W.formalW))
      (-1 / algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q W.formalW)),
      formalThetaPoint W KK q = .some _ _ hns := by
  have hΔ' := W.fracCurve_Δ_ne_zero (σ := σ) (KK := KK) W.isUnit_Δ.ne_zero
  have hz : (algebraMap (MvPowerSeries σ K) KK ∘ ![q, -1, PowerSeries.subst q W.formalW]) 2 ≠ 0 :=
    W.algebraMap_subst_formalW_ne_zero hq hq0
  have hN := nonsingular_algebraMap_formalPoint W hΔ' hq
  refine ⟨by simpa using (Projective.nonsingular_of_Z_ne_zero hz).mp hN, ?_⟩
  rw [formalThetaPoint, Projective.Point.toAffine_of_Z_ne_zero hN hz]
  simp

private theorem formalThetaPoint_inj {K : Type*} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] {σ : Type*} (KK : Type*) [Field KK] [Algebra (MvPowerSeries σ K) KK]
    [IsFractionRing (MvPowerSeries σ K) KK] {q₁ q₂ : MvPowerSeries σ K}
    (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0)
    (h : formalThetaPoint W KK q₁ = formalThetaPoint W KK q₂) : q₁ = q₂ := by
  rcases eq_or_ne q₁ 0 with rfl | hq₁0
  · rcases eq_or_ne q₂ 0 with rfl | hq₂0
    · rfl
    · obtain ⟨_, hθ⟩ := formalThetaPoint_eq_some W KK hq₂ hq₂0
      rw [formalThetaPoint_zero W KK, hθ] at h
      simp at h
  · rcases eq_or_ne q₂ 0 with rfl | hq₂0
    · obtain ⟨_, hθ⟩ := formalThetaPoint_eq_some W KK hq₁ hq₁0
      rw [formalThetaPoint_zero W KK, hθ] at h
      simp at h
    · obtain ⟨_, hθ₁⟩ := formalThetaPoint_eq_some W KK hq₁ hq₁0
      obtain ⟨_, hθ₂⟩ := formalThetaPoint_eq_some W KK hq₂ hq₂0
      rw [hθ₁, hθ₂, Affine.Point.some.injEq] at h
      have hw₁0 : algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q₁ W.formalW) ≠ 0 :=
        W.algebraMap_subst_formalW_ne_zero hq₁ hq₁0
      have hw₂0 : algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q₂ W.formalW) ≠ 0 :=
        W.algebraMap_subst_formalW_ne_zero hq₂ hq₂0
      have hw : algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q₁ W.formalW) =
          algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q₂ W.formalW) := by
        have h2 := h.2
        field_simp [hw₁0, hw₂0] at h2
        exact neg_inj.mp h2.symm
      have hq : algebraMap (MvPowerSeries σ K) KK q₁ =
          algebraMap (MvPowerSeries σ K) KK q₂ := by
        have h1 := h.1
        rw [hw, div_left_inj₀ hw₂0] at h1
        exact h1
      exact IsFractionRing.injective (MvPowerSeries σ K) KK hq

private theorem formalThetaPoint_add {K : Type*} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] {σ : Type*} (KK : Type*) [Field KK] [DecidableEq KK]
    [Algebra (MvPowerSeries σ K) KK] [IsFractionRing (MvPowerSeries σ K) KK]
    {q₁ q₂ : MvPowerSeries σ K} (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0) :
    formalThetaPoint W KK q₁ + formalThetaPoint W KK q₂ =
      formalThetaPoint W KK (subst ![q₁, q₂] (formalGroup W).toPowerSeries) := by
  set ρ := algebraMap (MvPowerSeries σ K) KK
  have hΔ' := W.fracCurve_Δ_ne_zero (σ := σ) (KK := KK) W.isUnit_Δ.ne_zero
  have hp : HasSubst (pairSubstitution q₁ q₂) := hasSubst_pair hq₁ hq₂
  set ψ : MvPowerSeries (Unit ⊕ Unit) K →ₐ[K] MvPowerSeries σ K := substAlgHom hp
  have hcurve : (W.toProjective.map (algebraMap K (MvPowerSeries (Unit ⊕ Unit) K))).map
      ψ.toRingHom = W.toProjective.map (algebraMap K (MvPowerSeries σ K)) := by
    have hcomp : ψ.toRingHom.comp (algebraMap K (MvPowerSeries (Unit ⊕ Unit) K)) =
        algebraMap K (MvPowerSeries σ K) := RingHom.ext fun c ↦ by simp [ψ]
    exact congrArg WeierstrassCurve.toProjective ((W.map_map _ _).trans (congrArg W.map hcomp))
  have hpt (t : MvPowerSeries (Unit ⊕ Unit) K) (ht : constantCoeff t = 0) :
      ψ.toRingHom ∘ ![t, -1, PowerSeries.subst t W.formalW] =
        ![ψ t, -1, PowerSeries.subst (ψ t) W.formalW] := by
    funext k
    fin_cases k
    · rfl
    · simp
    · simp only [Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ψ,
        coe_substAlgHom hp]
      exact subst_powerSeriesSubst hp (.of_constantCoeff_zero ht) W.formalW
  have h₁ := hpt (X (Sum.inl ())) (constantCoeff_X _)
  have h₂ := hpt (X (Sum.inr ())) (constantCoeff_X _)
  have hF := hpt (formalAdd W) (constantCoeff_formalAdd W)
  have hψ₁ : ψ (X (Sum.inl ())) = q₁ := by simp [ψ, subst_X hp]
  have hψ₂ : ψ (X (Sum.inr ())) = q₂ := by simp [ψ, subst_X hp]
  have hψF : ψ (formalAdd W) = subst ![q₁, q₂] (formalGroup W).toPowerSeries := by
    simp only [ψ, coe_substAlgHom hp]
    rw [formalGroup_toPowerSeries, MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _
      (hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨hq₁, hq₂⟩))]
    congr 1
    funext i
    rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp
  rw [hψ₁] at h₁
  rw [hψ₂] at h₂
  rw [hψF] at hF
  set G := subst ![q₁, q₂] (formalGroup W).toPowerSeries
  have hdbl := congrArg (fun v ↦ ψ.toRingHom ∘ v) W.dblAddXYZ_formalW_eq_smul
  rw [← Projective.map_dblAddXYZ, hcurve, h₁, h₂] at hdbl
  have hrhs : ψ.toRingHom ∘
      (-(W.toProjective.map (algebraMap K (MvPowerSeries (Unit ⊕ Unit) K))).dblAddY
          ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
          ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW] •
        ![formalAdd W, -1, PowerSeries.subst (formalAdd W) W.formalW]) =
      -ψ ((W.toProjective.map (algebraMap K (MvPowerSeries (Unit ⊕ Unit) K))).dblAddY
          ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
          ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW]) •
        ![G, -1, PowerSeries.subst G W.formalW] := by
    funext k
    have hk := congrFun hF k
    simp only [Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Pi.smul_apply, smul_eq_mul, map_mul, map_neg] at hk ⊢
    rw [hk]
  rw [hrhs] at hdbl
  have hu : IsUnit
      (-ρ (ψ ((W.toProjective.map (algebraMap K (MvPowerSeries (Unit ⊕ Unit) K))).dblAddY
        ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
        ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW]))) :=
    (W.isUnit_dblAddY_formalW.map ψ.toRingHom).map ρ |>.neg
  have hN₁ := nonsingular_algebraMap_formalPoint W hΔ' hq₁
  have hN₂ := nonsingular_algebraMap_formalPoint W hΔ' hq₂
  have hD : (fracCurve W σ KK).toProjective.dblAddXYZ
      (ρ ∘ ![q₁, -1, PowerSeries.subst q₁ W.formalW])
      (ρ ∘ ![q₂, -1, PowerSeries.subst q₂ W.formalW]) =
      hu.unit • (ρ ∘ ![G, -1, PowerSeries.subst G W.formalW]) := by
    have hmap : (fracCurve W σ KK).toProjective =
        (W.toProjective.map (algebraMap K (MvPowerSeries σ K))).map ρ :=
      congrArg WeierstrassCurve.toProjective ((fracCurve_def W σ KK).trans (W.map_map _ _).symm)
    rw [hmap, Projective.map_dblAddXYZ, hdbl]
    funext k
    fin_cases k <;> simp [Units.smul_def, IsUnit.unit_spec]
  have hD0 : (fracCurve W σ KK).toProjective.dblAddXYZ
      (ρ ∘ ![q₁, -1, PowerSeries.subst q₁ W.formalW])
      (ρ ∘ ![q₂, -1, PowerSeries.subst q₂ W.formalW]) ≠ 0 := by
    rw [hD]
    intro h0
    have h1 := congrFun h0 1
    exact hu.ne_zero (by simpa [Units.smul_def, IsUnit.unit_spec] using h1)
  rw [formalThetaPoint, formalThetaPoint, formalThetaPoint,
    ← Projective.Point.toAffine_add hN₁ hN₂,
    ← Projective.Point.toAffine_of_equiv (Projective.dblAddXYZ_equiv_add hN₁ hN₂ hD0), hD,
    Projective.Point.toAffine_of_equiv ⟨hu.unit, rfl⟩]

-- `formalThetaPoint` transported along `fracCurve_def` to the explicit `W.toAffine.map` curve.
private noncomputable def formalThetaPointMap {K : Type*} [Field K] (W : WeierstrassCurve K)
    {σ : Type*} (KK : Type*) [Field KK] [DecidableEq KK] [Algebra (MvPowerSeries σ K) KK]
    (q : MvPowerSeries σ K) :
    (W.toAffine.map ((algebraMap (MvPowerSeries σ K) KK).comp
      (algebraMap K (MvPowerSeries σ K)))).Point :=
  AddEquiv.cast (M := fun V : WeierstrassCurve KK ↦ V.toAffine.Point) (fracCurve_def W σ KK)
    (formalThetaPoint W KK q)

private theorem formalThetaPointMap_eq_some {K : Type*} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] {σ : Type*} (KK : Type*) [Field KK] [DecidableEq KK]
    [Algebra (MvPowerSeries σ K) KK] [IsFractionRing (MvPowerSeries σ K) KK]
    {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    ∃ hns : (W.toAffine.map ((algebraMap (MvPowerSeries σ K) KK).comp
        (algebraMap K (MvPowerSeries σ K)))).Nonsingular
      (algebraMap (MvPowerSeries σ K) KK q /
        algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q W.formalW))
      (-1 / algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q W.formalW)),
      formalThetaPointMap W KK q = .some _ _ hns := by
  obtain ⟨hns, hθ⟩ := formalThetaPoint_eq_some W KK hq hq0
  have hcurve : (fracCurve W σ KK).toAffine =
      W.toAffine.map ((algebraMap (MvPowerSeries σ K) KK).comp
        (algebraMap K (MvPowerSeries σ K))) :=
    congrArg WeierstrassCurve.toAffine (fracCurve_def W σ KK)
  refine ⟨hcurve ▸ hns, ?_⟩
  rw [formalThetaPointMap, hθ, AddEquiv.cast_apply, Affine.Point.cast_some (fracCurve_def W σ KK)]

private theorem formalThetaPointMap_inj {K : Type*} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] {σ : Type*} (KK : Type*) [Field KK] [DecidableEq KK]
    [Algebra (MvPowerSeries σ K) KK] [IsFractionRing (MvPowerSeries σ K) KK]
    {q₁ q₂ : MvPowerSeries σ K} (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0)
    (h : formalThetaPointMap W KK q₁ = formalThetaPointMap W KK q₂) : q₁ = q₂ :=
  formalThetaPoint_inj W KK hq₁ hq₂ ((AddEquiv.cast _).injective h)

private theorem formalThetaPointMap_add {K : Type*} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] {σ : Type*} (KK : Type*) [Field KK] [DecidableEq KK]
    [Algebra (MvPowerSeries σ K) KK] [IsFractionRing (MvPowerSeries σ K) KK]
    {q₁ q₂ : MvPowerSeries σ K} (hq₁ : constantCoeff q₁ = 0) (hq₂ : constantCoeff q₂ = 0) :
    formalThetaPointMap W KK q₁ + formalThetaPointMap W KK q₂ =
      formalThetaPointMap W KK (subst ![q₁, q₂] (formalGroup W).toPowerSeries) := by
  rw [formalThetaPointMap, formalThetaPointMap, formalThetaPointMap, ← _root_.map_add,
    formalThetaPoint_add W KK hq₁ hq₂]

end FormalPoint

/-! ### Formal series of morphisms in `Hom` -/

namespace Hom

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

/-- **The formal power series of a morphism `f : Hom W₁ W₂`**, stipulating `0` for the zero
morphism and `(toIsogeny hf).formalSeries` for a nonzero morphism. -/
noncomputable def formalSeries (f : Hom W₁.toAffine W₂.toAffine) : K⟦X⟧ := by
  classical exact if hf : f = 0 then 0 else (toIsogeny hf).formalSeries

/-- The zero morphism induces the zero formal series. -/
@[simp]
theorem formalSeries_zero : (0 : Hom W₁.toAffine W₂.toAffine).formalSeries = 0 := by
  classical simp [formalSeries]

/-- The formal series of `Hom.ofIsogeny φ` is `φ.formalSeries`. -/
@[simp]
theorem formalSeries_ofIsogeny (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalSeries = φ.formalSeries := by
  simp [formalSeries]

/-- **A morphism's formal series vanishes if and only if the morphism is zero.** -/
@[simp]
theorem formalSeries_eq_zero_iff {f : Hom W₁.toAffine W₂.toAffine} :
    f.formalSeries = 0 ↔ f = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · simp [φ.formalSeries_ne_zero]

/-- **Every morphism's formal series has zero constant coefficient.** -/
@[simp]
theorem constantCoeff_formalSeries (f : Hom W₁.toAffine W₂.toAffine) :
    PowerSeries.constantCoeff f.formalSeries = 0 := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp
  · simp

/-- **The identity morphism induces the formal series `X`.** -/
@[simp]
theorem formalSeries_id (W : WeierstrassCurve K) :
    (Hom.id W.toAffine).formalSeries = PowerSeries.X := by
  rw [Hom.id_def, formalSeries_ofIsogeny, Isogeny.formalSeries_id]

/-- **Composition of morphisms induces composition of their formal series.** -/
@[simp]
theorem formalSeries_comp (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalSeries = PowerSeries.subst f.formalSeries g.formalSeries := by
  rcases eq_zero_or_exists_ofIsogeny g with rfl | ⟨ψ, rfl⟩
  · simp [PowerSeries.subst_zero]
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · simp [PowerSeries.subst_zero_of_constantCoeff_zero ψ.constantCoeff_formalSeries]
  · rw [ofIsogeny_comp_ofIsogeny, formalSeries_ofIsogeny, formalSeries_ofIsogeny,
      formalSeries_ofIsogeny, Isogeny.formalSeries_comp]

section Addition

variable [W₂.IsElliptic]

private theorem map_baseChange_functionFieldLaurentExpansion_eq_fracCurve
    (W₁ W₂ : WeierstrassCurve K) :
    (W₂.toAffine⁄W₁.toAffine.FunctionField).map W₁.functionFieldLaurentExpansion.toRingHom =
      fracCurve W₂ Unit K⸨X⸩ := by
  have hcomp : W₁.functionFieldLaurentExpansion.toRingHom.comp
      (algebraMap K W₁.toAffine.FunctionField) =
      (algebraMap (MvPowerSeries Unit K) K⸨X⸩).comp (algebraMap K (MvPowerSeries Unit K)) :=
    RingHom.ext fun c ↦ (W₁.functionFieldLaurentExpansion.commutes c).trans
      (IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩ c)
  exact ((W₂.map_map _ _).trans (congrArg W₂.map hcomp)).trans (fracCurve_def W₂ Unit K⸨X⸩).symm

open scoped Classical in
private theorem map_functionFieldLaurentExpansion_tautologicalPoint
    (f : Hom W₁.toAffine W₂.toAffine) :
    Affine.Point.mapAlong W₁.functionFieldLaurentExpansion.toRingHom
        W₁.functionFieldLaurentExpansion.toRingHom.injective f.tautologicalPoint =
      AddEquiv.cast (M := fun V : WeierstrassCurve K⸨X⸩ ↦ V.toAffine.Point)
        (map_baseChange_functionFieldLaurentExpansion_eq_fracCurve W₁ W₂).symm
        (formalThetaPoint W₂ K⸨X⸩ f.formalSeries) := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [tautologicalPoint_zero, Affine.Point.mapAlong_zero, formalSeries_zero,
      formalThetaPoint_zero W₂ K⸨X⸩, _root_.map_zero]
  · obtain ⟨hns, hθ⟩ := formalThetaPoint_eq_some W₂ K⸨X⸩ φ.constantCoeff_formalSeries
      φ.formalSeries_ne_zero
    rw [formalSeries_ofIsogeny, hθ, AddEquiv.cast_apply,
      Affine.Point.cast_some (map_baseChange_functionFieldLaurentExpansion_eq_fracCurve W₁ W₂).symm,
      tautologicalPoint_ofIsogeny, Isogeny.tautologicalPoint_eq_map_genericPoint,
      Affine.genericPoint_eq_some, Affine.Point.map_some, Affine.Point.mapAlong_some]
    have hY : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY) =
        -1 / algebraMap (MvPowerSeries Unit K) K⸨X⸩
          (PowerSeries.subst φ.formalSeries W₂.formalW) := by
      have hw := φ.coe_subst_formalW_formalSeries
      simp only [_root_.map_neg, map_inv₀] at hw
      have h0 : algebraMap (MvPowerSeries Unit K) K⸨X⸩
          (PowerSeries.subst φ.formalSeries W₂.formalW) ≠ 0 :=
        W₂.algebraMap_subst_formalW_ne_zero φ.constantCoeff_formalSeries φ.formalSeries_ne_zero
      rw [_root_.LaurentSeries.coe_algebraMap] at h0
      rw [_root_.LaurentSeries.coe_algebraMap, eq_div_iff h0]
      have hw' : -((W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY))⁻¹) =
          ((PowerSeries.subst φ.formalSeries W₂.formalW : K⟦X⟧) : K⸨X⸩) := hw.symm
      have hy0 : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY) ≠ 0 := by
        intro hz
        rw [hz, inv_zero, _root_.neg_zero] at hw'
        exact h0 hw'.symm
      linear_combination
        -(W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericY)) * hw' -
          inv_mul_cancel₀ hy0
    have hX : W₁.functionFieldLaurentExpansion (φ.fieldPullback W₂.toAffine.genericX) =
        algebraMap (MvPowerSeries Unit K) K⸨X⸩ φ.formalSeries /
          algebraMap (MvPowerSeries Unit K) K⸨X⸩
            (PowerSeries.subst φ.formalSeries W₂.formalW) := by
      have hp := φ.coe_formalSeries
      simp only [map_div₀, _root_.map_neg, hY] at hp
      have h0 : algebraMap (MvPowerSeries Unit K) K⸨X⸩
          (PowerSeries.subst φ.formalSeries W₂.formalW) ≠ 0 :=
        W₂.algebraMap_subst_formalW_ne_zero φ.constantCoeff_formalSeries φ.formalSeries_ne_zero
      rw [_root_.LaurentSeries.coe_algebraMap] at hp h0 ⊢
      rw [div_eq_mul_inv (-1), neg_one_mul, div_neg, div_inv_eq_mul, neg_mul, neg_neg] at hp
      exact (eq_div_iff h0).mpr hp.symm
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hX, hY]

/-- **Addition of morphisms induces formal-group addition of their formal series.** -/
theorem formalSeries_add (f g : Hom W₁.toAffine W₂.toAffine) :
    (f + g).formalSeries =
      subst ![f.formalSeries, g.formalSeries] (formalGroup W₂).toPowerSeries := by
  classical
  have hfg0 : ∀ i : Fin 2, constantCoeff (![f.formalSeries, g.formalSeries] i) = 0 :=
    Fin.forall_fin_two.mpr ⟨f.constantCoeff_formalSeries, g.constantCoeff_formalSeries⟩
  refine formalThetaPoint_inj W₂ K⸨X⸩ (f + g).constantCoeff_formalSeries
    (constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hfg0) hfg0
      (formalGroup W₂).zero_constantCoeff) ?_
  rw [← formalThetaPoint_add W₂ K⸨X⸩ f.constantCoeff_formalSeries g.constantCoeff_formalSeries]
  have hf := map_functionFieldLaurentExpansion_tautologicalPoint f
  have hg := map_functionFieldLaurentExpansion_tautologicalPoint g
  have hfg := map_functionFieldLaurentExpansion_tautologicalPoint (f + g)
  rw [tautologicalPoint_add, Affine.Point.mapAlong_add, hf, hg, ← _root_.map_add] at hfg
  exact ((AddEquiv.cast _).injective hfg).symm

/-- **The formal series of morphisms `W₁ → W₂` as an additive homomorphism into `1`-variable
points of `formalGroup W₂`.** -/
noncomputable def toFormalGroupPoint :
    Hom W₁.toAffine W₂.toAffine →+ (formalGroup W₂).Point Unit where
  toFun f := ⟨f.formalSeries, .of_constantCoeff_zero f.constantCoeff_formalSeries⟩
  map_zero' := Subtype.ext formalSeries_zero
  map_add' f g := Subtype.ext (formalSeries_add f g)

/-- The underlying power series of `f.toFormalGroupPoint` is `f.formalSeries`. -/
@[simp]
theorem val_toFormalGroupPoint (f : Hom W₁.toAffine W₂.toAffine) :
    (f.toFormalGroupPoint).val = f.formalSeries := (rfl)

/-- **Negation of a morphism composes its formal series with the formal inverse of `W₂`.** -/
theorem formalSeries_neg (f : Hom W₁.toAffine W₂.toAffine) :
    (-f).formalSeries = PowerSeries.subst f.formalSeries (formalGroup W₂).addInvX := by
  have h := congrArg Subtype.val (_root_.map_neg (toFormalGroupPoint (W₁ := W₁) (W₂ := W₂)) f)
  simpa only [val_toFormalGroupPoint, FormalGroup.neg_apply] using h

/-- **Natural scalar multiplication of a morphism composes its formal series with
`nsmulSeries n`.** -/
theorem formalSeries_nsmul (n : ℕ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).nsmulSeries n) := by
  have h := congrArg Subtype.val (_root_.map_nsmul (toFormalGroupPoint (W₁ := W₁) (W₂ := W₂)) n f)
  simpa only [val_toFormalGroupPoint, ← (formalGroup W₂).subst_nsmulSeries] using h

/-- **Integer scalar multiplication of a morphism composes its formal series with
`zsmulSeries n`.** -/
theorem formalSeries_zsmul (n : ℤ) (f : Hom W₁.toAffine W₂.toAffine) :
    (n • f).formalSeries = PowerSeries.subst f.formalSeries ((formalGroup W₂).zsmulSeries n) := by
  have h := congrArg Subtype.val (_root_.map_zsmul (toFormalGroupPoint (W₁ := W₁) (W₂ := W₂)) n f)
  simpa only [val_toFormalGroupPoint, ← (formalGroup W₂).subst_zsmulSeries] using h

/-- **Two morphisms with the same formal series are equal.** -/
theorem formalSeries_injective :
    Function.Injective (formalSeries (W₁ := W₁) (W₂ := W₂)) := by
  intro f g h
  rw [← sub_eq_zero, ← formalSeries_eq_zero_iff]
  have hp : f.toFormalGroupPoint = g.toFormalGroupPoint := Subtype.ext h
  exact congrArg Subtype.val
    ((_root_.map_sub (toFormalGroupPoint (W₁ := W₁) (W₂ := W₂)) f g).trans (sub_eq_zero.mpr hp))

end Addition

section EndRing

variable (W : WeierstrassCurve K) [W.IsElliptic]

-- Not `@[simp]`: `Hom.one_def` reduces `1` to `Hom.id W`, which `formalSeries_id` simplifies.
/-- The multiplicative identity `1 : Hom W W` induces the formal series `X`. -/
theorem formalSeries_one : (1 : Hom W.toAffine W.toAffine).formalSeries = PowerSeries.X :=
  formalSeries_id W

/-- The natural-number endomorphism `(n : Hom W W)` induces `(formalGroup W).nsmulSeries n`. -/
@[simp]
theorem formalSeries_natCast (n : ℕ) :
    (n : Hom W.toAffine W.toAffine).formalSeries = (formalGroup W).nsmulSeries n := by
  rw [← nsmul_one, formalSeries_nsmul, formalSeries_one, PowerSeries.X_subst]

/-- The integer endomorphism `(n : Hom W W)` induces `(formalGroup W).zsmulSeries n`. -/
@[simp]
theorem formalSeries_intCast (n : ℤ) :
    (n : Hom W.toAffine W.toAffine).formalSeries = (formalGroup W).zsmulSeries n := by
  rw [← zsmul_one, formalSeries_zsmul, formalSeries_one, PowerSeries.X_subst]

end EndRing

end Hom

/-! ### Multiplication-by-`n` isogenies on the formal group -/

section MulByInt

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The multiplication-by-`n` isogeny induces `(formalGroup W).zsmulSeries n` on the formal
parameter** (Silverman IV.4.2). -/
@[simp]
theorem formalSeries_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n := by
  rw [← Hom.formalSeries_ofIsogeny, ofIsogeny_mulByIntIsogeny, Hom.formalSeries_zsmul,
    Hom.formalSeries_id, PowerSeries.X_subst]

-- Not `@[simp]`: `mulByIntIsogenyOfNeZero` is an `abbrev` of `mulByIntIsogeny`, so `simpNF`
-- handles it through `formalSeries_mulByIntIsogeny`.
/-- **For `n ≠ 0`, multiplication by `n` induces `(formalGroup W).zsmulSeries n`.** -/
theorem formalSeries_mulByIntIsogenyOfNeZero {n : ℤ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries = (formalGroup W).zsmulSeries n :=
  formalSeries_mulByIntIsogeny W _

/-- **The order of `(formalGroup W).zsmulSeries n` equals the inseparable degree of `[n]`.** -/
theorem _root_.WeierstrassCurve.order_zsmulSeries_formalGroup {n : ℤ} (hn : n ≠ 0) :
    ((formalGroup W).zsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine hn).inseparableDegree := by
  rw [← formalSeries_mulByIntIsogenyOfNeZero W hn, order_formalSeries]

/-- **The order of `(formalGroup W).nsmulSeries n` equals the inseparable degree of `[n]`.** -/
theorem _root_.WeierstrassCurve.order_nsmulSeries_formalGroup {n : ℕ} (hn : n ≠ 0) :
    ((formalGroup W).nsmulSeries n).order =
      (mulByIntIsogenyOfNeZero W.toAffine (Nat.cast_ne_zero.mpr hn)).inseparableDegree := by
  rw [← FormalGroup.zsmulSeries_natCast, W.order_zsmulSeries_formalGroup (Nat.cast_ne_zero.mpr hn)]

/-- **For `n ≠ 0`, `(formalGroup W).zsmulSeries n` is nonzero**, in every characteristic. -/
theorem _root_.WeierstrassCurve.zsmulSeries_formalGroup_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (formalGroup W).zsmulSeries n ≠ 0 := by
  rw [← formalSeries_mulByIntIsogenyOfNeZero W hn]
  exact (mulByIntIsogenyOfNeZero W.toAffine hn).formalSeries_ne_zero

/-- **For `n ≠ 0`, `(formalGroup W).nsmulSeries n` is nonzero**, in every characteristic. -/
theorem _root_.WeierstrassCurve.nsmulSeries_formalGroup_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (formalGroup W).nsmulSeries n ≠ 0 := by
  rw [← FormalGroup.zsmulSeries_natCast]
  exact W.zsmulSeries_formalGroup_ne_zero (Nat.cast_ne_zero.mpr hn)

end MulByInt

/-! ### Bundled formal-group homomorphisms -/

section FormalGroupHom

variable {K : Type*} [Field K] {W₁ W₂ W₃ : WeierstrassCurve K}

private theorem subst_eq_zero_iff_mvPowerSeries {σ : Type*} {q : MvPowerSeries σ K}
    (hq : constantCoeff q = 0) (hq0 : q ≠ 0) {f : K⟦X⟧} :
    PowerSeries.subst q f = 0 ↔ f = 0 := by
  have := MvPowerSeries.isDomain_of_isDomain (σ := σ) (R := K)
  refine ⟨fun hf0 ↦ ?_, fun h ↦ by simp [h, PowerSeries.subst_zero]⟩
  by_contra hf
  have hhs : PowerSeries.HasSubst q := .of_constantCoeff_zero hq
  have hmul : PowerSeries.subst q f =
      q ^ f.order.toNat * PowerSeries.subst q f.divXPowOrder := by
    conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f)]
    rw [PowerSeries.subst_mul hhs, PowerSeries.subst_pow hhs, PowerSeries.subst_X hhs]
  rw [hmul] at hf0
  rcases mul_eq_zero.mp hf0 with hpow | hdiv
  · exact hq0 (eq_zero_of_pow_eq_zero hpow)
  · have hc := PowerSeries.constantCoeff_subst_of_constantCoeff_zero hq f.divXPowOrder
    rw [hdiv, map_zero] at hc
    exact PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hf (by simpa using hc.symm)

private noncomputable def liftSubstRingHom {σ : Type*} (KK : Type*) [Field KK]
    [Algebra (MvPowerSeries σ K) KK] [IsFractionRing (MvPowerSeries σ K) KK]
    {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) : K⸨X⸩ →+* KK :=
  let S : K⟦X⟧ →+* KK :=
    (algebraMap (MvPowerSeries σ K) KK).comp
      (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hq)).toRingHom
  have hSinj : Function.Injective S := by
    refine (injective_iff_map_eq_zero S).mpr fun f hf ↦ ?_
    simp only [S, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      PowerSeries.coe_substAlgHom] at hf
    exact (subst_eq_zero_iff_mvPowerSeries hq hq0).mp
      ((map_eq_zero_iff _ (IsFractionRing.injective (MvPowerSeries σ K) KK)).mp hf)
  IsFractionRing.lift hSinj

private theorem liftSubstRingHom_coe {σ : Type*} (KK : Type*) [Field KK]
    [Algebra (MvPowerSeries σ K) KK] [IsFractionRing (MvPowerSeries σ K) KK]
    {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) (f : K⟦X⟧) :
    liftSubstRingHom KK hq hq0 (f : K⸨X⸩) =
      algebraMap (MvPowerSeries σ K) KK (PowerSeries.subst q f) := by
  rw [liftSubstRingHom, ← _root_.LaurentSeries.coe_algebraMap, IsFractionRing.lift_algebraMap]
  simp [PowerSeries.coe_substAlgHom]

private theorem liftSubstRingHom_comp_substAlgHom {σ : Type*} (KK : Type*) [Field KK]
    [Algebra (MvPowerSeries σ K) KK] [IsFractionRing (MvPowerSeries σ K) KK]
    {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0)
    {s : K⟦X⟧} (hs : PowerSeries.constantCoeff s = 0) (hs0 : s ≠ 0) :
    (liftSubstRingHom KK hq hq0).comp
        (TauCeti.LaurentSeries.substAlgHom hs hs0).toRingHom =
      liftSubstRingHom KK (PowerSeries.constantCoeff_subst_eq_zero hq s hs)
        ((subst_eq_zero_iff_mvPowerSeries hq hq0).not.mpr hs0) := by
  refine IsFractionRing.ringHom_ext (A := K⟦X⟧) fun f ↦ ?_
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    _root_.LaurentSeries.coe_algebraMap, TauCeti.LaurentSeries.substAlgHom_coe,
    liftSubstRingHom_coe, liftSubstRingHom_coe,
    PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero' hs) (.of_constantCoeff_zero hq)]

private theorem pointMap_map_formalThetaPointMap [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) {σ : Type*} (KK : Type*) [Field KK] [DecidableEq KK]
    [Algebra (MvPowerSeries σ K) KK] [IsFractionRing (MvPowerSeries σ K) KK]
    {q : MvPowerSeries σ K} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    (Hom.ofIsogeny (φ.map
      ((algebraMap (MvPowerSeries σ K) KK).comp (algebraMap K (MvPowerSeries σ K))))).pointMap
        (formalThetaPointMap W₁ KK q) =
      formalThetaPointMap W₂ KK (PowerSeries.subst q φ.formalSeries) := by
  set ρ := algebraMap (MvPowerSeries σ K) KK
  set ι : K →+* KK := ρ.comp (algebraMap K (MvPowerSeries σ K))
  set q' := PowerSeries.subst q φ.formalSeries
  have hq' : constantCoeff q' = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hq φ.formalSeries φ.constantCoeff_formalSeries
  have hq'0 : q' ≠ 0 := (subst_eq_zero_iff_mvPowerSeries hq hq0).not.mpr φ.formalSeries_ne_zero
  obtain ⟨hns₁, hθ₁⟩ := formalThetaPointMap_eq_some W₁ KK hq hq0
  obtain ⟨hns₂, hθ₂⟩ := formalThetaPointMap_eq_some W₂ KK hq' hq'0
  rw [hθ₁, hθ₂]
  set E₁ : W₁.toAffine.FunctionField →+* KK :=
    (liftSubstRingHom KK hq hq0).comp W₁.functionFieldLaurentExpansion.toRingHom
  set E₂ : W₂.toAffine.FunctionField →+* KK :=
    (liftSubstRingHom KK hq' hq'0).comp W₂.functionFieldLaurentExpansion.toRingHom
  have hEcomp : E₁.comp φ.fieldPullback.toRingHom = E₂ := by
    ext f
    simp only [E₁, E₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      φ.functionFieldLaurentExpansion_fieldPullback]
    exact RingHom.congr_fun (liftSubstRingHom_comp_substAlgHom KK hq hq0
      φ.constantCoeff_formalSeries φ.formalSeries_ne_zero) (W₂.functionFieldLaurentExpansion f)
  have hEY {V : WeierstrassCurve K} {t : MvPowerSeries σ K} (ht : constantCoeff t = 0)
      (ht0 : t ≠ 0) :
      ((liftSubstRingHom KK ht ht0).comp V.functionFieldLaurentExpansion.toRingHom)
          V.toAffine.genericY =
        -1 / ρ (PowerSeries.subst t V.formalW) := by
    have hw :=
      congrArg (liftSubstRingHom KK ht ht0) V.functionFieldLaurentExpansion_neg_inv_genericY
    simp only [map_neg, map_inv₀, liftSubstRingHom_coe] at hw
    have h0 : ρ (PowerSeries.subst t V.formalW) ≠ 0 :=
      V.algebraMap_subst_formalW_ne_zero ht ht0
    have hy0 : ((liftSubstRingHom KK ht ht0).comp V.functionFieldLaurentExpansion.toRingHom)
        V.toAffine.genericY ≠ 0 :=
      (map_ne_zero_iff _ (RingHom.injective _)).mpr V.toAffine.genericY_ne_zero
    rw [eq_div_iff h0]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hy0 ⊢
    linear_combination -((liftSubstRingHom KK ht ht0) (V.functionFieldLaurentExpansion
      V.toAffine.genericY)) * hw - inv_mul_cancel₀ hy0
  have hEX {V : WeierstrassCurve K} {t : MvPowerSeries σ K} (ht : constantCoeff t = 0)
      (ht0 : t ≠ 0) :
      ((liftSubstRingHom KK ht ht0).comp V.functionFieldLaurentExpansion.toRingHom)
          V.toAffine.genericX =
        ρ t / ρ (PowerSeries.subst t V.formalW) := by
    have hp := congrArg (liftSubstRingHom KK ht ht0)
      V.functionFieldLaurentExpansion_neg_genericX_div_genericY
    simp only [map_div₀, map_neg, liftSubstRingHom_coe,
      PowerSeries.subst_X (.of_constantCoeff_zero ht)] at hp
    have hy := hEY (V := V) ht ht0
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hy ⊢
    have h0 : ρ (PowerSeries.subst t V.formalW) ≠ 0 :=
      V.algebraMap_subst_formalW_ne_zero ht ht0
    rw [hy] at hp
    field_simp [h0] at hp ⊢
    exact hp
  have hEval (p : K[X][Y]) :
      E₁ (algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
          (Affine.CoordinateRing.mk W₁.toAffine p)) =
        (p.map (Polynomial.mapRingHom ι)).evalEval
          (ρ q / ρ (PowerSeries.subst q W₁.formalW))
          (-1 / ρ (PowerSeries.subst q W₁.formalW)) := by
    let _ : Algebra K KK := ι.toAlgebra
    let fAlg : W₁.toAffine.CoordinateRing →ₐ[K] KK :=
      { toRingHom := E₁.comp (algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField)
        commutes' c := by
          change E₁ (algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
            (algebraMap K W₁.toAffine.CoordinateRing c)) = ι c
          rw [← IsScalarTower.algebraMap_apply K W₁.toAffine.CoordinateRing
            W₁.toAffine.FunctionField c]
          simp only [E₁, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            AlgHom.commutes, ι, ρ]
          rw [IsScalarTower.algebraMap_apply K K⟦X⟧ K⸨X⸩ c, _root_.LaurentSeries.coe_algebraMap,
            liftSubstRingHom_coe, PowerSeries.algebraMap_eq, PowerSeries.subst_C,
            c_eq_algebraMap] }
    have hmk := Affine.CoordinateRing.algHom_mk_eq_evalEval fAlg p
    have hfX : fAlg (AdjoinRoot.of W₁.toAffine.polynomial Polynomial.X) =
        ρ q / ρ (PowerSeries.subst q W₁.formalW) := by
      change E₁ (algebraMap _ _ (AdjoinRoot.of W₁.toAffine.polynomial Polynomial.X)) = _
      rw [← AdjoinRoot.mk_C, ← Affine.CoordinateRing.mk, ← Affine.genericX_def]
      exact hEX hq hq0
    have hfY : fAlg (AdjoinRoot.root W₁.toAffine.polynomial) =
        -1 / ρ (PowerSeries.subst q W₁.formalW) := by
      change E₁ (algebraMap _ _ (AdjoinRoot.root W₁.toAffine.polynomial)) = _
      rw [← AdjoinRoot.mk_X, ← Affine.genericY_def]
      exact hEY hq hq0
    rw [hfX, hfY] at hmk
    exact hmk
  have hval (g : W₁.toAffine.FunctionField) :
      (Affine.CoordinateRing.pointPlace hns₁.1).valuation
        (W₁.toAffine.map ι).FunctionField
        (Affine.FunctionField.map W₁.toAffine ι g -
          algebraMap KK (W₁.toAffine.map ι).FunctionField (E₁ g)) < 1 := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W₁.toAffine.CoordinateRing) g
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    obtain ⟨d, rfl⟩ := AdjoinRoot.mk_surjective b
    set d' := d.map (Polynomial.mapRingHom ι)
    set num' := p.map (Polynomial.mapRingHom ι) -
      Polynomial.C (Polynomial.C (E₁ (algebraMap _ _ (Affine.CoordinateRing.mk W₁.toAffine p) /
        algebraMap _ _ (Affine.CoordinateRing.mk W₁.toAffine d)))) * d'
    have hb0 : algebraMap W₁.toAffine.CoordinateRing W₁.toAffine.FunctionField
        (Affine.CoordinateRing.mk W₁.toAffine d) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero hb)
    have hdEval : d'.evalEval (ρ q / ρ (PowerSeries.subst q W₁.formalW))
        (-1 / ρ (PowerSeries.subst q W₁.formalW)) ≠ 0 := by
      rw [← hEval d]
      exact (map_ne_zero_iff E₁ E₁.injective).mpr hb0
    have hnumEval : num'.evalEval (ρ q / ρ (PowerSeries.subst q W₁.formalW))
        (-1 / ρ (PowerSeries.subst q W₁.formalW)) = 0 := by
      simp only [num', d', Polynomial.evalEval_sub, Polynomial.evalEval_mul, Polynomial.evalEval_C,
        Polynomial.eval_C, ← hEval p, ← hEval d, map_div₀]
      exact sub_eq_zero.mpr (div_mul_cancel₀ _ ((map_ne_zero_iff E₁ E₁.injective).mpr hb0)).symm
    have hfrac : Affine.FunctionField.map W₁.toAffine ι
          (algebraMap _ _ (Affine.CoordinateRing.mk W₁.toAffine p) /
            algebraMap _ _ (Affine.CoordinateRing.mk W₁.toAffine d)) -
          algebraMap KK (W₁.toAffine.map ι).FunctionField
            (E₁ (algebraMap _ _ (Affine.CoordinateRing.mk W₁.toAffine p) /
              algebraMap _ _ (Affine.CoordinateRing.mk W₁.toAffine d))) =
        algebraMap (W₁.toAffine.map ι).CoordinateRing _
            (Affine.CoordinateRing.mk (W₁.toAffine.map ι) num') /
          algebraMap (W₁.toAffine.map ι).CoordinateRing _
            (Affine.CoordinateRing.mk (W₁.toAffine.map ι) d') := by
      have hd'0 : algebraMap (W₁.toAffine.map ι).CoordinateRing
          (W₁.toAffine.map ι).FunctionField
          (Affine.CoordinateRing.mk (W₁.toAffine.map ι) d') ≠ 0 := by
        rw [← Affine.CoordinateRing.map_mk, ← Affine.FunctionField.map_algebraMap_coordinateRing]
        exact (map_ne_zero_iff _ (Affine.FunctionField.map W₁.toAffine ι).injective).mpr hb0
      rw [map_div₀, Affine.FunctionField.map_algebraMap_coordinateRing,
        Affine.FunctionField.map_algebraMap_coordinateRing, Affine.CoordinateRing.map_mk,
        Affine.CoordinateRing.map_mk, eq_div_iff hd'0, sub_mul, div_mul_cancel₀ _ hd'0]
      simp only [num', d', map_sub, map_mul, Affine.CoordinateRing.mk, AdjoinRoot.mk_C]
      rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply KK (Polynomial KK) (W₁.toAffine.map ι).CoordinateRing,
        ← IsScalarTower.algebraMap_apply KK (W₁.toAffine.map ι).CoordinateRing
          (W₁.toAffine.map ι).FunctionField]
    rw [hfrac]
    exact Affine.CoordinateRing.valuation_pointPlace_div_lt_one _ hns₁.1 hdEval hnumEval
  rw [Hom.pointMap_eq_iff, Hom.tautologicalPoint_ofIsogeny,
    Isogeny.tautologicalPoint_eq_map_genericPoint, Affine.genericPoint_eq_some,
    Affine.Point.map_some, Affine.Point.equivBaseChangeSelf_some _ hns₂,
    Affine.some_sub_baseChange_mem_polePoints_iff, Affine.coe_pointEquivDegreeOnePlace_some]
  simp only [Place.valuation_ofPrime]
  have hx2 : E₁ (φ.fieldPullback W₂.toAffine.genericX) =
      ρ q' / ρ (PowerSeries.subst q' W₂.formalW) := by
    change (E₁.comp φ.fieldPullback.toRingHom) W₂.toAffine.genericX = _
    rw [hEcomp]
    exact hEX hq' hq'0
  have hy2 : E₁ (φ.fieldPullback W₂.toAffine.genericY) =
      -1 / ρ (PowerSeries.subst q' W₂.formalW) := by
    change (E₁.comp φ.fieldPullback.toRingHom) W₂.toAffine.genericY = _
    rw [hEcomp]
    exact hEY hq' hq'0
  have hmapX : (φ.map ι).fieldPullback (W₂.toAffine.map ι).genericX =
      Affine.FunctionField.map W₁.toAffine ι (φ.fieldPullback W₂.toAffine.genericX) := by
    rw [← Affine.FunctionField.map_genericX, map_fieldPullback_map]
  have hmapY : (φ.map ι).fieldPullback (W₂.toAffine.map ι).genericY =
      Affine.FunctionField.map W₁.toAffine ι (φ.fieldPullback W₂.toAffine.genericY) := by
    rw [← Affine.FunctionField.map_genericY, map_fieldPullback_map]
  rw [hmapX, hmapY, ← hx2, ← hy2]
  exact ⟨hval _, hval _⟩

/-- **An isogeny induces a homomorphism of formal group laws** `formalGroup W₁ → formalGroup W₂`
(Silverman IV.4.2). -/
noncomputable def formalGroupHom [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := φ.formalSeries
  zero_constantCoeff := φ.constantCoeff_formalSeries
  hom := by
    classical
    have : W₁.IsElliptic := φ.isElliptic
    let KK := FractionRing (MvPowerSeries (Fin 2) K)
    set ι : K →+* KK :=
      (algebraMap (MvPowerSeries (Fin 2) K) KK).comp (algebraMap K (MvPowerSeries (Fin 2) K))
    have hx0 (i : Fin 2) : constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := constantCoeff_X i
    have hxne (i : Fin 2) : (X i : MvPowerSeries (Fin 2) K) ≠ 0 :=
      nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
    have hFne : (formalGroup W₁).toPowerSeries ≠ 0 := by
      intro h0
      have h1 := (formalGroup W₁).lin_coeff_X
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hsum := congrArg
      (Hom.ofIsogeny (φ.map ι)).pointMap
      (formalThetaPointMap_add W₁ KK (hx0 0) (hx0 1))
    have hself : subst ![X 0, X 1] (formalGroup W₁).toPowerSeries =
        (formalGroup W₁).toPowerSeries := by
      have hX : (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 2) K) = X := by
        funext i
        fin_cases i <;> rfl
      rw [hX, subst_self, id_eq]
    have hφ0 (i : Fin 2) :
        constantCoeff
          (![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) K) φ.formalSeries,
            PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) K) φ.formalSeries] i) = 0 := by
      fin_cases i <;>
        exact PowerSeries.constantCoeff_subst_eq_zero (hx0 _) _ φ.constantCoeff_formalSeries
    rw [hself, Hom.pointMap_add,
      pointMap_map_formalThetaPointMap φ KK (hx0 0) (hxne 0),
      pointMap_map_formalThetaPointMap φ KK (hx0 1) (hxne 1),
      pointMap_map_formalThetaPointMap φ KK (formalGroup W₁).zero_constantCoeff hFne,
      formalThetaPointMap_add W₂ KK
        (PowerSeries.constantCoeff_subst_eq_zero (hx0 0) _ φ.constantCoeff_formalSeries)
        (PowerSeries.constantCoeff_subst_eq_zero (hx0 1) _ φ.constantCoeff_formalSeries)] at hsum
    have heq := (formalThetaPointMap_inj W₂ KK
      (constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hφ0) hφ0
        (formalGroup W₂).zero_constantCoeff)
      (PowerSeries.constantCoeff_subst_eq_zero (formalGroup W₁).zero_constantCoeff _
        φ.constantCoeff_formalSeries) hsum).symm
    refine heq.trans ?_
    congr 1
    funext i
    fin_cases i <;> simp [PowerSeries.toMvPowerSeries_eq_subst]

/-- The underlying power series of `φ.formalGroupHom` is `φ.formalSeries`. -/
@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalGroupHom.toPowerSeries = φ.formalSeries := (rfl)

/-- The identity isogeny induces the identity formal-group homomorphism. -/
@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Isogeny.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext : 1
  simp

/-- Composition of isogenies induces composition of formal-group homomorphisms. -/
@[simp]
theorem formalGroupHom_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (ψ : Isogeny W₂.toAffine W₃.toAffine) (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ψ.comp φ).formalGroupHom = ψ.formalGroupHom.comp φ.formalGroupHom := by
  ext : 1
  simp

/-- Multiplication by `n` induces `(formalGroup W).zsmulHom n` on the formal group. -/
@[simp]
theorem formalGroupHom_mulByIntIsogeny (W : WeierstrassCurve K) [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W.toAffine n ≠ 0) :
    (mulByIntIsogeny W.toAffine hn).formalGroupHom = (formalGroup W).zsmulHom n := by
  ext : 1
  simp

namespace Hom

/-- **Every morphism `f : Hom W₁ W₂` induces a homomorphism of formal group laws**
`formalGroup W₁ → formalGroup W₂`. -/
noncomputable def formalGroupHom [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    FormalGroupHom (formalGroup W₁) (formalGroup W₂) where
  toPowerSeries := f.formalSeries
  zero_constantCoeff := f.constantCoeff_formalSeries
  hom := by
    rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
    · rw [formalSeries_zero]
      exact (FormalGroup.homDefect_eq_zero_iff _ _).mp FormalGroup.homDefect_zero
    · rw [formalSeries_ofIsogeny]
      exact φ.formalGroupHom.hom

/-- The underlying power series of `f.formalGroupHom` is `f.formalSeries`. -/
@[simp]
theorem formalGroupHom_toPowerSeries [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine) :
    f.formalGroupHom.toPowerSeries = f.formalSeries := (rfl)

/-- On an isogeny, `Hom.formalGroupHom` agrees with `Isogeny.formalGroupHom`. -/
@[simp]
theorem formalGroupHom_ofIsogeny [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    (ofIsogeny φ).formalGroupHom = φ.formalGroupHom := by
  ext : 1
  simp

/-- The identity morphism induces the identity formal-group homomorphism. -/
@[simp]
theorem formalGroupHom_id (W : WeierstrassCurve K) [W.IsElliptic] :
    (Hom.id W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) := by
  ext : 1
  simp

-- Not `@[simp]`: `Hom.one_def` reduces `1` to `Hom.id W`, which `formalGroupHom_id` simplifies.
/-- The multiplicative identity `1 : Hom W W` induces the identity formal-group homomorphism. -/
theorem formalGroupHom_one (W : WeierstrassCurve K) [W.IsElliptic] :
    (1 : Hom W.toAffine W.toAffine).formalGroupHom = FormalGroupHom.id (formalGroup W) :=
  formalGroupHom_id W

/-- Composition of morphisms induces composition of formal-group homomorphisms. -/
@[simp]
theorem formalGroupHom_comp [W₂.IsElliptic] [W₃.IsElliptic]
    (g : Hom W₂.toAffine W₃.toAffine) (f : Hom W₁.toAffine W₂.toAffine) :
    (g.comp f).formalGroupHom = g.formalGroupHom.comp f.formalGroupHom := by
  ext : 1
  simp

/-- The natural-number endomorphism `(n : Hom W W)` induces `(formalGroup W).nsmulHom n`. -/
@[simp]
theorem formalGroupHom_natCast (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ) :
    (n : Hom W.toAffine W.toAffine).formalGroupHom = (formalGroup W).nsmulHom n := by
  ext : 1
  simp

/-- The integer endomorphism `(n : Hom W W)` induces `(formalGroup W).zsmulHom n`. -/
@[simp]
theorem formalGroupHom_intCast (W : WeierstrassCurve K) [W.IsElliptic] (n : ℤ) :
    (n : Hom W.toAffine W.toAffine).formalGroupHom = (formalGroup W).zsmulHom n := by
  ext : 1
  simp

/-- The scalar multiple `n • Hom.id W` induces `(formalGroup W).zsmulHom n`. -/
theorem formalGroupHom_zsmul_id (W : WeierstrassCurve K) [W.IsElliptic] (n : ℤ) :
    (n • Hom.id W.toAffine).formalGroupHom = (formalGroup W).zsmulHom n := by
  ext : 1
  rw [formalGroupHom_toPowerSeries, formalSeries_zsmul, formalSeries_id, PowerSeries.X_subst,
    FormalGroup.zsmulHom_toPowerSeries]

end Hom

end FormalGroupHom

end TauCeti.Isogeny
