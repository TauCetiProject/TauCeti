/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Order
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Inverse
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Neg
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
import TauCeti.Algebra.CharP.Lemmas
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The order of the formal power series of an isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `K`, with local parameter expansion
`φ.formalSeries` in `z = -x / y` at the point at infinity. This file computes `φ.formalSeries` for
negation and iterated relative Frobenius, and proves that the power-series order of `φ.formalSeries`
equals the inseparable degree `φ.inseparableDegree`.

The proof follows the Frobenius factorisation `φ = χ ∘ F^r` (Silverman II.2.12), where `F^r` is
the `r`-fold relative Frobenius of degree `p ^ r = φ.inseparableDegree` and `χ` is separable:

1. If `χ` is separable, Hurwitz's theorem makes `χ` unramified at infinity
   (`TauCeti.Isogeny.ramificationIdx_eq_one`), so the pulled-back uniformizer `-x₂ / y₂` remains a
   uniformizer on the source curve and `χ.formalSeries` has order `1`.
2. The `r`-fold relative Frobenius raises both generic coordinates to the `p ^ r`-th power, and
   `(-a) ^ (p ^ r) = -(a ^ (p ^ r))` in exponential characteristic `p`, so its formal series is
   `X ^ (p ^ r)`.
3. Since composition of isogenies corresponds to substitution of formal series and orders multiply
   under substitution over a domain, `φ.formalSeries` has order `p ^ r * 1 = φ.inseparableDegree`.

In particular, `φ` is separable if and only if `φ.formalSeries` has order `1`, equivalently has a
nonzero linear coefficient.

## Main results

* `TauCeti.Isogeny.formalSeries_negIsogeny`: `(negIsogeny W.toAffine).formalSeries =
  W.formalInverse`, for any Weierstrass curve `W`.
* `TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.formalSeries_relativeFrobeniusIsogeny`: the formal series of `F^n` is
  `X ^ (p ^ n)`, and that of `F` is `X ^ p`.
* `TauCeti.Isogeny.order_formalSeries`: `φ.formalSeries.order = φ.inseparableDegree`.
* `TauCeti.Isogeny.order_formalSeries_eq_one_iff_isSeparable` and
  `TauCeti.Isogeny.coeff_one_formalSeries_ne_zero_iff_isSeparable`: `φ` is separable if and only if
  `φ.formalSeries` has order `1`, equivalently nonzero linear coefficient.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.12, III.4.10 and IV.4.
-/

public section

open WeierstrassCurve HahnSeries
open scoped LaurentSeries PowerSeries WithZero

namespace TauCeti.Isogeny

section NegAndFrobenius

variable {K : Type*} [Field K]

/-- The formal power series of the negation isogeny `[-1]` on a Weierstrass curve is its formal
inverse `ι(z) = -z / (1 - a₁ z - a₃ w(z))`. -/
@[simp]
theorem formalSeries_negIsogeny (W : WeierstrassCurve K) :
    (negIsogeny W.toAffine).formalSeries = W.formalInverse := by
  rw [formalSeries_eq_iff]
  have hy : W.toAffine.genericY ≠ 0 := W.toAffine.genericY_ne_zero
  have hrat : -W.toAffine.genericX /
      (W⁄W.toAffine.FunctionField).toAffine.negY W.toAffine.genericX W.toAffine.genericY =
        -((-W.toAffine.genericX / W.toAffine.genericY) /
          (1 - algebraMap K _ W.a₁ * (-W.toAffine.genericX / W.toAffine.genericY) -
            algebraMap K _ W.a₃ * (-W.toAffine.genericY⁻¹))) := by
    simp only [Affine.negY, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃]
    field_simp
    rw [← div_neg]
    congr 1
    ring
  have hunit : (formalInverseDenom W : K⸨X⸩) *
      (PowerSeries.invOfUnit (formalInverseDenom W) 1 : K⟦X⟧) = 1 := by
    rw [← map_mul, mul_invOfUnit_formalInverseDenom, map_one]
  have hd0 : (formalInverseDenom W : K⸨X⸩) ≠ 0 := left_ne_zero_of_mul_eq_one hunit
  rw [map_div₀, map_neg, fieldPullback_negIsogeny_genericX, fieldPullback_negIsogeny_genericY,
    hrat, map_neg, map_div₀, functionFieldLaurentExpansion_neg_genericX_div_genericY]
  simp only [map_sub, map_one, map_mul, AlgHom.commutes,
    functionFieldLaurentExpansion_neg_genericX_div_genericY,
    functionFieldLaurentExpansion_neg_inv_genericY]
  have hdenom : (1 : K⸨X⸩) - algebraMap K K⸨X⸩ W.a₁ * (PowerSeries.X : K⟦X⟧) -
      algebraMap K K⸨X⸩ W.a₃ * (formalW W : K⸨X⸩) = (formalInverseDenom W : K⸨X⸩) := by
    rw [formalInverseDenom_def]
    simp [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq]
  rw [hdenom, formalInverse_def, map_neg, map_mul, neg_inj, eq_div_iff hd0, mul_assoc,
    mul_comm _ (formalInverseDenom W : K⸨X⸩), hunit, mul_one]

/-- The formal power series of the `n`-fold relative Frobenius `F^n : W → W⁽ᵖⁿ⁾` is
`X ^ (p ^ n)`. -/
@[simp]
theorem formalSeries_iterateRelativeFrobeniusIsogeny (p : ℕ) [ExpChar K p]
    (W : WeierstrassCurve K) (n : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W.toAffine n).formalSeries = PowerSeries.X ^ p ^ n := by
  have := expChar_of_injective_algebraMap (algebraMap K W.toAffine.FunctionField).injective p
  rw [formalSeries_eq_iff, map_pow, map_div₀, map_neg,
    fieldPullback_iterateRelativeFrobeniusIsogeny_genericX,
    fieldPullback_iterateRelativeFrobeniusIsogeny_genericY,
    ← TauCeti.neg_pow_expChar_pow p n W.toAffine.genericX, ← div_pow, map_pow,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- The formal power series of the relative Frobenius isogeny `F : W → W⁽ᵖ⁾` is `X ^ p`. -/
@[simp]
theorem formalSeries_relativeFrobeniusIsogeny (p : ℕ) [ExpChar K p] (W : WeierstrassCurve K) :
    (relativeFrobeniusIsogeny p W.toAffine).formalSeries = PowerSeries.X ^ p := by
  have := expChar_of_injective_algebraMap (algebraMap K W.toAffine.FunctionField).injective p
  have hx : (relativeFrobeniusIsogeny p W.toAffine).fieldPullback
      (W.map (frobenius K p)).toAffine.genericX = W.toAffine.genericX ^ p := by
    rw [Affine.genericX_eq_algebraMap, Affine.genericX_eq_algebraMap,
      fieldPullback_relativeFrobeniusIsogeny_X]
  have hy : (relativeFrobeniusIsogeny p W.toAffine).fieldPullback
      (W.map (frobenius K p)).toAffine.genericY = W.toAffine.genericY ^ p := by
    rw [Affine.genericY_def, Affine.genericY_def, AdjoinRoot.mk_X, AdjoinRoot.mk_X,
      ← Affine.CoordinateRing.map_root, fieldPullback_relativeFrobeniusIsogeny_coordinateRingMap]
  have hneg : (-W.toAffine.genericX) ^ p = -(W.toAffine.genericX ^ p) := by
    simpa using TauCeti.neg_pow_expChar_pow p 1 W.toAffine.genericX
  rw [formalSeries_eq_iff, map_pow, map_div₀, map_neg, hx, hy, ← hneg, ← div_pow, map_pow,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

end NegAndFrobenius

section Order

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- A separable isogeny has formal power series of order `1`. -/
theorem order_formalSeries_eq_one_of_isSeparable
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalSeries.order = 1 := by
  let _ : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    φ.fieldPullback.toRingHom.toAlgebra
  have halg : ∀ z, algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField z =
      φ.fieldPullback z := fun _ ↦ rfl
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback halg
  have := φ.finiteDimensional_functionField halg
  set P₁ : Place K W₁.toAffine.FunctionField := Place.infinity W₁.toAffine with hP₁
  let P₂ : Place K W₂.toAffine.FunctionField := Place.infinity W₂.toAffine
  have hres : P₁.restrict K W₂.toAffine.FunctionField = P₂ :=
    (Place.restrict_eq_iff_isEquiv_comap K W₂.toAffine.FunctionField P₁ P₂).mpr
      (Valuation.isEquiv_iff_val_le_one.mpr <| by
        simpa only [P₁, P₂, Place.valuation_infinity, Valuation.comap_apply, halg,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
          fun {x} ↦ Valuation.isEquiv_iff_val_le_one.mp φ.isEquiv_comap_infinityPlace (x := x))
  have hram : Place.ramificationIdx W₂.toAffine.FunctionField P₁ = 1 :=
    ramificationIdx_eq_one φ halg P₁
  have hval : Valued.v (φ.formalSeries : K⸨X⸩) = WithZero.exp (-1 : ℤ) := by
    rw [coe_formalSeries, valuation_functionFieldLaurentExpansion, ← Place.valuation_infinity,
      ← hP₁, ← halg, Place.valuation_algebraMap_restrict K W₂.toAffine.FunctionField P₁, hres,
      hram, pow_one, Place.valuation_infinity, Affine.infinityPlace_neg_genericX_div_genericY]
  rw [TauCeti.LaurentSeries.valuation_coe φ.formalSeries_ne_zero] at hval
  have hord : φ.formalSeries.order.toNat = 1 := by
    have := WithZero.exp_injective hval
    omega
  rw [← ENat.natCast_toNat (PowerSeries.order_eq_top.not.mpr φ.formalSeries_ne_zero), hord,
    Nat.cast_one]

/-- **The order of the formal series of an isogeny is its inseparable degree.** -/
@[simp]
theorem order_formalSeries : φ.formalSeries.order = φ.inseparableDegree := by
  let p := ringExpChar K
  obtain ⟨r, χ, hχ, hcomp⟩ := exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  have := hχ
  have hinsep : φ.inseparableDegree = p ^ r :=
    inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq hcomp
  rw [hinsep, ← hcomp, formalSeries_comp (W₂ := W₁.map (iterateFrobenius K p r)),
    PowerSeries.order_subst (constantCoeff_formalSeries _),
    formalSeries_iterateRelativeFrobeniusIsogeny,
    order_formalSeries_eq_one_of_isSeparable χ, mul_one, PowerSeries.order_X_pow]

/-- **An isogeny is separable if and only if its formal series has order `1`.** -/
theorem order_formalSeries_eq_one_iff_isSeparable :
    φ.formalSeries.order = 1 ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField := by
  rw [order_formalSeries, ← Nat.cast_one, Nat.cast_inj, inseparableDegree_eq_one_iff_isSeparable]

/-- **An isogeny is separable if and only if its formal series has a nonzero linear coefficient**
(Silverman IV.4.2(c) together with III.5.5). -/
theorem coeff_one_formalSeries_ne_zero_iff_isSeparable :
    PowerSeries.coeff 1 φ.formalSeries ≠ 0 ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField := by
  rw [← order_formalSeries_eq_one_iff_isSeparable, ← Nat.cast_one (R := ℕ∞),
    PowerSeries.order_eq_nat]
  refine ⟨fun h ↦ ⟨h, fun i hi ↦ ?_⟩, fun h ↦ h.1⟩
  rw [Nat.lt_one_iff.mp hi, PowerSeries.coeff_zero_eq_constantCoeff]
  exact φ.constantCoeff_formalSeries

/-- A separable isogeny has nonzero linear coefficient in its formal series. -/
theorem coeff_one_formalSeries_ne_zero_of_isSeparable
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    PowerSeries.coeff 1 φ.formalSeries ≠ 0 :=
  φ.coeff_one_formalSeries_ne_zero_iff_isSeparable.mpr inferInstance

end Order

end TauCeti.Isogeny
