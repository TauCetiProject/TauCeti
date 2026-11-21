/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace.Restrict
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
import TauCeti.RingTheory.LaurentSeries.Basic
import TauCeti.RingTheory.PowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The order of the formal power series of an isogeny

Let `φ : W₁ → W₂` be an isogeny of Weierstrass curves over a field `K`. Its formal power series
`φ.formalSeries : K⟦X⟧` expands the pulled-back parameter `-x₂/y₂` at the point at infinity of `W₁`
in the parameter `z₁ = -x₁/y₁`. Both parameters are uniformizers at the places at infinity, so the
order of vanishing of `φ.formalSeries` is the ramification index of the place at infinity of `W₁`
over that of `W₂`.

When `W₂` is elliptic, every separable isogeny is unramified
(`TauCeti.Isogeny.ramificationIdx_eq_one`), so its formal series has order `1` and nonzero linear
coefficient. On the other hand, the `r`-fold relative Frobenius `F^r : W₁ → W₁⁽ᵖʳ⁾` raises `-x/y`
to its `p ^ r`-th power, so its formal series is `X ^ (p ^ r)`. Factoring an arbitrary isogeny `φ`
as `φ = φ_sep ∘ F^r` with `φ_sep` separable
(`TauCeti.Isogeny.exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq`) and reading off
orders under substitution (`PowerSeries.order_subst`) identifies the order of `φ.formalSeries` —
and hence the ramification index at infinity — with the inseparable degree of `φ`.

## Main results

* `TauCeti.Isogeny.order_formalSeries_eq_ramificationIdx`: the order of `φ.formalSeries` is the
  ramification index of the place at infinity along `φ`.
* `TauCeti.Isogeny.formalSeries_relativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny`: the formal series of relative
  Frobenius and its `n`-fold iterate are `X ^ p` and `X ^ (p ^ n)`.
* `TauCeti.Isogeny.order_formalSeries`: when `W₂` is elliptic, the order of `φ.formalSeries` is
  the inseparable degree of `φ`.
* `TauCeti.Isogeny.ramificationIdx_infinity_eq_inseparableDegree`: the ramification index at
  infinity of an isogeny to an elliptic curve equals its inseparable degree.
* `TauCeti.Isogeny.order_formalSeries_eq_one_iff_isSeparable` and
  `TauCeti.Isogeny.coeff_one_formalSeries_ne_zero_iff_isSeparable`: an isogeny to an elliptic
  curve is separable exactly when its formal series has order `1`, equivalently nonzero linear
  coefficient.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.12, III.4.10 and IV.4.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped LaurentSeries PowerSeries WithZero

namespace TauCeti.Isogeny

section General

variable {K : Type*} [Field K]

/-- **The order of an isogeny's formal series is the ramification index at infinity**, for any
Weierstrass curves (nonsingular or not). -/
theorem order_formalSeries_eq_ramificationIdx {W₁ W₂ : WeierstrassCurve K}
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    (h : ∀ z, algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField z =
      φ.fieldPullback z) :
    φ.formalSeries.order =
      Place.ramificationIdx W₂.toAffine.FunctionField (Place.infinity W₁.toAffine) := by
  -- Both `-x₁/y₁` and `-x₂/y₂` have normalized valuation `exp (-1)` at infinity, so scaling the
  -- target valuation by the ramification index matches the power-series order of the pullback.
  have := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  have := φ.finiteDimensional_functionField h
  set z₂ := -W₂.toAffine.genericX / W₂.toAffine.genericY
  have hval := Place.valuation_algebraMap_restrict K W₂.toAffine.FunctionField
    (Place.infinity W₁.toAffine) z₂
  rw [restrict_infinity φ h, h z₂, Place.valuation_infinity, Place.valuation_infinity,
    infinityPlace_neg_genericX_div_genericY, ← WithZero.exp_nsmul, Int.nsmul_eq_mul, mul_neg_one,
    ← W₁.valuation_functionFieldLaurentExpansion, ← φ.coe_formalSeries,
    TauCeti.LaurentSeries.valuation_coe φ.formalSeries_ne_zero] at hval
  have heq : φ.formalSeries.order.toNat =
      Place.ramificationIdx W₂.toAffine.FunctionField (Place.infinity W₁.toAffine) := by
    have := WithZero.exp_inj.mp hval
    omega
  rw [← heq]
  exact (ENat.natCast_toNat (PowerSeries.order_eq_top.not.mpr φ.formalSeries_ne_zero)).symm

/-- **The formal series of the `n`-fold relative Frobenius is `X ^ (p ^ n)`.** -/
@[simp]
theorem formalSeries_iterateRelativeFrobeniusIsogeny (p : ℕ) [ExpChar K p]
    (W : WeierstrassCurve K) (n : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W.toAffine n).formalSeries = PowerSeries.X ^ p ^ n := by
  apply (formalSeries_eq_iff _ _).mpr
  set f := iterateFrobenius K p n
  have hparam : -(W.map f).toAffine.genericX / (W.map f).toAffine.genericY =
      FunctionField.map W.toAffine f (-W.toAffine.genericX / W.toAffine.genericY) := by
    rw [map_div₀, map_neg, FunctionField.map_genericX, FunctionField.map_genericY]
  rw [hparam, fieldPullback_iterateRelativeFrobeniusIsogeny_map, PowerSeries.coe_pow, map_pow,
    W.functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- **The formal series of the relative Frobenius isogeny is `X ^ p`.** -/
@[simp]
theorem formalSeries_relativeFrobeniusIsogeny (p : ℕ) [ExpChar K p] (W : WeierstrassCurve K) :
    (relativeFrobeniusIsogeny p W.toAffine).formalSeries = PowerSeries.X ^ p := by
  apply (formalSeries_eq_iff _ _).mpr
  have hparam : -(W.map (frobenius K p)).toAffine.genericX /
      (W.map (frobenius K p)).toAffine.genericY =
      FunctionField.map W.toAffine (frobenius K p)
        (-W.toAffine.genericX / W.toAffine.genericY) := by
    rw [map_div₀, map_neg, FunctionField.map_genericX, FunctionField.map_genericY]
  rw [hparam, fieldPullback_relativeFrobeniusIsogeny_map, PowerSeries.coe_pow, map_pow,
    W.functionFieldLaurentExpansion_neg_genericX_div_genericY]

end General

section Elliptic

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **A separable isogeny to an elliptic curve has formal series of order one.** -/
theorem order_formalSeries_eq_one_of_isSeparable
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalSeries.order = 1 := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have h : ∀ z, algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField z =
      φ.fieldPullback z := φ.fieldPullback.algebraMap_toAlgebra_apply
  rw [order_formalSeries_eq_ramificationIdx φ h, ramificationIdx_eq_one φ h, Nat.cast_one]

/-- **The order of the formal series of an isogeny to an elliptic curve is its inseparable degree**
(Silverman II.2.12, III.4.10(b), IV.4). -/
-- Handle composites and `[n]` before `formalSeries_comp` or `formalSeries_mulByIntIsogeny`
-- rewrites `.formalSeries`.
@[simp↓]
theorem order_formalSeries : φ.formalSeries.order = φ.inseparableDegree := by
  -- Factoring `φ = χ ∘ F^r` with `χ` separable gives
  -- `φ.formalSeries = χ.formalSeries(X ^ (p ^ r))`.
  let p := ringExpChar K
  obtain ⟨r, χ, hχ, rfl⟩ :=
    exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  set F := iterateRelativeFrobeniusIsogeny p W₁.toAffine r
  rw [formalSeries_comp, PowerSeries.order_subst F.constantCoeff_formalSeries,
    formalSeries_iterateRelativeFrobeniusIsogeny, PowerSeries.order_X_pow,
    order_formalSeries_eq_one_of_isSeparable χ, mul_one,
    inseparableDegree_comp, inseparableDegree_eq_one_of_isSeparable χ, one_mul,
    inseparableDegree_eq_degree_of_isPurelyInseparable F,
    degree_iterateRelativeFrobeniusIsogeny, Nat.cast_pow]

/-- **The ramification index at infinity of an isogeny to an elliptic curve is its inseparable
degree.** -/
theorem ramificationIdx_infinity_eq_inseparableDegree
    [Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    (h : ∀ z, algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField z =
      φ.fieldPullback z) :
    Place.ramificationIdx W₂.toAffine.FunctionField (Place.infinity W₁.toAffine) =
      φ.inseparableDegree := by
  exact_mod_cast (φ.order_formalSeries_eq_ramificationIdx h).symm.trans φ.order_formalSeries

/-- **An isogeny to an elliptic curve is separable if and only if its formal series has order
one.** -/
theorem order_formalSeries_eq_one_iff_isSeparable :
    φ.formalSeries.order = 1 ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField := by
  rw [order_formalSeries, ← Nat.cast_one, Nat.cast_inj, inseparableDegree_eq_one_iff_isSeparable]

/-- **An isogeny to an elliptic curve is separable if and only if the linear coefficient of its
formal series is nonzero.** -/
theorem coeff_one_formalSeries_ne_zero_iff_isSeparable :
    PowerSeries.coeff 1 φ.formalSeries ≠ 0 ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField := by
  rw [← order_formalSeries_eq_one_iff_isSeparable,
    PowerSeries.order_eq_one_iff_of_constantCoeff_eq_zero φ.constantCoeff_formalSeries]

/-- **A separable isogeny to an elliptic curve has nonzero linear coefficient in its formal
series.** -/
theorem coeff_one_formalSeries_ne_zero_of_isSeparable
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    PowerSeries.coeff 1 φ.formalSeries ≠ 0 :=
  φ.coeff_one_formalSeries_ne_zero_iff_isSeparable.mpr inferInstance

/-- The linear coefficient of the formal series of an isogeny to an elliptic curve is a unit of the
base field if and only if the isogeny is separable. -/
theorem isUnit_coeff_one_formalSeries_iff_isSeparable :
    IsUnit (PowerSeries.coeff 1 φ.formalSeries) ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField := by
  rw [isUnit_iff_ne_zero, coeff_one_formalSeries_ne_zero_iff_isSeparable]

/-- **The `ℕ`-valued order of an isogeny's formal series equals its inseparable degree.** -/
theorem toNat_order_formalSeries : φ.formalSeries.order.toNat = φ.inseparableDegree := by
  rw [order_formalSeries, ENat.toNat_natCast]

/-- **The leading coefficient of `φ.formalSeries` sits in degree `φ.inseparableDegree`.** -/
theorem coeff_inseparableDegree_formalSeries_ne_zero :
    PowerSeries.coeff φ.inseparableDegree φ.formalSeries ≠ 0 := by
  have h := PowerSeries.coeff_order φ.formalSeries_ne_zero
  rwa [toNat_order_formalSeries] at h

/-- **All coefficients of `φ.formalSeries` strictly below `φ.inseparableDegree` vanish.** -/
theorem coeff_formalSeries_eq_zero_of_lt_inseparableDegree {n : ℕ}
    (hn : n < φ.inseparableDegree) :
    PowerSeries.coeff n φ.formalSeries = 0 :=
  PowerSeries.coeff_of_lt_order n (by rw [order_formalSeries]; exact Nat.cast_lt.mpr hn)

end Elliptic

end TauCeti.Isogeny

end
