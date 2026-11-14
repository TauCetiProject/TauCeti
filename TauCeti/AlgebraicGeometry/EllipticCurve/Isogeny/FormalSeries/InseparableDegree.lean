/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Differential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import Mathlib.Algebra.CharP.Algebra
import TauCeti.Algebra.CharP.Lemmas
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Formal series of the relative Frobenius and the order–inseparable-degree formula

In exponential characteristic `p`, the relative Frobenius `F : W → W⁽ᵖ⁾` pulls the parameter
`-x / y` back to `(-x)ᵖ / yᵖ = (-x / y)ᵖ` (including in characteristic `2`, since `(-x)² = -x²`),
so its formal series is `X ^ p` (`formalSeries_relativeFrobeniusIsogeny`), and that of the `n`-fold
iterate `Fⁿ : W → W⁽ᵖⁿ⁾` is `X ^ p ^ n` (`formalSeries_iterateRelativeFrobeniusIsogeny`). Neither
statement requires `W` to be elliptic.

Combining this with the Frobenius factorisation `φ = χ ∘ Fʳ` (`χ` separable, `p ^ r = deg_i φ`) and
the order-one characterisation of separable isogenies (`order_formalSeries_eq_one_of_isSeparable`)
identifies the order of `φ.formalSeries` for every isogeny of elliptic curves over every field:

`φ.formalSeries.order = φ.inseparableDegree`.

## Main results

* `TauCeti.Isogeny.formalSeries_relativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny`: `(Fⁿ).formalSeries = X ^ p ^ n`.
* `TauCeti.Isogeny.order_formalSeries` and `TauCeti.Isogeny.toNat_order_formalSeries`: the order of
  `φ.formalSeries` equals `φ.inseparableDegree`.
* `TauCeti.Isogeny.coeff_inseparableDegree_formalSeries_ne_zero` and
  `TauCeti.Isogeny.coeff_formalSeries_eq_zero_of_lt_inseparableDegree`: `φ.formalSeries` vanishes
  below `deg_i φ` and has nonzero coefficient in degree `deg_i φ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11, II.2.12, and IV.4.
-/

public section

open WeierstrassCurve
open scoped LaurentSeries PowerSeries

namespace TauCeti.Isogeny

variable {K : Type*} [Field K]

/-- **The formal series of the `n`-fold relative Frobenius `Fⁿ : W → W⁽ᵖⁿ⁾` is `X ^ p ^ n`.**
No ellipticity assumption on `W` is required. -/
@[simp]
theorem formalSeries_iterateRelativeFrobeniusIsogeny (p : ℕ) [ExpChar K p]
    (W : WeierstrassCurve K) (n : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W.toAffine n).formalSeries = PowerSeries.X ^ p ^ n := by
  have : ExpChar W.toAffine.FunctionField p :=
    expChar_of_injective_algebraMap (algebraMap K W.toAffine.FunctionField).injective p
  apply (formalSeries_eq_iff (W₂ := W.map (iterateFrobenius K p n)) _ _).mpr
  rw [PowerSeries.coe_pow, map_div₀, map_neg,
    fieldPullback_iterateRelativeFrobeniusIsogeny_genericX,
    fieldPullback_iterateRelativeFrobeniusIsogeny_genericY, ← TauCeti.neg_pow_expChar_pow p n,
    ← div_pow, map_pow W.functionFieldLaurentExpansion,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- **The formal series of the relative Frobenius `F : W → W⁽ᵖ⁾` is `X ^ p`.**
No ellipticity assumption on `W` is required. -/
@[simp]
theorem formalSeries_relativeFrobeniusIsogeny (p : ℕ) [ExpChar K p]
    (W : WeierstrassCurve K) :
    (relativeFrobeniusIsogeny p W.toAffine).formalSeries = PowerSeries.X ^ p := by
  have : ExpChar W.toAffine.FunctionField p :=
    expChar_of_injective_algebraMap (algebraMap K W.toAffine.FunctionField).injective p
  have hneg : (-W.toAffine.genericX) ^ p = -W.toAffine.genericX ^ p := by
    simpa only [pow_one] using TauCeti.neg_pow_expChar_pow p 1 W.toAffine.genericX
  apply (formalSeries_eq_iff (W₂ := W.map (frobenius K p)) _ _).mpr
  rw [PowerSeries.coe_pow, map_div₀, map_neg, fieldPullback_relativeFrobeniusIsogeny_genericX,
    fieldPullback_relativeFrobeniusIsogeny_genericY, ← hneg, ← div_pow,
    map_pow W.functionFieldLaurentExpansion,
    functionFieldLaurentExpansion_neg_genericX_div_genericY]

section Elliptic

variable {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- **The order of an isogeny's formal series equals its inseparable degree**: factoring
`φ = χ ∘ Fʳ` with `χ` separable gives `φ.formalSeries = χ.formalSeries(X ^ p ^ r)`, of order
`p ^ r · 1 = deg_i φ`. -/
@[simp]
theorem order_formalSeries : φ.formalSeries.order = φ.inseparableDegree := by
  let p := ringExpChar K
  obtain ⟨r, χ, hsep, hχ⟩ := exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  have hr : φ.inseparableDegree = p ^ r :=
    inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ
  have hc : PowerSeries.constantCoeff ((PowerSeries.X : K⟦X⟧) ^ p ^ r) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (expChar_pow_pos K p r).ne']
  rw [hr, ← hχ, formalSeries_comp (W₂ := W₁.map (iterateFrobenius K p r)),
    formalSeries_iterateRelativeFrobeniusIsogeny, PowerSeries.order_subst hc,
    PowerSeries.order_X_pow,
    order_formalSeries_eq_one_of_isSeparable (W₁ := W₁.map (iterateFrobenius K p r)) χ, mul_one]

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
