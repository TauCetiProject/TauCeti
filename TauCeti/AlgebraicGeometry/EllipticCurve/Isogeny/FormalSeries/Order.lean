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
-- Proof-only: Frobenius factorization of an isogeny into a Frobenius power and a separable factor.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
-- Proof-only: separable isogenies of elliptic curves are unramified at every place.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
-- Proof-only: valuation of a nonzero power series in `K⸨X⸩`.
import TauCeti.RingTheory.LaurentSeries.Basic
-- Proof-only: `PowerSeries.order_subst` for composing orders under substitution.
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The order of an isogeny's formal series

For an isogeny `φ : W₁ → W₂` of Weierstrass curves over a field `K`, the formal power series
`φ.formalSeries ∈ K⟦X⟧` expands the pulled-back uniformizer `-x₂ / y₂` at infinity in terms of
`-x₁ / y₁`. Comparing its valuation in `K⸨X⸩` with the place-theoretic ramification formula
`v_∞(φ* f) = v_∞(f) ^ e(∞₁ ∣ ∞₂)` identifies the order of `φ.formalSeries` with the ramification
index of `φ` at the place at infinity, for every Weierstrass curve
(`order_formalSeries_eq_ramificationIdx`).

For an elliptic curve, every separable isogeny is unramified everywhere
(`Isogeny.ramificationIdx_eq_one`), so its formal series has order `1`
(`order_formalSeries_eq_one_of_isSeparable`). On the other hand, the `r`-fold relative Frobenius
`F^r : W → W⁽ᵖʳ⁾` pulls back `-x / y` to `(-x / y) ^ (p ^ r)`, so its formal series is
`X ^ (p ^ r)` (`formalSeries_iterateRelativeFrobeniusIsogeny`). Combining these via the Frobenius
factorization `φ = ψ ∘ F^r` (`exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq`) shows
that for every isogeny of elliptic curves, the order of `φ.formalSeries` equals the inseparable
degree of `φ` (`order_formalSeries_eq_inseparableDegree`).

## Main results

* `TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.formalSeries_relativeFrobeniusIsogeny`: the formal series of `F^r` is
  `X ^ (p ^ r)` and that of `F` is `X ^ p`.
* `TauCeti.Isogeny.order_formalSeries_eq_ramificationIdx`: the order of `φ.formalSeries` is the
  ramification index at infinity, for any Weierstrass curves.
* `TauCeti.Isogeny.order_formalSeries_eq_one_of_isSeparable`: a separable isogeny of elliptic
  curves has formal series of order `1`.
* `TauCeti.Isogeny.order_formalSeries_eq_inseparableDegree`: the order of `φ.formalSeries` equals
  the inseparable degree of `φ`, for any isogeny of elliptic curves.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.12, III.4.10 and IV.4.
-/

public section

open WeierstrassCurve
open scoped LaurentSeries PowerSeries WithZero

namespace TauCeti.Isogeny

variable {K : Type*} [Field K]

/-- **The formal series of the `r`-fold relative Frobenius is `X ^ (p ^ r)`.** -/
@[simp]
theorem formalSeries_iterateRelativeFrobeniusIsogeny (p : ℕ) [ExpChar K p]
    (W : WeierstrassCurve K) (r : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W.toAffine r).formalSeries = PowerSeries.X ^ p ^ r := by
  rw [formalSeries_eq_iff, map_div₀, map_neg,
    fieldPullback_iterateRelativeFrobeniusIsogeny_genericX,
    fieldPullback_iterateRelativeFrobeniusIsogeny_genericY]
  have : ExpChar W.toAffine.FunctionField p :=
    expChar_of_injective_algebraMap (algebraMap K W.toAffine.FunctionField).injective p
  have hneg : -(W.toAffine.genericX ^ p ^ r) = (-W.toAffine.genericX) ^ p ^ r := by
    simpa only [iterateFrobenius_def] using
      (map_neg (iterateFrobenius W.toAffine.FunctionField p r) W.toAffine.genericX).symm
  rw [hneg, ← div_pow, map_pow, map_pow,
    W.functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- **The formal series of the relative Frobenius is `X ^ p`.** -/
@[simp]
theorem formalSeries_relativeFrobeniusIsogeny (p : ℕ) [ExpChar K p] (W : WeierstrassCurve K) :
    (relativeFrobeniusIsogeny p W.toAffine).formalSeries = PowerSeries.X ^ p := by
  rw [formalSeries_eq_iff, map_div₀, map_neg,
    fieldPullback_relativeFrobeniusIsogeny_genericX,
    fieldPullback_relativeFrobeniusIsogeny_genericY]
  have : ExpChar W.toAffine.FunctionField p :=
    expChar_of_injective_algebraMap (algebraMap K W.toAffine.FunctionField).injective p
  have hneg : -(W.toAffine.genericX ^ p) = (-W.toAffine.genericX) ^ p := by
    simpa only [frobenius_def] using
      (map_neg (frobenius W.toAffine.FunctionField p) W.toAffine.genericX).symm
  rw [hneg, ← div_pow, map_pow, map_pow,
    W.functionFieldLaurentExpansion_neg_genericX_div_genericY]

/-- **The order of an isogeny's formal series is the ramification index at infinity.**
This holds for every isogeny of Weierstrass curves, without assuming ellipticity. -/
theorem order_formalSeries_eq_ramificationIdx {W₁ W₂ : WeierstrassCurve K}
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField]
    (h : ∀ z, algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField z =
      φ.fieldPullback z) :
    φ.formalSeries.order =
      (Place.ramificationIdx W₂.toAffine.FunctionField (Place.infinity W₁.toAffine) : ℕ∞) := by
  have := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  have := φ.finiteDimensional_functionField h
  have hres : (Place.infinity W₁.toAffine).restrict K W₂.toAffine.FunctionField =
      Place.infinity W₂.toAffine := by
    rw [Place.restrict_eq_iff_isEquiv_comap, Place.valuation_infinity, Place.valuation_infinity]
    have hcomp : W₁.toAffine.infinityPlace.comap
        (algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField) =
        W₁.toAffine.infinityPlace.comap φ.fieldPullback.toRingHom := by
      ext z
      exact congrArg W₁.toAffine.infinityPlace (h z)
    rw [hcomp]
    exact φ.isEquiv_comap_infinityPlace
  have hval := Place.valuation_algebraMap_restrict K W₂.toAffine.FunctionField
    (Place.infinity W₁.toAffine) (-W₂.toAffine.genericX / W₂.toAffine.genericY)
  rw [hres, Place.valuation_infinity, Place.valuation_infinity, h,
    Affine.infinityPlace_neg_genericX_div_genericY, ← WithZero.exp_nsmul, Int.nsmul_eq_mul,
    mul_neg, mul_one, ← W₁.valuation_functionFieldLaurentExpansion, ← φ.coe_formalSeries,
    TauCeti.LaurentSeries.valuation_coe φ.formalSeries_ne_zero] at hval
  have htoNat : φ.formalSeries.order.toNat =
      Place.ramificationIdx W₂.toAffine.FunctionField (Place.infinity W₁.toAffine) := by
    have hneg := WithZero.exp_injective hval
    omega
  rw [← ENat.natCast_toNat (PowerSeries.order_eq_top.not.mpr φ.formalSeries_ne_zero), htoNat]

/-- **A separable isogeny of elliptic curves has formal series of order `1`.** -/
theorem order_formalSeries_eq_one_of_isSeparable {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalSeries.order = 1 := by
  let _ : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    φ.fieldPullback.toRingHom.toAlgebra
  rw [order_formalSeries_eq_ramificationIdx φ (fun _ ↦ rfl),
    Isogeny.ramificationIdx_eq_one φ (fun _ ↦ rfl) (Place.infinity W₁.toAffine), Nat.cast_one]

/-- **The order of an isogeny's formal series equals its inseparable degree** (Silverman IV.4):
factoring `φ = ψ ∘ F^r` with `ψ` separable gives `φ.formalSeries = ψ.formalSeries(X ^ (p ^ r))`,
whose order is `p ^ r = deg_i φ`. -/
theorem order_formalSeries_eq_inseparableDegree {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalSeries.order = (φ.inseparableDegree : ℕ∞) := by
  let p := ringExpChar K
  obtain ⟨r, ψ, hψ_sep, hcomp⟩ :=
    exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  have hinsep : φ.inseparableDegree = p ^ r :=
    inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq hcomp
  rw [hinsep, ← hcomp, formalSeries_comp, formalSeries_iterateRelativeFrobeniusIsogeny,
    PowerSeries.order_subst (by simp [expChar_ne_zero K p]),
    order_formalSeries_eq_one_of_isSeparable ψ, mul_one, PowerSeries.order_X_pow]

end TauCeti.Isogeny

end
