/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
import TauCeti.RingTheory.LaurentSeries.Basic
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The order of the formal power series of an isogeny

For an isogeny `φ : W₁ → W₂` of elliptic curves over a field `K`, the formal power series
`φ.formalSeries ∈ K⟦X⟧` expands the pulled-back uniformizer `-x₂ / y₂` in the source uniformizer
`z₁ = -x₁ / y₁`. This file computes its order:

  `φ.formalSeries.order = φ.inseparableDegree`

in every characteristic, including characteristics `2` and `3`.

The proof follows the factorisation `φ = χ ∘ F^r` through the `r`-fold relative Frobenius
(`TauCeti.Isogeny.exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq`).

* On the `r`-fold relative Frobenius `F^r : W → W⁽ᵖʳ⁾`, the pullback raises `x` and `y` to the
  `p ^ r`-th power, hence raises `-x / y` to the `p ^ r`-th power in every exponential
  characteristic `p`, so `(F^r).formalSeries = X ^ (p ^ r)`.
* A separable isogeny `χ` of elliptic curves is unramified at every place
  (`TauCeti.Isogeny.ramificationIdx_eq_one`), in particular at the place at infinity, so it sends
  the target uniformizer `-x₂ / y₂` to a uniformizer of the source at infinity; hence
  `χ.formalSeries` has order `1`.
* Composition of isogenies corresponds to substitution of formal series (`formalSeries_comp`),
  and substitution multiplies power-series orders (`PowerSeries.order_subst`), yielding
  `ord φ.formalSeries = p ^ r = deg_i φ`.

In particular, `φ` is separable exactly when its formal series has order `1`, equivalently when
its linear coefficient is nonzero (Silverman IV.4.2).

## Main results

* `TauCeti.Isogeny.formalSeries_relativeFrobeniusIsogeny`: the formal series of relative
  Frobenius is `X ^ p`.
* `TauCeti.Isogeny.formalSeries_iterateRelativeFrobeniusIsogeny`: the formal series of the
  `r`-fold relative Frobenius is `X ^ (p ^ r)`.
* `TauCeti.Isogeny.order_formalSeries_of_isSeparable`: a separable isogeny of elliptic curves
  has formal series of order `1`.
* `TauCeti.Isogeny.order_formalSeries_eq_inseparableDegree`: the order of the formal series of
  an isogeny of elliptic curves equals its inseparable degree.
* `TauCeti.Isogeny.isSeparable_iff_order_formalSeries_eq_one` and
  `TauCeti.Isogeny.isSeparable_iff_coeff_one_formalSeries_ne_zero`: separability of an isogeny
  characterized by order `1` or nonzero linear term of its formal series.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.12, III.4.10 and IV.4.
-/

public section

open WeierstrassCurve HahnSeries
open scoped LaurentSeries PowerSeries WithZero

namespace TauCeti.Isogeny

variable {K : Type*} [Field K]

/-- The formal series of the `r`-fold relative Frobenius isogeny is `X ^ (p ^ r)`. -/
@[simp]
theorem formalSeries_iterateRelativeFrobeniusIsogeny (p : ℕ) [ExpChar K p]
    (W : WeierstrassCurve K) (r : ℕ) :
    (iterateRelativeFrobeniusIsogeny p W.toAffine r).formalSeries =
      PowerSeries.X ^ (p ^ r) := by
  have : ExpChar W.toAffine.FunctionField p :=
    expChar_of_injective_algebraMap (algebraMap K W.toAffine.FunctionField).injective p
  refine (formalSeries_eq_iff _ _).mpr ?_
  have hneg : -(W.toAffine.genericX ^ (p ^ r)) = (-W.toAffine.genericX) ^ (p ^ r) := by
    simpa only [iterateFrobenius_def] using
      (map_neg (iterateFrobenius W.toAffine.FunctionField p r) W.toAffine.genericX).symm
  rw [map_div₀, map_neg, fieldPullback_iterateRelativeFrobeniusIsogeny_genericX,
    fieldPullback_iterateRelativeFrobeniusIsogeny_genericY, hneg, ← div_pow,
    map_pow W.functionFieldLaurentExpansion,
    functionFieldLaurentExpansion_neg_genericX_div_genericY, PowerSeries.coe_pow]

/-- The formal series of the relative Frobenius isogeny is `X ^ p`. -/
@[simp]
theorem formalSeries_relativeFrobeniusIsogeny (p : ℕ) [ExpChar K p]
    (W : WeierstrassCurve K) :
    (relativeFrobeniusIsogeny p W.toAffine).formalSeries = PowerSeries.X ^ p := by
  have hcast : ∀ (f : K →+* K) (hf : f = frobenius K p)
      (φ : Isogeny W.toAffine (W.map f).toAffine),
      φ = (congrArg W.map hf.symm ▸ relativeFrobeniusIsogeny p W.toAffine) →
      φ.formalSeries = (relativeFrobeniusIsogeny p W.toAffine).formalSeries := by
    rintro _ rfl _ rfl; rfl
  rw [← hcast _ (iterateFrobenius_one K p) (iterateRelativeFrobeniusIsogeny p W.toAffine 1)
    (iterateRelativeFrobeniusIsogeny_one p W.toAffine),
    formalSeries_iterateRelativeFrobeniusIsogeny, pow_one]

/-- **A separable isogeny of elliptic curves has formal series of order `1`.** By Hurwitz's
formula a separable isogeny is unramified at every place, so it pulls back the uniformizer
`-x₂ / y₂` at infinity to a uniformizer at infinity of the source. -/
theorem order_formalSeries_of_isSeparable {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    φ.formalSeries.order = 1 := by
  let _ : Algebra W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    φ.fieldPullback.toRingHom.toAlgebra
  have halg : ∀ z, algebraMap W₂.toAffine.FunctionField W₁.toAffine.FunctionField z =
      φ.fieldPullback z := fun _ ↦ rfl
  have := isScalarTower_of_algebraMap_eq_fieldPullback φ halg
  have := φ.finiteDimensional_functionField halg
  -- The place at infinity of `W₁` restricts to that of `W₂`, with ramification index `1`.
  have hrest : (Place.infinity W₁.toAffine).restrict K W₂.toAffine.FunctionField =
      Place.infinity W₂.toAffine := by
    rw [Place.restrict_eq_iff_isEquiv_comap, Place.valuation_infinity, Place.valuation_infinity]
    exact φ.isEquiv_comap_infinityPlace
  have hram : Place.ramificationIdx W₂.toAffine.FunctionField (Place.infinity W₁.toAffine) = 1 :=
    ramificationIdx_eq_one φ halg (Place.infinity W₁.toAffine)
  -- Pullback therefore preserves the valuation of the uniformizer `-x₂ / y₂`.
  have hval : Valued.v (φ.formalSeries : K⸨X⸩) = WithZero.exp (-1) := by
    have h := Place.valuation_algebraMap_restrict K W₂.toAffine.FunctionField
      (Place.infinity W₁.toAffine) (-W₂.toAffine.genericX / W₂.toAffine.genericY)
    rw [hrest, hram, pow_one, Place.valuation_infinity, Place.valuation_infinity, halg,
      Affine.infinityPlace_neg_genericX_div_genericY] at h
    rw [φ.coe_formalSeries, W₁.valuation_functionFieldLaurentExpansion, h]
  rw [TauCeti.LaurentSeries.valuation_coe φ.formalSeries_ne_zero] at hval
  have htoNat : φ.formalSeries.order.toNat = 1 := by
    have := WithZero.exp_injective hval
    omega
  rw [← ENat.natCast_toNat (PowerSeries.order_eq_top.not.mpr φ.formalSeries_ne_zero), htoNat,
    Nat.cast_one]

/-- **The order of the formal series of an isogeny equals its inseparable degree.** Factoring
`φ = χ ∘ F^r` into the `r`-fold relative Frobenius and a separable isogeny `χ`, the formal series
is `χ.formalSeries (X ^ (p ^ r))`, whose order is `p ^ r = deg_i φ`. -/
theorem order_formalSeries_eq_inseparableDegree {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    φ.formalSeries.order = φ.inseparableDegree := by
  obtain ⟨p, _⟩ := ExpChar.exists K
  obtain ⟨r, χ, hχsep, hχ⟩ := exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  have hinsep : φ.inseparableDegree = p ^ r :=
    inseparableDegree_eq_pow_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ
  have hpr : p ^ r ≠ 0 := (expChar_pow_pos K p r).ne'
  rw [hinsep, ← hχ, formalSeries_comp, formalSeries_iterateRelativeFrobeniusIsogeny,
    PowerSeries.order_subst (by rw [map_pow, PowerSeries.constantCoeff_X, zero_pow hpr]),
    PowerSeries.order_X_pow, order_formalSeries_of_isSeparable χ, mul_one]

/-- **Separability from the order of the formal series.** An isogeny of elliptic curves is
separable exactly when its formal power series has order `1`. -/
theorem isSeparable_iff_order_formalSeries_eq_one {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      φ.formalSeries.order = 1 := by
  rw [← inseparableDegree_eq_one_iff_isSeparable, order_formalSeries_eq_inseparableDegree,
    Nat.cast_eq_one]

/-- **Separability from the linear coefficient of the formal series** (Silverman IV.4.2): an
isogeny of elliptic curves is separable exactly when the coefficient of `X` in its formal power
series is nonzero. -/
theorem isSeparable_iff_coeff_one_formalSeries_ne_zero {W₁ W₂ : WeierstrassCurve K}
    [W₂.IsElliptic] (φ : Isogeny W₁.toAffine W₂.toAffine) :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField ↔
      PowerSeries.coeff 1 φ.formalSeries ≠ 0 := by
  rw [isSeparable_iff_order_formalSeries_eq_one, ← Nat.cast_one, PowerSeries.order_eq_nat]
  refine ⟨And.left, fun h ↦ ⟨h, fun i hi ↦ ?_⟩⟩
  rw [Nat.lt_one_iff.mp hi, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_formalSeries]

end TauCeti.Isogeny
