/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.RingTheory.MvPowerSeries.Inverse
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The formal inverse of a Weierstrass curve

In the `(z, w)`-chart of `WeierstrassCurve.formalW`, where `x = z / w` and `y = -1 / w`, the
negative of the point with parameter `z` has parameter `ι(z) = -z / (1 - a₁ z - a₃ w(z))`. This
file constructs that series and proves it is an involution.

The denominator is `formalInverseDenom`; its constant coefficient is `1`, so it is a unit, which is
what makes `formalInverse` a power series at all.

## Main definitions

* `WeierstrassCurve.formalInverseDenom`: the series `1 - a₁ z - a₃ w(z)` inverted in `ι`.
* `WeierstrassCurve.formalInverse`: the parameter `ι(z)` of the negative point.

## Main results

* `WeierstrassCurve.subst_formalInverse_self`: `ι(ι(z)) = z`, the formal inverse is an
  involution. This is the formal-series form of `-(-P) = P`.
* `WeierstrassCurve.subst_formalInverse_formalW` and
  `WeierstrassCurve.subst_formalInverse_formalInverseDenom`: the two substitution identities the
  involution is assembled from, giving the `w`-coordinate and the denominator at the negative
  point.
* `WeierstrassCurve.subst_formalInverse_eq`, `WeierstrassCurve.subst_formalInverseDenom_eq`,
  `WeierstrassCurve.algebraMap_subst_formalInverseDenom_eq`, and
  `WeierstrassCurve.subst_formalW_subst_formalInverse`: parameter-level forms of the formal
  inverse, its denominator, and `w(ι(q))`.
* `WeierstrassCurve.isUnit_formalInverseDenom`: the denominator is a unit.
* `WeierstrassCurve.constantCoeff_formalInverse` and `WeierstrassCurve.subst_formalInverse_ne_zero`:
  `ι(0) = 0`, so `ι` may itself be substituted into a power series
  (`WeierstrassCurve.hasSubst_formalInverse`), and `ι(q) ≠ 0` over a domain when `q ≠ 0` and
  `constantCoeff q = 0`.

## Implementation notes

The substitution identities are proved through the uniqueness of the solution of the
`w`-equation (`WeierstrassCurve.eq_subst_formalW_of_wEquation`) rather than by comparing
coefficients: `w ∘ ι` and the candidate `-w · u⁻¹` both solve that equation at the parameter
`ι`, and a solution with vanishing constant coefficient is unique.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean` — declarations `uSeries`,
`constantCoeff_uSeries`, `mul_invOfUnit_uSeries`, `isUnit_uSeries`, `inverseSeries`,
`constantCoeff_inverseSeries`, `hasSubst_inverseSeries`, `subst_inverseSeries_invOfUnit`,
`subst_inverseSeries_wSeries`, `subst_inverseSeries_uSeries` and `subst_inverseSeries_self`.

The source's `uSeries` is renamed `formalInverseDenom` here. It must not be called `formalU`: that
name is already taken, in `FormalGroup/WExpansion.lean`, by the unit part `w(z) / z ^ 3`, which
is a different series (it is the source's `vSeries`). The source proves the substitution
identities through its own private `wStep` recursion; this file uses the `w`-equation API of
`FormalGroup/WExpansion.lean` instead, so the source's `wStepAt` lemmas are not ported.

The single-parameter helpers `subst_formalInverseDenom_mul`, `subst_formalInverse_eq`,
`subst_formalInverseDenom_eq`, and `subst_formalW_subst_formalInverse` are likewise adapted
from `single_u_mul`, `single_iota_eq`, `single_u_eq`, and `single_wIota` in
`EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean` (at the same commit), proved as
transports of the one-variable identities above along `PowerSeries.subst q`.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The denominator of the formal inverse -/

/-- The denominator `1 - a₁ z - a₃ w(z)` of the formal inverse.

Up to sign and a factor of `w`, this is the `y`-coordinate of the negative of the point with
parameter `z`, in the coordinates `x = z / w`, `y = -1 / w`. -/
noncomputable def formalInverseDenom : PowerSeries R :=
  1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * formalW W

/-- The defining formula for `formalInverseDenom`. -/
theorem formalInverseDenom_def :
    formalInverseDenom W =
      1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * formalW W :=
  (rfl)

/-- The denominator of the formal inverse is `1` at the origin, which is what makes it a unit. -/
@[simp]
theorem constantCoeff_formalInverseDenom :
    PowerSeries.constantCoeff (formalInverseDenom W) = 1 := by
  rw [formalInverseDenom_def]
  simp

/-- The denominator times its `invOfUnit` is `1`. -/
theorem mul_invOfUnit_formalInverseDenom :
    formalInverseDenom W * PowerSeries.invOfUnit (formalInverseDenom W) 1 = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simp)

/-- The denominator of the formal inverse is a unit. -/
theorem isUnit_formalInverseDenom : IsUnit (formalInverseDenom W) :=
  IsUnit.of_mul_eq_one _ (mul_invOfUnit_formalInverseDenom W)

/-! ### The formal inverse -/

/-- The parameter `ι(z) = -z / (1 - a₁ z - a₃ w(z))` of the negative of the point with parameter
`z` on the curve `(z, w(z))`. -/
noncomputable def formalInverse : PowerSeries R :=
  -(PowerSeries.X * PowerSeries.invOfUnit (formalInverseDenom W) 1)

/-- The defining formula for `formalInverse`. -/
theorem formalInverse_def :
    formalInverse W = -(PowerSeries.X * PowerSeries.invOfUnit (formalInverseDenom W) 1) :=
  (rfl)

/-- The formal inverse vanishes at the origin: the negative of `O` is `O`. -/
@[simp]
theorem constantCoeff_formalInverse : PowerSeries.constantCoeff (formalInverse W) = 0 := by
  rw [formalInverse_def]
  simp

/-- The formal inverse may be substituted into a power series. -/
theorem hasSubst_formalInverse : PowerSeries.HasSubst (formalInverse W) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_formalInverse W)

/-! ### Substituting the formal inverse -/

/-- Composing the `w`-expansion with the formal inverse gives `-w / (1 - a₁ z - a₃ w)`, the
`w`-coordinate of the negative point.

Both sides solve the `w`-equation at the parameter `ι` and have vanishing constant coefficient,
so they agree by `eq_subst_formalW_of_wEquation`. Clearing the denominator `u ^ 3`, the identity
to check is `-w u ^ 2 = -z ^ 3 + a₁ z w u - a₂ z ^ 2 w + a₃ w ^ 2 u - a₄ z w ^ 2 - a₆ w ^ 3`,
which is the `w`-equation itself after `a₁ z w + a₃ w ^ 2 = w (1 - u)`. -/
theorem subst_formalInverse_formalW :
    PowerSeries.subst (formalInverse W) (formalW W) =
      -(formalW W * PowerSeries.invOfUnit (formalInverseDenom W) 1) := by
  have hu := mul_invOfUnit_formalInverseDenom W
  have hw := formalW_wEquation W
  refine (eq_subst_formalW_of_wEquation W (constantCoeff_formalInverse W) ?_ ?_).symm
  · simp
  · refine ((isUnit_formalInverseDenom W).pow 3).mul_left_cancel ?_
    rw [wEquationRHS_powerSeries, formalInverse_def, formalInverseDenom_def] at *
    grind

/-- Composing the denominator with the formal inverse inverts it. -/
theorem subst_formalInverse_formalInverseDenom :
    PowerSeries.subst (formalInverse W) (formalInverseDenom W) =
      PowerSeries.invOfUnit (formalInverseDenom W) 1 := by
  have hu := mul_invOfUnit_formalInverseDenom W
  refine (isUnit_formalInverseDenom W).mul_left_cancel ?_
  rw [mul_invOfUnit_formalInverseDenom W, formalInverseDenom_def,
    ← PowerSeries.coe_substAlgHom (hasSubst_formalInverse W)]
  -- `subst_C` lands on `MvPowerSeries.C`; `C_apply` is what identifies it with `PowerSeries.C`,
  -- without which the two spellings of the same map are opaque to `grind`.
  simp only [map_sub, map_mul, map_one, PowerSeries.coe_substAlgHom,
    PowerSeries.substAlgHom_X, PowerSeries.subst_C, ← PowerSeries.C_apply,
    subst_formalInverse_formalW W]
  rw [formalInverse_def, formalInverseDenom_def] at *
  grind

/-- **The formal inverse is an involution**: `ι(ι(z)) = z`.

This is the formal-series form of `-(-P) = P` for the group law near the origin. -/
theorem subst_formalInverse_self :
    PowerSeries.subst (formalInverse W) (formalInverse W) = PowerSeries.X := by
  have hu := mul_invOfUnit_formalInverseDenom W
  have hinv := PowerSeries.map_invOfUnit
    (PowerSeries.substAlgHom (hasSubst_formalInverse W)) (D := formalInverseDenom W)
    (u := 1) (v := 1) (constantCoeff_formalInverseDenom W)
    (by rw [PowerSeries.coe_substAlgHom, subst_formalInverse_formalInverseDenom W]
        exact PowerSeries.constantCoeff_invOfUnit _ _)
  rw [PowerSeries.coe_substAlgHom] at hinv
  have hdouble : PowerSeries.invOfUnit (PowerSeries.invOfUnit (formalInverseDenom W) 1) 1 =
      formalInverseDenom W := by
    exact (left_inv_eq_right_inv hu
      (PowerSeries.mul_invOfUnit _ 1 (by simp))).symm
  have hexp : PowerSeries.subst (formalInverse W) (formalInverse W) =
      -(formalInverse W * PowerSeries.subst (formalInverse W)
        (PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
    have h : PowerSeries.subst (formalInverse W) (formalInverse W) =
        PowerSeries.subst (formalInverse W)
          (-(PowerSeries.X * PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
      rw [← formalInverse_def]
    rw [h, ← PowerSeries.coe_substAlgHom (hasSubst_formalInverse W), map_neg, map_mul,
      PowerSeries.substAlgHom_X (hasSubst_formalInverse W)]
  rw [hexp, hinv, subst_formalInverse_formalInverseDenom W, hdouble, formalInverse_def]
  linear_combination (PowerSeries.X : PowerSeries R) * hu

/-! ### Base change -/

section BaseChange

variable {S : Type*} [CommRing S] (φ : R →+* S)

/-- The denominator of the formal inverse commutes with base change. -/
@[simp]
theorem map_formalInverseDenom :
    formalInverseDenom (W.map φ) = PowerSeries.map φ (formalInverseDenom W) := by
  simp only [formalInverseDenom_def, map_sub, map_one, map_mul, PowerSeries.map_C,
    PowerSeries.map_X, map_formalW W φ, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

/-- **The formal inverse commutes with base change.** -/
@[simp]
theorem map_formalInverse :
    formalInverse (W.map φ) = PowerSeries.map φ (formalInverse W) := by
  have hinv := PowerSeries.map_invOfUnit (PowerSeries.map φ) (D := formalInverseDenom W)
    (u := 1) (v := 1) (constantCoeff_formalInverseDenom W)
    (by rw [show (PowerSeries.map φ (formalInverseDenom W) : PowerSeries S) =
          formalInverseDenom (W.map φ) from (map_formalInverseDenom W φ).symm]
        exact constantCoeff_formalInverseDenom (W.map φ))
  rw [formalInverse_def, formalInverse_def, map_neg, map_mul, PowerSeries.map_X, hinv,
    map_formalInverseDenom W φ]

end BaseChange

/-! ### The formal inverse at a parameter -/

/-- Over a nontrivial commutative ring, the formal inverse `ι(z) = -z + ⋯` is nonzero. -/
@[simp]
theorem formalInverse_ne_zero [Nontrivial R] : formalInverse W ≠ 0 := by
  intro h
  have h1 := congrArg (PowerSeries.coeff 1) h
  rw [formalInverse_def, map_neg, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit,
    map_zero] at h1
  simp only [inv_one, Units.val_one] at h1
  exact one_ne_zero (neg_eq_zero.mp h1)

/-- Over a domain of multivariate series, the formal inverse at a nonzero parameter with vanishing
constant coefficient is itself nonzero. -/
theorem subst_formalInverse_ne_zero {σ : Type*} [IsDomain (MvPowerSeries σ R)]
    {q : MvPowerSeries σ R} (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    PowerSeries.subst q (formalInverse W) ≠ 0 := by
  have : Nontrivial R := RingHom.domain_nontrivial (MvPowerSeries.C : R →+* MvPowerSeries σ R)
  have : NoZeroDivisors R :=
    (MvPowerSeries.C_injective (σ := σ)).noZeroDivisors MvPowerSeries.C (map_zero _) (map_mul _)
  exact (PowerSeries.subst_eq_zero_iff hq hq0).not.mpr (formalInverse_ne_zero W)

/-- The denominator of the formal inverse, read at a parameter, still multiplies its `invOfUnit`
to `1`: substituting is a ring map, so it carries `mul_invOfUnit_formalInverseDenom` along. -/
theorem subst_formalInverseDenom_mul {σ : Type*} {q : MvPowerSeries σ R}
    (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst q (formalInverseDenom W) *
        PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1) = 1 := by
  have h := congrArg (PowerSeries.substAlgHom hq) (mul_invOfUnit_formalInverseDenom W)
  simp only [map_mul, map_one] at h
  simpa only [PowerSeries.coe_substAlgHom hq] using h

/-- The formal inverse read at a parameter: `ι(q) = -(q * u(q)⁻¹)`. -/
theorem subst_formalInverse_eq {σ : Type*} {q : MvPowerSeries σ R}
    (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst q (formalInverse W) =
      -(q * PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
  rw [formalInverse_def, ← PowerSeries.coe_substAlgHom hq]
  simp only [map_neg, map_mul]
  rw [PowerSeries.coe_substAlgHom hq, PowerSeries.subst_X hq]

/-- The denominator of the formal inverse read at a parameter, written out. -/
theorem subst_formalInverseDenom_eq {σ : Type*} {q : MvPowerSeries σ R}
    (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst q (formalInverseDenom W) =
      1 - MvPowerSeries.C W.a₁ * q - MvPowerSeries.C W.a₃ * PowerSeries.subst q (formalW W) := by
  rw [formalInverseDenom_def, ← PowerSeries.coe_substAlgHom hq]
  simp only [map_sub, map_one, map_mul, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_C]

/-- The denominator of the formal inverse read at a parameter, pushed into any commutative
`MvPowerSeries σ R`-algebra `T`, where `W` is base-changed along the composite map
`R → MvPowerSeries σ R → T`. -/
theorem algebraMap_subst_formalInverseDenom_eq {σ T : Type*} [CommRing T]
    [Algebra (MvPowerSeries σ R) T] {q : MvPowerSeries σ R} (hq : PowerSeries.HasSubst q) :
    algebraMap (MvPowerSeries σ R) T (PowerSeries.subst q (formalInverseDenom W)) =
      1 - (W.map ((algebraMap (MvPowerSeries σ R) T).comp
            (algebraMap R (MvPowerSeries σ R)))).a₁ * algebraMap (MvPowerSeries σ R) T q -
        (W.map ((algebraMap (MvPowerSeries σ R) T).comp
            (algebraMap R (MvPowerSeries σ R)))).a₃ *
          algebraMap (MvPowerSeries σ R) T (PowerSeries.subst q (formalW W)) := by
  rw [W.subst_formalInverseDenom_eq hq, map_sub, map_sub, map_one, map_mul, map_mul,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, RingHom.comp_apply, RingHom.comp_apply,
    MvPowerSeries.c_eq_algebraMap]

/-- The `w`-expansion at the inverted parameter: `w(ι(q)) = -(w(q) * u(q)⁻¹)`.

This is the one-variable `subst_formalInverse_formalW` carried through the substitution `q`. -/
theorem subst_formalW_subst_formalInverse {σ : Type*} {q : MvPowerSeries σ R}
    (hq : PowerSeries.HasSubst q) :
    PowerSeries.subst (PowerSeries.subst q (formalInverse W)) (formalW W) =
      -(PowerSeries.subst q (formalW W) *
        PowerSeries.subst q (PowerSeries.invOfUnit (formalInverseDenom W) 1)) := by
  rw [← PowerSeries.subst_comp_subst_apply (hasSubst_formalInverse W) hq,
    subst_formalInverse_formalW, ← PowerSeries.coe_substAlgHom hq]
  simp only [map_neg, map_mul]

/-- The formal inverse at a parameter, read through a further substitution `g` that kills that
parameter: the result vanishes, since the inverse has no constant term. -/
theorem subst_subst_formalInverse_eq_zero {σ' : Type*}
    {g : σ' → MvPowerSeries Unit R} (hg : MvPowerSeries.HasSubst g) {a : MvPowerSeries σ' R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hga : MvPowerSeries.subst g a = 0) :
    MvPowerSeries.subst g (MvPowerSeries.subst (fun _ : Unit ↦ a) (formalInverse W)) = 0 := by
  rw [MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ ↦ ha) hg,
    show (fun _ : Unit ↦ MvPowerSeries.subst g a) = (0 : Unit → MvPowerSeries Unit R) from
      funext fun _ ↦ hga]
  exact MvPowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_formalInverse W)

end WeierstrassCurve
