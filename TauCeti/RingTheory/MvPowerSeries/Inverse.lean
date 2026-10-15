/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Monoid homomorphisms and `invOfUnit`

`MvPowerSeries.invOfUnit D u` inverts a power series whose constant coefficient is the unit `u`.
Monoid homomorphisms between power series rings preserve this inverse, provided the constant
coefficient of the image is also a specified unit. The inverse of `1 - Xᵢ` is the geometric series
`∑ₙ Xᵢⁿ`, and the coefficients of its powers `Xᵢⁿ` are all `1`.

## Main results

* `MvPowerSeries.map_invOfUnit`: for a monoid homomorphism `φ` between multivariate power
  series rings, `φ (invOfUnit D u) = invOfUnit (φ D) v`, given `constantCoeff D = u` and
  `constantCoeff (φ D) = v`.
* `PowerSeries.map_invOfUnit`: the same statement in one variable.
* `MvPowerSeries.coeff_single_eq_one_of_one_sub_X_mul_eq_one`: a right inverse of `1 - Xᵢ` has
  coefficient `1` at every power `Xᵢⁿ`.

## Implementation notes

Only multiplication and `1` are needed, so the results use `MonoidHomClass`. They apply to
coefficient maps, variable renamings, and substitution algebra homomorphisms. The source and
target variable types and coefficient rings may differ; neither coefficient ring needs to be
commutative. The two units independently certify the source and image constant coefficients:
no compatibility between the homomorphism and `constantCoeff` is assumed.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project (Apache-2.0),
[`EllipticCurves/WeierstrassFormalGroup/Chord.lean`](https://github.com/MichaelStollBayreuth/EllipticCurves/blob/66889eada51a/EllipticCurves/WeierstrassFormalGroup/Chord.lean),
the private `ringHom_invOfUnit` and its specialisation `rename_swap_invOfUnit`. The source fixes
the constant coefficients to `1` and works over a commutative ring; here the units are arbitrary
and the coefficient rings need not be commutative.
-/

public section

variable {σ τ R S : Type*} [Ring R] [Ring S]

namespace MvPowerSeries

/-- A monoid homomorphism between multivariate power series rings carries `invOfUnit` to the
`invOfUnit` of the image. -/
theorem map_invOfUnit {F : Type*} [FunLike F (MvPowerSeries σ R) (MvPowerSeries τ S)]
    [MonoidHomClass F (MvPowerSeries σ R) (MvPowerSeries τ S)] (φ : F) {D : MvPowerSeries σ R}
    {u : Rˣ} {v : Sˣ} (hD : constantCoeff D = u) (hD' : constantCoeff (φ D) = v) :
    φ (invOfUnit D u) = invOfUnit (φ D) v :=
  left_inv_eq_right_inv
    (map_mul_eq_one φ (invOfUnit_mul D u hD))
    (mul_invOfUnit (φ D) v hD')

/-- **A right inverse of `1 - Xᵢ` has coefficient `1` at every power `Xᵢⁿ`**: it is the geometric
series `∑ₙ Xᵢⁿ`. -/
theorem coeff_single_eq_one_of_one_sub_X_mul_eq_one {g : MvPowerSeries σ R} {i : σ}
    (hg : (1 - X i) * g = 1) (n : ℕ) : coeff (Finsupp.single i n) g = 1 := by
  classical
  have hg' : g = 1 + X i * g := by
    rwa [sub_mul, one_mul, sub_eq_iff_eq_add] at hg
  induction n with
  | zero => rw [hg']; simp
  | succ n ih =>
    have hX : coeff (Finsupp.single i (n + 1)) (X i * g) = coeff (Finsupp.single i n) g := by
      rw [X_def, show Finsupp.single i (n + 1) = Finsupp.single i 1 + Finsupp.single i n by
          rw [← Finsupp.single_add, add_comm],
        coeff_add_monomial_mul, one_mul]
    conv_lhs => rw [hg']
    rw [map_add, hX, ih]
    simp [coeff_one]

end MvPowerSeries

namespace PowerSeries

/-- The one-variable form of `MvPowerSeries.map_invOfUnit`, expressed with
`PowerSeries.invOfUnit` and `PowerSeries.constantCoeff`. -/
theorem map_invOfUnit {F : Type*} [FunLike F (PowerSeries R) (PowerSeries S)]
    [MonoidHomClass F (PowerSeries R) (PowerSeries S)] (φ : F) {D : PowerSeries R}
    {u : Rˣ} {v : Sˣ} (hD : constantCoeff D = u) (hD' : constantCoeff (φ D) = v) :
    φ (invOfUnit D u) = invOfUnit (φ D) v :=
  MvPowerSeries.map_invOfUnit φ hD hD'

end PowerSeries
