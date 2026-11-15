/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fin.Rev

import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# Exchange polynomials

In polynomial and generalized cluster mutation, each mutable direction `k` carries a univariate
*exchange polynomial* `H(T) = ∑_{l=0}^r h_l T^l` of specified positive degree `r > 0` whose
constant coefficient `h_0` and leading coefficient `h_r` are units. Under mutation in direction `k`,
the polynomial at `k` is reversed to `T^r H(T⁻¹)`, while every other polynomial is dilated by a
unit `κ = h_r^{[b]₊} h_0^{-[-b]₊}` determined by the endpoint coefficients of `H` and the divided
exchange matrix entry `b`, and then rescaled by a normalizer unit.

Because reversal, dilation, and unit scaling use only products, zero, and one, exchange polynomials
live naturally over any commutative monoid with zero `𝕂`. Recording the positive degree explicitly
also keeps all operations well-behaved over trivial targets.

## Main definitions

* `TauCeti.ExchangePolynomial 𝕂`: an exchange polynomial of specified positive degree over a
  commutative monoid with zero `𝕂`, with unit constant and leading coefficients.
* `TauCeti.ExchangePolynomial.unitZero`, `TauCeti.ExchangePolynomial.unitLast`: the constant and
  leading coefficients as units of `𝕂`.
* `TauCeti.ExchangePolynomial.reverse`: the reversed polynomial `T^r H(T⁻¹)`.
* `TauCeti.ExchangePolynomial.dilate`: the dilated polynomial `H(κ T)` for `κ : 𝕂ˣ`.
* `TauCeti.ExchangePolynomial.scale`: the unit multiple `e H` for `e : 𝕂ˣ`.
* `TauCeti.ExchangePolynomial.dilationFactor`: the propagation factor `h_r^{b⁺} h_0^{-b⁻}` in `𝕂ˣ`.
* `TauCeti.ExchangePolynomial.HasUnitOneEndpoints`: the predicate `h_0 = 1 ∧ h_r = 1`.
* `TauCeti.ExchangePolynomial.binary`: the binomial exchange polynomial `1 + T`.
* `TauCeti.ExchangePolynomial.map`: coefficientwise pushforward along a `MonoidWithZeroHomClass`
  map.
* `TauCeti.ExchangePolynomial.evalHomogeneous`: homogeneous evaluation of `H` at `(x, y)`.

## Main results

* `TauCeti.ExchangePolynomial.scale_injective`: scaling a fixed exchange polynomial by units of `𝕂`
  is injective.
* `TauCeti.ExchangePolynomial.reverse_dilate`: reversing a dilated polynomial dilates the reversal
  by `κ⁻¹` and scales by `κ ^ r`.
* `TauCeti.ExchangePolynomial.dilationFactor_reverse`,
  `TauCeti.ExchangePolynomial.dilationFactor_reverse_neg`: the dilation factor of `H.reverse` at
  `-b` is the inverse of the dilation factor of `H` at `b`.
* `TauCeti.ExchangePolynomial.dilationFactor_scale`: scaling `H` by `e` multiplies its dilation
  factor at `b` by `e ^ b`.

## References

* L. Chekhov and M. Shapiro, *Teichmüller spaces of Riemann surfaces with orbifold points of
  arbitrary order and cluster variables*, Int. Math. Res. Not. 2014 (2014), §2.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277 (2015),
  §2.
* L. Bai, X. Chen, M. Ding and F. Xu, *Generalized quantum cluster algebras: the Laurent phenomenon
  and upper bounds*, J. Algebra 619 (2023), §2.
-/

public section

namespace TauCeti

/-- An *exchange polynomial* of specified positive degree over a commutative monoid with zero `𝕂`,
with unit constant and leading coefficients.

Reversal, dilation, and unit scaling use only the multiplicative structure of `𝕂`. Carrying
`degree` explicitly avoids degeneracy when `𝕂` is trivial. -/
structure ExchangePolynomial (𝕂 : Type*) [CommMonoidWithZero 𝕂] where
  /-- The specified positive degree `r` of the exchange polynomial. -/
  degree : ℕ
  /-- The exchange degree is positive. -/
  degree_pos : 0 < degree
  /-- The coefficients `h_0, …, h_r`, indexed by `Fin (degree + 1)`. -/
  coeff : Fin (degree + 1) → 𝕂
  /-- The constant coefficient `h_0` is a unit of `𝕂`. -/
  isUnit_coeff_zero : IsUnit (coeff 0)
  /-- The leading coefficient `h_r` is a unit of `𝕂`. -/
  isUnit_coeff_last : IsUnit (coeff (Fin.last degree))

namespace ExchangePolynomial

variable {𝕂 𝕂' 𝕂'' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  [CommMonoidWithZero 𝕂'']

/-- Two exchange polynomials are equal when they have the same degree and matching coefficients. -/
@[ext (iff := false)]
theorem ext {H₁ H₂ : ExchangePolynomial 𝕂} (hdeg : H₁.degree = H₂.degree)
    (hcoeff : ∀ l : Fin (H₁.degree + 1),
      H₁.coeff l = H₂.coeff (l.cast (congrArg (· + 1) hdeg))) : H₁ = H₂ := by
  obtain ⟨d₁, hd₁, c₁, h0₁, hl₁⟩ := H₁
  obtain ⟨d₂, hd₂, c₂, h0₂, hl₂⟩ := H₂
  dsimp only at hdeg hcoeff
  subst hdeg
  congr
  funext l
  exact hcoeff l

/-- Characterize equality of exchange polynomials by degree equality and coefficient agreement. -/
theorem ext_iff {H₁ H₂ : ExchangePolynomial 𝕂} :
    H₁ = H₂ ↔ ∃ hdeg : H₁.degree = H₂.degree,
      ∀ l : Fin (H₁.degree + 1), H₁.coeff l = H₂.coeff (l.cast (congrArg (· + 1) hdeg)) := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ ↦ rfl⟩
  · rintro ⟨hdeg, hcoeff⟩
    exact ext hdeg hcoeff

/-- The specified degree of an exchange polynomial is nonzero. -/
theorem degree_ne_zero (H : ExchangePolynomial 𝕂) : H.degree ≠ 0 :=
  H.degree_pos.ne'

/-! ### Endpoint units -/

/-- The constant coefficient `h_0` of an exchange polynomial, as a unit of `𝕂`. -/
noncomputable def unitZero (H : ExchangePolynomial 𝕂) : 𝕂ˣ :=
  H.isUnit_coeff_zero.unit

/-- The leading coefficient `h_r` of an exchange polynomial, as a unit of `𝕂`. -/
noncomputable def unitLast (H : ExchangePolynomial 𝕂) : 𝕂ˣ :=
  H.isUnit_coeff_last.unit

@[simp]
theorem val_unitZero (H : ExchangePolynomial 𝕂) : (H.unitZero : 𝕂) = H.coeff 0 :=
  H.isUnit_coeff_zero.unit_spec

@[simp]
theorem val_unitLast (H : ExchangePolynomial 𝕂) :
    (H.unitLast : 𝕂) = H.coeff (Fin.last H.degree) :=
  H.isUnit_coeff_last.unit_spec

/-! ### Reversal, dilation, and unit scaling -/

/-- The reversed exchange polynomial `T^r H(T⁻¹)`, reversing the order of the coefficients. -/
def reverse (H : ExchangePolynomial 𝕂) : ExchangePolynomial 𝕂 where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := H.coeff l.rev
  isUnit_coeff_zero := by simpa using H.isUnit_coeff_last
  isUnit_coeff_last := by simpa using H.isUnit_coeff_zero

@[simp]
theorem reverse_degree (H : ExchangePolynomial 𝕂) : H.reverse.degree = H.degree :=
  (rfl)

@[simp]
theorem reverse_coeff (H : ExchangePolynomial 𝕂) (l : Fin (H.reverse.degree + 1)) :
    H.reverse.coeff l = H.coeff (l.cast (congrArg (· + 1) H.reverse_degree)).rev :=
  (rfl)

/-- Reversing an exchange polynomial twice recovers the original polynomial. -/
@[simp]
theorem reverse_reverse (H : ExchangePolynomial 𝕂) : H.reverse.reverse = H := by
  refine ext (by simp) fun l ↦ ?_
  simp [Fin.cast_rev]

/-- Reversal of exchange polynomials is an involution. -/
theorem reverse_involutive : Function.Involutive (reverse (𝕂 := 𝕂)) :=
  reverse_reverse

@[simp]
theorem unitZero_reverse (H : ExchangePolynomial 𝕂) : H.reverse.unitZero = H.unitLast := by
  ext
  simp

@[simp]
theorem unitLast_reverse (H : ExchangePolynomial 𝕂) : H.reverse.unitLast = H.unitZero := by
  ext
  simp

/-- The dilated exchange polynomial `H(κ T)` for a unit `κ : 𝕂ˣ`, multiplying the `l`-th
coefficient by `κ ^ l`. -/
def dilate (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) : ExchangePolynomial 𝕂 where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := H.coeff l * ((κ ^ (l : ℕ) : 𝕂ˣ) : 𝕂)
  isUnit_coeff_zero := H.isUnit_coeff_zero.mul (Units.isUnit _)
  isUnit_coeff_last := H.isUnit_coeff_last.mul (Units.isUnit _)

@[simp]
theorem dilate_degree (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) : (H.dilate κ).degree = H.degree :=
  (rfl)

@[simp]
theorem dilate_coeff (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) (l : Fin ((H.dilate κ).degree + 1)) :
    (H.dilate κ).coeff l =
      H.coeff (l.cast (congrArg (· + 1) (H.dilate_degree κ))) * (κ : 𝕂) ^ (l : ℕ) := by
  exact congrArg (H.coeff l * ·) (Units.val_pow_eq_pow_val κ l)

@[simp]
theorem dilate_one (H : ExchangePolynomial 𝕂) : H.dilate 1 = H := by
  refine ext (by simp) fun l ↦ ?_
  simp

/-- Successive dilations multiply their dilation units. -/
theorem dilate_dilate (H : ExchangePolynomial 𝕂) (κ₁ κ₂ : 𝕂ˣ) :
    (H.dilate κ₁).dilate κ₂ = H.dilate (κ₁ * κ₂) := by
  refine ext (by simp) fun l ↦ ?_
  simp [mul_pow, mul_assoc]

@[simp]
theorem dilate_mul_inv_cancel (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ).dilate κ⁻¹ = H := by
  rw [dilate_dilate, mul_inv_cancel, dilate_one]

@[simp]
theorem dilate_inv_mul_cancel (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ⁻¹).dilate κ = H := by
  rw [dilate_dilate, inv_mul_cancel, dilate_one]

@[simp]
theorem unitZero_dilate (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ).unitZero = H.unitZero := by
  ext
  simp

@[simp]
theorem unitLast_dilate (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ).unitLast = H.unitLast * κ ^ H.degree := by
  ext
  simp

/-- Scale every coefficient of an exchange polynomial by a unit `e : 𝕂ˣ`. -/
def scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) : ExchangePolynomial 𝕂 where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := (e : 𝕂) * H.coeff l
  isUnit_coeff_zero := (Units.isUnit e).mul H.isUnit_coeff_zero
  isUnit_coeff_last := (Units.isUnit e).mul H.isUnit_coeff_last

@[simp]
theorem scale_degree (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) : (H.scale e).degree = H.degree :=
  (rfl)

@[simp]
theorem scale_coeff (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) (l : Fin ((H.scale e).degree + 1)) :
    (H.scale e).coeff l =
      (e : 𝕂) * H.coeff (l.cast (congrArg (· + 1) (H.scale_degree e))) :=
  (rfl)

@[simp]
theorem scale_one (H : ExchangePolynomial 𝕂) : H.scale 1 = H := by
  refine ext (by simp) fun l ↦ ?_
  simp

/-- Successive unit scalings multiply the scaling units. -/
theorem scale_scale (H : ExchangePolynomial 𝕂) (e₁ e₂ : 𝕂ˣ) :
    (H.scale e₁).scale e₂ = H.scale (e₁ * e₂) := by
  refine ext (by simp) fun l ↦ ?_
  simp [mul_assoc, mul_left_comm]

@[simp]
theorem scale_mul_inv_cancel (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e).scale e⁻¹ = H := by
  rw [scale_scale, mul_inv_cancel, scale_one]

@[simp]
theorem scale_inv_mul_cancel (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e⁻¹).scale e = H := by
  rw [scale_scale, inv_mul_cancel, scale_one]

@[simp]
theorem unitZero_scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e).unitZero = e * H.unitZero := by
  ext
  simp

@[simp]
theorem unitLast_scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e).unitLast = e * H.unitLast := by
  ext
  simp

/-- Scaling a fixed exchange polynomial by units of `𝕂` is injective, because its constant
coefficient is a unit. -/
theorem scale_injective (H : ExchangePolynomial 𝕂) : Function.Injective H.scale := by
  intro e₁ e₂ h
  have h0 : (H.scale e₁).unitZero = (H.scale e₂).unitZero := congrArg unitZero h
  simpa only [unitZero_scale, mul_left_inj] using h0

@[simp]
theorem scale_inj {H : ExchangePolynomial 𝕂} {e₁ e₂ : 𝕂ˣ} :
    H.scale e₁ = H.scale e₂ ↔ e₁ = e₂ :=
  H.scale_injective.eq_iff

@[simp]
theorem scale_eq_self {H : ExchangePolynomial 𝕂} {e : 𝕂ˣ} : H.scale e = H ↔ e = 1 := by
  conv_rhs => rw [← H.scale_inj]
  rw [scale_one]

@[simp]
theorem reverse_scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e).reverse = H.reverse.scale e := by
  refine ext (by simp) fun l ↦ ?_
  simp [Fin.cast_rev]

@[simp]
theorem dilate_scale (H : ExchangePolynomial 𝕂) (e κ : 𝕂ˣ) :
    (H.scale e).dilate κ = (H.dilate κ).scale e := by
  refine ext (by simp) fun l ↦ ?_
  simp [mul_assoc]

/-- Reversing a dilated polynomial dilates the reversed polynomial by `κ⁻¹` and scales by
`κ ^ H.degree`. -/
theorem reverse_dilate (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ).reverse = (H.reverse.dilate κ⁻¹).scale (κ ^ H.degree) := by
  refine ext (by simp) fun l ↦ ?_
  have hl : (H.degree - (l : ℕ)) + (l : ℕ) = H.degree := by
    have hlt : (l : ℕ) < H.degree + 1 := l.isLt.trans_eq (by simp)
    omega
  have hpow : κ ^ H.degree * (κ⁻¹) ^ (l : ℕ) = κ ^ (H.degree - (l : ℕ)) := by
    calc
      κ ^ H.degree * (κ⁻¹) ^ (l : ℕ)
          = κ ^ ((H.degree - (l : ℕ)) + (l : ℕ)) * (κ⁻¹) ^ (l : ℕ) :=
            congrArg (fun n ↦ κ ^ n * (κ⁻¹) ^ (l : ℕ)) hl.symm
      _ = κ ^ (H.degree - (l : ℕ)) * (κ ^ (l : ℕ) * (κ⁻¹) ^ (l : ℕ)) := by
            rw [pow_add, mul_assoc]
      _ = κ ^ (H.degree - (l : ℕ)) := by simp
  have hval : ((κ ^ H.degree : 𝕂ˣ) : 𝕂) * ((κ⁻¹ : 𝕂ˣ) : 𝕂) ^ (l : ℕ) =
      (κ : 𝕂) ^ (H.degree - (l : ℕ)) := by
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using congrArg Units.val hpow
  simp only [reverse_coeff, dilate_coeff, scale_coeff, Fin.cast_rev, Fin.val_cast, Fin.val_rev,
    dilate_degree, Nat.succ_sub_succ_eq_sub]
  calc
    H.coeff (l.cast (by simp)).rev * (κ : 𝕂) ^ (H.degree - (l : ℕ))
        = H.coeff (l.cast (by simp)).rev *
            (((κ ^ H.degree : 𝕂ˣ) : 𝕂) * ((κ⁻¹ : 𝕂ˣ) : 𝕂) ^ (l : ℕ)) := by
          rw [hval]
    _ = ((κ ^ H.degree : 𝕂ˣ) : 𝕂) *
          (H.coeff (l.cast (by simp)).rev * ((κ⁻¹ : 𝕂ˣ) : 𝕂) ^ (l : ℕ)) := by
          rw [mul_left_comm]

/-! ### Propagation dilation factors -/

/-- The unit `h_r^{b⁺} h_0^{-b⁻}` by which mutation in the direction of `H` dilates an exchange
polynomial whose divided exchange matrix entry is `b`. -/
noncomputable def dilationFactor (H : ExchangePolynomial 𝕂) (b : ℤ) : 𝕂ˣ :=
  H.unitLast ^ b⁺ * H.unitZero ^ (-b⁻)

/-- Restatement of `dilationFactor` in terms of `unitLast` and `unitZero`. -/
theorem dilationFactor_def (H : ExchangePolynomial 𝕂) (b : ℤ) :
    H.dilationFactor b = H.unitLast ^ b⁺ * H.unitZero ^ (-b⁻) :=
  (rfl)

/-- Restatement of `dilationFactor` using `max b 0` and `-max (-b) 0`. -/
theorem dilationFactor_eq_max (H : ExchangePolynomial 𝕂) (b : ℤ) :
    H.dilationFactor b =
      H.isUnit_coeff_last.unit ^ max b 0 * H.isUnit_coeff_zero.unit ^ (-max (-b) 0) := by
  rw [dilationFactor_def, posPart_def, negPart_def]
  rfl

@[simp]
theorem dilationFactor_zero (H : ExchangePolynomial 𝕂) : H.dilationFactor 0 = 1 := by
  simp [dilationFactor_def]

/-- For a nonnegative entry `b`, the dilation factor is `h_r ^ b`. -/
theorem dilationFactor_of_nonneg (H : ExchangePolynomial 𝕂) {b : ℤ} (hb : 0 ≤ b) :
    H.dilationFactor b = H.unitLast ^ b := by
  simp [dilationFactor_def, posPart_eq_self.mpr hb, negPart_eq_zero.mpr hb]

/-- For a nonpositive entry `b`, the dilation factor is `h_0 ^ b`. -/
theorem dilationFactor_of_nonpos (H : ExchangePolynomial 𝕂) {b : ℤ} (hb : b ≤ 0) :
    H.dilationFactor b = H.unitZero ^ b := by
  simp [dilationFactor_def, posPart_eq_zero.mpr hb, negPart_eq_neg.mpr hb]

/-- Reversing `H` and negating the matrix entry inverts the propagation dilation factor. -/
@[simp]
theorem dilationFactor_reverse (H : ExchangePolynomial 𝕂) (b : ℤ) :
    H.reverse.dilationFactor b = (H.dilationFactor (-b))⁻¹ := by
  simp [dilationFactor_def, mul_inv_rev, zpow_neg]

/-- Evaluating the dilation factor of `H.reverse` at `-b` gives `(H.dilationFactor b)⁻¹`. -/
theorem dilationFactor_reverse_neg (H : ExchangePolynomial 𝕂) (b : ℤ) :
    H.reverse.dilationFactor (-b) = (H.dilationFactor b)⁻¹ := by
  simp

/-- Scaling `H` by a unit `e` multiplies its dilation factor at `b` by `e ^ b`. -/
theorem dilationFactor_scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) (b : ℤ) :
    (H.scale e).dilationFactor b = e ^ b * H.dilationFactor b := by
  rw [dilationFactor_def, dilationFactor_def, unitLast_scale, unitZero_scale, mul_zpow, mul_zpow]
  calc
    e ^ b⁺ * H.unitLast ^ b⁺ * (e ^ (-b⁻) * H.unitZero ^ (-b⁻))
        = (e ^ b⁺ * e ^ (-b⁻)) * (H.unitLast ^ b⁺ * H.unitZero ^ (-b⁻)) := by
          simp only [mul_assoc, mul_left_comm]
    _ = e ^ (b⁺ - b⁻) * (H.unitLast ^ b⁺ * H.unitZero ^ (-b⁻)) := by
          rw [← zpow_add, sub_eq_add_neg]
    _ = e ^ b * (H.unitLast ^ b⁺ * H.unitZero ^ (-b⁻)) := by rw [posPart_sub_negPart]

/-! ### Endpoint-one and binary exchange polynomials -/

/-- An exchange polynomial has *endpoint coefficients one* when `h_0 = 1` and `h_r = 1`. -/
@[mk_iff]
structure HasUnitOneEndpoints (H : ExchangePolynomial 𝕂) : Prop where
  /-- The constant coefficient equals `1`. -/
  coeff_zero : H.coeff 0 = 1
  /-- The leading coefficient equals `1`. -/
  coeff_last : H.coeff (Fin.last H.degree) = 1

namespace HasUnitOneEndpoints

theorem unitZero_eq_one {H : ExchangePolynomial 𝕂} (h : H.HasUnitOneEndpoints) :
    H.unitZero = 1 :=
  Units.ext (by simp [h.coeff_zero])

theorem unitLast_eq_one {H : ExchangePolynomial 𝕂} (h : H.HasUnitOneEndpoints) :
    H.unitLast = 1 :=
  Units.ext (by simp [h.coeff_last])

/-- An exchange polynomial with endpoint coefficients one produces trivial dilation factors. -/
theorem dilationFactor_eq_one {H : ExchangePolynomial 𝕂} (h : H.HasUnitOneEndpoints) (b : ℤ) :
    H.dilationFactor b = 1 := by
  simp [dilationFactor_def, h.unitZero_eq_one, h.unitLast_eq_one]

/-- Reversal preserves having endpoint coefficients equal to `1`. -/
protected theorem reverse {H : ExchangePolynomial 𝕂} (h : H.HasUnitOneEndpoints) :
    H.reverse.HasUnitOneEndpoints where
  coeff_zero := by simpa using h.coeff_last
  coeff_last := by simpa using h.coeff_zero

end HasUnitOneEndpoints

@[simp]
theorem hasUnitOneEndpoints_reverse {H : ExchangePolynomial 𝕂} :
    H.reverse.HasUnitOneEndpoints ↔ H.HasUnitOneEndpoints :=
  ⟨fun h ↦ H.reverse_reverse ▸ h.reverse, HasUnitOneEndpoints.reverse⟩

/-- The binary exchange polynomial `1 + T` of degree `1`. -/
def binary : ExchangePolynomial 𝕂 where
  degree := 1
  degree_pos := Nat.one_pos
  coeff _ := 1
  isUnit_coeff_zero := isUnit_one
  isUnit_coeff_last := isUnit_one

@[simp]
theorem binary_degree : (binary : ExchangePolynomial 𝕂).degree = 1 :=
  (rfl)

@[simp]
theorem binary_coeff (l : Fin ((binary : ExchangePolynomial 𝕂).degree + 1)) :
    (binary : ExchangePolynomial 𝕂).coeff l = 1 :=
  (rfl)

@[simp]
theorem unitZero_binary : (binary : ExchangePolynomial 𝕂).unitZero = 1 :=
  Units.ext (by simp)

@[simp]
theorem unitLast_binary : (binary : ExchangePolynomial 𝕂).unitLast = 1 :=
  Units.ext (by simp)

@[simp]
theorem reverse_binary : (binary : ExchangePolynomial 𝕂).reverse = binary := by
  refine ext (by simp) fun l ↦ ?_
  simp

@[simp]
theorem dilationFactor_binary (b : ℤ) : (binary : ExchangePolynomial 𝕂).dilationFactor b = 1 := by
  simp [dilationFactor_def]

/-- The binary polynomial `1 + T` has endpoint coefficients equal to `1`. -/
theorem hasUnitOneEndpoints_binary : (binary : ExchangePolynomial 𝕂).HasUnitOneEndpoints :=
  ⟨by simp, by simp⟩

/-! ### Functoriality along multiplicative maps -/

/-- Push an exchange polynomial forward coefficientwise along a map preserving `0`, `1`, and
multiplication. -/
def map {F : Type*} [FunLike F 𝕂 𝕂'] [MonoidWithZeroHomClass F 𝕂 𝕂'] (ψ : F)
    (H : ExchangePolynomial 𝕂) : ExchangePolynomial 𝕂' where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := ψ (H.coeff l)
  isUnit_coeff_zero := H.isUnit_coeff_zero.map ψ
  isUnit_coeff_last := H.isUnit_coeff_last.map ψ

section Map

variable {F : Type*} [FunLike F 𝕂 𝕂'] [MonoidWithZeroHomClass F 𝕂 𝕂'] (ψ : F)
  (H : ExchangePolynomial 𝕂)

@[simp]
theorem map_degree : (H.map ψ).degree = H.degree :=
  (rfl)

@[simp]
theorem map_coeff (l : Fin ((H.map ψ).degree + 1)) :
    (H.map ψ).coeff l = ψ (H.coeff (l.cast (congrArg (· + 1) (H.map_degree ψ)))) :=
  (rfl)

@[simp]
theorem map_id : H.map (MonoidWithZeroHom.id 𝕂) = H := by
  refine ext (by simp) fun l ↦ ?_
  simp

/-- Mapping twice composes the underlying coefficient maps. -/
theorem map_map {G : Type*} [FunLike G 𝕂' 𝕂''] [MonoidWithZeroHomClass G 𝕂' 𝕂''] (ψ' : G) :
    (H.map ψ).map ψ' = H.map ((MonoidWithZeroHom.ofClass ψ').comp
      (MonoidWithZeroHom.ofClass ψ)) := by
  refine ext (by simp) fun l ↦ ?_
  simp

@[simp]
theorem unitZero_map :
    (H.map ψ).unitZero = Units.map (MonoidHom.ofClass ψ) H.unitZero := by
  ext
  simp

@[simp]
theorem unitLast_map :
    (H.map ψ).unitLast = Units.map (MonoidHom.ofClass ψ) H.unitLast := by
  ext
  simp

@[simp]
theorem reverse_map : (H.map ψ).reverse = H.reverse.map ψ := by
  refine ext (by simp) fun l ↦ ?_
  simp [Fin.cast_rev]

@[simp]
theorem dilate_map (κ : 𝕂ˣ) :
    (H.dilate κ).map ψ = (H.map ψ).dilate (Units.map (MonoidHom.ofClass ψ) κ) := by
  refine ext (by simp) fun l ↦ ?_
  simp

@[simp]
theorem scale_map (e : 𝕂ˣ) :
    (H.scale e).map ψ = (H.map ψ).scale (Units.map (MonoidHom.ofClass ψ) e) := by
  refine ext (by simp) fun l ↦ ?_
  simp

@[simp]
theorem dilationFactor_map (b : ℤ) :
    (H.map ψ).dilationFactor b =
      Units.map (MonoidHom.ofClass ψ) (H.dilationFactor b) := by
  simp [dilationFactor_def]

@[simp]
theorem map_binary : (binary : ExchangePolynomial 𝕂).map ψ = binary := by
  refine ext (by simp) fun l ↦ ?_
  simp

protected theorem HasUnitOneEndpoints.map {H : ExchangePolynomial 𝕂}
    (h : H.HasUnitOneEndpoints) : (H.map ψ).HasUnitOneEndpoints where
  coeff_zero := by simp [h.coeff_zero]
  coeff_last := by simp [h.coeff_last]

end Map

/-! ### Sums over coefficients -/

section Sum

variable {M : Type*} [AddCommMonoid M]

/-- Summing a function of the coefficients of `H.reverse` equals summing over `H`. -/
theorem sum_reverse (H : ExchangePolynomial 𝕂) (f : 𝕂 → M) :
    ∑ l, f (H.reverse.coeff l) = ∑ l, f (H.coeff l) :=
  Equiv.sum_comp Fin.revPerm fun l ↦ f (H.coeff l)

/-- Summing a function of the coefficients of `H.scale e` reindexes cleanly to `H.degree + 1`. -/
theorem sum_scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) (f : 𝕂 → M) :
    ∑ l, f ((H.scale e).coeff l) = ∑ l, f ((e : 𝕂) * H.coeff l) :=
  (rfl)

/-- Summing a function of the coefficients of `H.map ψ` reindexes cleanly to `H.degree + 1`. -/
theorem sum_map {F : Type*} [FunLike F 𝕂 𝕂'] [MonoidWithZeroHomClass F 𝕂 𝕂'] (ψ : F)
    (H : ExchangePolynomial 𝕂) (f : 𝕂' → M) :
    ∑ l, f ((H.map ψ).coeff l) = ∑ l, f (ψ (H.coeff l)) :=
  (rfl)

/-- Summing a function over the coefficients of `binary` gives `f 1 + f 1`. -/
theorem sum_binary (f : 𝕂 → M) : ∑ l, f ((binary : ExchangePolynomial 𝕂).coeff l) = f 1 + f 1 :=
  Fin.sum_univ_two fun _ ↦ f 1

/-- Homogeneous bivariate evaluation `∑_{l = 0}^r f(h_l) • (x^l * y^{r - l})` of `H` at elements
`x, y : A` with scalar weights given by `f : 𝕂 → R`. -/
def evalHomogeneous {R A : Type*} [CommSemiring A] [SMul R A] (f : 𝕂 → R)
    (H : ExchangePolynomial 𝕂) (x y : A) : A :=
  ∑ l : Fin (H.degree + 1), f (H.coeff l) • (x ^ (l : ℕ) * y ^ (H.degree - (l : ℕ)))

theorem evalHomogeneous_def {R A : Type*} [CommSemiring A] [SMul R A] (f : 𝕂 → R)
    (H : ExchangePolynomial 𝕂) (x y : A) :
    H.evalHomogeneous f x y =
      ∑ l : Fin (H.degree + 1), f (H.coeff l) • (x ^ (l : ℕ) * y ^ (H.degree - (l : ℕ))) :=
  (rfl)

/-- Reversing `H` swaps the two arguments of homogeneous bivariate evaluation. -/
@[simp]
theorem evalHomogeneous_reverse {R A : Type*} [CommSemiring A] [SMul R A] (f : 𝕂 → R)
    (H : ExchangePolynomial 𝕂) (x y : A) :
    H.reverse.evalHomogeneous f x y = H.evalHomogeneous f y x := by
  simp only [evalHomogeneous, reverse]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have hl : (l : ℕ) ≤ H.degree := Nat.lt_succ_iff.mp l.isLt
  have hrev : (l.rev : ℕ) = H.degree - (l : ℕ) := by
    simp [Fin.val_rev, Nat.succ_sub_succ_eq_sub]
  have hsub : H.degree - (H.degree - (l : ℕ)) = (l : ℕ) := by omega
  simp only [Fin.revPerm_apply]
  rw [hrev, hsub, mul_comm]

@[simp]
theorem evalHomogeneous_map {R A : Type*} [CommSemiring A] [SMul R A]
    {F : Type*} [FunLike F 𝕂 𝕂'] [MonoidWithZeroHomClass F 𝕂 𝕂'] (ψ : F) (f : 𝕂' → R)
    (H : ExchangePolynomial 𝕂) (x y : A) :
    (H.map ψ).evalHomogeneous f x y = H.evalHomogeneous (f ∘ ψ) x y :=
  (rfl)

@[simp]
theorem evalHomogeneous_binary {R A : Type*} [CommSemiring A] [SMul R A] (f : 𝕂 → R) (x y : A) :
    (binary : ExchangePolynomial 𝕂).evalHomogeneous f x y = f 1 • y + f 1 • x :=
  (Fin.sum_univ_two fun l : Fin 2 ↦ f 1 • (x ^ (l : ℕ) * y ^ (1 - (l : ℕ)))).trans (by simp)

end Sum

/-! ### Checks -/

/-- For `H(T) = 1 + 2T` over `ℚ`, the dilation factor at `1` is `2`, at `-1` is `1`, and the
dilation factor of `H.reverse` at `-1` is `1 / 2`. -/
example :
    let H : ExchangePolynomial ℚ :=
      ⟨1, Nat.one_pos, fun l ↦ if l = 0 then 1 else 2, isUnit_one, by simp⟩
    (H.dilationFactor 1 : ℚ) = 2 ∧
      (H.dilationFactor (-1) : ℚ) = 1 ∧
      (H.reverse.dilationFactor (-1) : ℚ) = 1 / 2 := by
  intro H
  refine ⟨?_, ?_, ?_⟩
  · rw [H.dilationFactor_of_nonneg (by omega)]
    simp [H]
  · rw [H.dilationFactor_of_nonpos (by omega)]
    simp [H]
  · rw [H.dilationFactor_reverse_neg, H.dilationFactor_of_nonneg (by omega)]
    norm_num [H]

end ExchangePolynomial

end TauCeti
