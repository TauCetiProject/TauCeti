/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Order.Ring.Int

import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Exchange polynomials

An *exchange polynomial* over a commutative monoid with zero `𝕂` is a finite coefficient sequence
`h₀, …, hᵣ ∈ 𝕂` of specified positive degree `r > 0` whose endpoint coefficients `h₀` and `hᵣ` are
units, extended by zero above `r`. Recording the degree explicitly allows the same definition to
work uniformly over every commutative monoid with zero, including the zero semiring and the
zero-adjoined group of a coefficient semifield, while indexing coefficients by `ℕ` avoids
dependent-index casts across degree-preserving operations.

The multiplicative structure of `𝕂` alone supports all operations required by generalized cluster
exchange: reversal `Tʳ H(T⁻¹)`, dilation `H(κT)` by a unit `κ ∈ 𝕂ˣ`, scaling `e H` by a unit
`e ∈ 𝕂ˣ`, transport along `MonoidWithZeroHom`s, and the dilation factor
`hᵣ^{[b]₊} h₀^{-[-b]₊} ∈ 𝕂ˣ` propagating exchange polynomials under mutation.

## Main definitions

* `TauCeti.ExchangePolynomial 𝕂`: exchange polynomials of positive degree with unit endpoints.
* `TauCeti.ExchangePolynomial.reverse`: the reversal `Tʳ H(T⁻¹)`.
* `TauCeti.ExchangePolynomial.dilate`: the dilation `H(κT)` by a unit `κ : 𝕂ˣ`.
* `TauCeti.ExchangePolynomial.scale`: the multiple `e H` by a unit `e : 𝕂ˣ`.
* `TauCeti.ExchangePolynomial.dilationFactor`: the propagation unit `hᵣ^{[b]₊} h₀^{-[-b]₊}`.
* `TauCeti.ExchangePolynomial.binary`: the standard binary exchange polynomial `1 + T`.
* `TauCeti.ExchangePolynomial.binomial`: the degree-one exchange polynomial `h₀ + h₁ T`.
* `TauCeti.ExchangePolynomial.map`: coefficientwise pushforward along `𝕂 →*₀ 𝕂'`.
* `TauCeti.ExchangePolynomial.IsEndpointOne`: the predicate `h₀ = 1 ∧ hᵣ = 1`.

## Main results

* `TauCeti.ExchangePolynomial.reverse_reverse`: reversal is involutive.
* `TauCeti.ExchangePolynomial.reverse_dilate`:
  `(H.dilate κ).reverse = (H.reverse.dilate κ⁻¹).scale (κ ^ H.degree)`.
* `TauCeti.ExchangePolynomial.dilationFactor_reverse_neg`: reversing `H` and negating the exponent
  inverts the dilation factor.
* `TauCeti.ExchangePolynomial.dilationFactor_scale`: scaling `H` by `e` multiplies the dilation
  factor at `b` by `e ^ b`.
* `TauCeti.ExchangePolynomial.map_dilationFactor`: `MonoidWithZeroHom`s commute with
  `dilationFactor`.

## References

* L. Chekhov and M. Shapiro, *Teichmüller spaces of Riemann surfaces with orbifold points of
  arbitrary order and cluster variables*, Int. Math. Res. Not. (2014), §2, equation (2.5).
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277
  (2015), §2.
-/

public section

namespace TauCeti

/-- An *exchange polynomial* over a commutative monoid with zero `𝕂`: a specified positive degree
`r` and coefficients `h_l ∈ 𝕂` vanishing for `l > r`, whose endpoint coefficients `h₀` and `hᵣ` are
units. -/
structure ExchangePolynomial (𝕂 : Type*) [CommMonoidWithZero 𝕂] where
  /-- The specified positive degree `r` of the exchange polynomial. -/
  degree : ℕ
  /-- The degree is strictly positive. -/
  degree_pos : 0 < degree
  /-- The coefficient sequence, supported in `0, …, degree`. -/
  coeff : ℕ → 𝕂
  /-- Coefficients above the specified degree vanish. -/
  coeff_of_gt : ∀ l, degree < l → coeff l = 0
  /-- The constant coefficient `h₀` is a unit. -/
  isUnit_coeff_zero : IsUnit (coeff 0)
  /-- The leading coefficient `hᵣ` is a unit. -/
  isUnit_coeff_degree : IsUnit (coeff degree)

namespace ExchangePolynomial

variable {𝕂 𝕂' 𝕂'' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  [CommMonoidWithZero 𝕂'']

/-- Two exchange polynomials are equal if they have the same degree and agree on all coefficients
up to that degree. -/
@[ext]
theorem ext {H₁ H₂ : ExchangePolynomial 𝕂} (hdeg : H₁.degree = H₂.degree)
    (hcoeff : ∀ l ≤ H₁.degree, H₁.coeff l = H₂.coeff l) : H₁ = H₂ := by
  cases H₁ with | mk d₁ hd₁ c₁ hgt₁ h0₁ hr₁ =>
  cases H₂ with | mk d₂ hd₂ c₂ hgt₂ h0₂ hr₂ =>
  dsimp only at hdeg hcoeff
  subst hdeg
  congr 1
  funext l
  by_cases hl : l ≤ d₁
  · exact hcoeff l hl
  · rw [hgt₁ l (Nat.lt_of_not_ge hl), hgt₂ l (Nat.lt_of_not_ge hl)]

/-! ### Reversal, dilation, and scaling -/

/-- The reversal `Tʳ H(T⁻¹)` of an exchange polynomial `H` of degree `r`. -/
def reverse (H : ExchangePolynomial 𝕂) : ExchangePolynomial 𝕂 where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := if l ≤ H.degree then H.coeff (H.degree - l) else 0
  coeff_of_gt l hl := by simp [Nat.not_le_of_gt hl]
  isUnit_coeff_zero := by simpa using H.isUnit_coeff_degree
  isUnit_coeff_degree := by simpa using H.isUnit_coeff_zero

@[simp]
theorem reverse_degree (H : ExchangePolynomial 𝕂) : H.reverse.degree = H.degree :=
  (rfl)

theorem reverse_coeff (H : ExchangePolynomial 𝕂) (l : ℕ) :
    H.reverse.coeff l = if l ≤ H.degree then H.coeff (H.degree - l) else 0 :=
  (rfl)

@[simp]
theorem reverse_coeff_of_le (H : ExchangePolynomial 𝕂) {l : ℕ} (hl : l ≤ H.degree) :
    H.reverse.coeff l = H.coeff (H.degree - l) := by
  simp [reverse_coeff, hl]

theorem reverse_coeff_zero (H : ExchangePolynomial 𝕂) :
    H.reverse.coeff 0 = H.coeff H.degree := by
  simp

theorem reverse_coeff_degree (H : ExchangePolynomial 𝕂) :
    H.reverse.coeff H.degree = H.coeff 0 := by
  simp

/-- Reversing an exchange polynomial twice recovers it. -/
@[simp]
theorem reverse_reverse (H : ExchangePolynomial 𝕂) : H.reverse.reverse = H := by
  ext l hl
  · rfl
  · simp only [reverse_degree] at hl
    rw [reverse_coeff_of_le _ (by simpa using hl), reverse_degree,
      reverse_coeff_of_le _ (Nat.sub_le _ _), Nat.sub_sub_self hl]

/-- Reversal of exchange polynomials is an involution. -/
theorem reverse_involutive : Function.Involutive (reverse (𝕂 := 𝕂)) :=
  reverse_reverse

/-- The dilation `H(κT)` of an exchange polynomial by a unit `κ : 𝕂ˣ`. -/
def dilate (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) : ExchangePolynomial 𝕂 where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := H.coeff l * (κ : 𝕂) ^ l
  coeff_of_gt l hl := by simp [H.coeff_of_gt l hl]
  isUnit_coeff_zero := by simpa using H.isUnit_coeff_zero
  isUnit_coeff_degree := H.isUnit_coeff_degree.mul (κ.isUnit.pow _)

@[simp]
theorem dilate_degree (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) : (H.dilate κ).degree = H.degree :=
  (rfl)

@[simp]
theorem dilate_coeff (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) (l : ℕ) :
    (H.dilate κ).coeff l = H.coeff l * (κ : 𝕂) ^ l :=
  (rfl)

/-- Dilating by `1` leaves an exchange polynomial unchanged. -/
@[simp]
theorem dilate_one (H : ExchangePolynomial 𝕂) : H.dilate 1 = H := by
  ext
  · rfl
  · simp

/-- Dilating twice multiplies the dilation units. -/
@[simp]
theorem dilate_dilate (H : ExchangePolynomial 𝕂) (κ₁ κ₂ : 𝕂ˣ) :
    (H.dilate κ₁).dilate κ₂ = H.dilate (κ₁ * κ₂) := by
  ext
  · rfl
  · simp [mul_pow, mul_assoc]

/-- Dilating by `κ` and then by `κ⁻¹` recovers the original polynomial. -/
theorem dilate_inv_dilate (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ).dilate κ⁻¹ = H := by
  rw [dilate_dilate, mul_inv_cancel, dilate_one]

/-- Dilating by `κ⁻¹` and then by `κ` recovers the original polynomial. -/
theorem dilate_dilate_inv (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ⁻¹).dilate κ = H := by
  rw [dilate_dilate, inv_mul_cancel, dilate_one]

/-- The multiple `e H` of an exchange polynomial by a unit `e : 𝕂ˣ`. -/
def scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) : ExchangePolynomial 𝕂 where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := (e : 𝕂) * H.coeff l
  coeff_of_gt l hl := by simp [H.coeff_of_gt l hl]
  isUnit_coeff_zero := e.isUnit.mul H.isUnit_coeff_zero
  isUnit_coeff_degree := e.isUnit.mul H.isUnit_coeff_degree

@[simp]
theorem scale_degree (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) : (H.scale e).degree = H.degree :=
  (rfl)

@[simp]
theorem scale_coeff (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) (l : ℕ) :
    (H.scale e).coeff l = (e : 𝕂) * H.coeff l :=
  (rfl)

/-- Scaling by `1` leaves an exchange polynomial unchanged. -/
@[simp]
theorem scale_one (H : ExchangePolynomial 𝕂) : H.scale 1 = H := by
  ext
  · rfl
  · simp

/-- Scaling twice multiplies the scaling units. -/
@[simp]
theorem scale_scale (H : ExchangePolynomial 𝕂) (e₁ e₂ : 𝕂ˣ) :
    (H.scale e₁).scale e₂ = H.scale (e₂ * e₁) := by
  ext
  · rfl
  · simp [mul_assoc]

/-- Scaling by `e` and then by `e⁻¹` recovers the original polynomial. -/
theorem scale_inv_scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e).scale e⁻¹ = H := by
  rw [scale_scale, inv_mul_cancel, scale_one]

/-- Scaling by `e⁻¹` and then by `e` recovers the original polynomial. -/
theorem scale_scale_inv (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e⁻¹).scale e = H := by
  rw [scale_scale, mul_inv_cancel, scale_one]

/-- Scaling is injective in the unit factor, because the constant coefficient is a unit. -/
theorem scale_right_injective (H : ExchangePolynomial 𝕂) : Function.Injective H.scale := by
  intro e₁ e₂ h
  have h0 : (e₁ : 𝕂) * H.coeff 0 = (e₂ : 𝕂) * H.coeff 0 := by
    simpa only [scale_coeff] using congrArg (fun P : ExchangePolynomial 𝕂 ↦ P.coeff 0) h
  exact Units.ext (H.isUnit_coeff_zero.mul_right_cancel h0)

/-- Scaling an exchange polynomial fixes it if and only if the unit factor is `1`. -/
@[simp]
theorem scale_eq_self_iff (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) : H.scale e = H ↔ e = 1 :=
  ⟨fun h ↦ H.scale_right_injective (by simpa using h), fun h ↦ by simp [h]⟩

/-- Reversal commutes with scaling. -/
@[simp]
theorem reverse_scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e).reverse = H.reverse.scale e := by
  ext l hl
  · rfl
  · simp only [reverse_degree, scale_degree] at hl
    simp [hl]

/-- Dilation commutes with scaling. -/
@[simp]
theorem dilate_scale (H : ExchangePolynomial 𝕂) (e κ : 𝕂ˣ) :
    (H.scale e).dilate κ = (H.dilate κ).scale e := by
  ext
  · rfl
  · simp [mul_assoc]

/-- Reversing a dilated polynomial inverts the dilation factor and pulls out the top power
`κ ^ H.degree` as a scaling unit. -/
theorem reverse_dilate (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ).reverse = (H.reverse.dilate κ⁻¹).scale (κ ^ H.degree) := by
  ext l hl
  · rfl
  · simp only [reverse_degree, dilate_degree] at hl
    have hpow : (κ : 𝕂) ^ H.degree * ((κ⁻¹ : 𝕂ˣ) : 𝕂) ^ l = (κ : 𝕂) ^ (H.degree - l) := by
      have hu : κ ^ H.degree * κ⁻¹ ^ l = κ ^ (H.degree - l) := by
        rw [inv_pow, mul_inv_eq_iff_eq_mul, ← pow_add, Nat.sub_add_cancel hl]
      simpa using congrArg (Units.val : 𝕂ˣ → 𝕂) hu
    rw [reverse_coeff_of_le (H.dilate κ) (by simpa using hl)]
    simp only [dilate_degree, dilate_coeff, scale_coeff, reverse_coeff_of_le _ hl,
      Units.val_pow_eq_pow_val]
    calc
      H.coeff (H.degree - l) * (κ : 𝕂) ^ (H.degree - l)
          = H.coeff (H.degree - l) * ((κ : 𝕂) ^ H.degree * ((κ⁻¹ : 𝕂ˣ) : 𝕂) ^ l) := by rw [hpow]
      _ = (κ : 𝕂) ^ H.degree * (H.coeff (H.degree - l) * ((κ⁻¹ : 𝕂ˣ) : 𝕂) ^ l) := by
          rw [mul_left_comm]

/-! ### The dilation factor -/

/-- The dilation factor `hᵣ^{[b]₊} h₀^{-[-b]₊} ∈ 𝕂ˣ` associated to an exchange polynomial `H`
and a divided matrix entry `b : ℤ`. -/
noncomputable def dilationFactor (H : ExchangePolynomial 𝕂) (b : ℤ) : 𝕂ˣ :=
  H.isUnit_coeff_degree.unit ^ b⁺ * H.isUnit_coeff_zero.unit ^ (-b⁻)

/-- Express `dilationFactor` directly from explicit unit representatives of the endpoints. -/
theorem dilationFactor_eq (H : ExchangePolynomial 𝕂) (b : ℤ) {u₀ uᵣ : 𝕂ˣ}
    (h₀ : (u₀ : 𝕂) = H.coeff 0) (hᵣ : (uᵣ : 𝕂) = H.coeff H.degree) :
    H.dilationFactor b = uᵣ ^ b⁺ * u₀ ^ (-b⁻) := by
  have hu₀ : H.isUnit_coeff_zero.unit = u₀ := Units.ext (by simp [h₀])
  have huᵣ : H.isUnit_coeff_degree.unit = uᵣ := Units.ext (by simp [hᵣ])
  simp [dilationFactor, hu₀, huᵣ]

@[simp]
theorem dilationFactor_zero (H : ExchangePolynomial 𝕂) : H.dilationFactor 0 = 1 := by
  simp [dilationFactor]

/-- Reversing `H` and negating the exponent inverts the dilation factor. -/
@[simp]
theorem dilationFactor_reverse_neg (H : ExchangePolynomial 𝕂) (b : ℤ) :
    H.reverse.dilationFactor (-b) = (H.dilationFactor b)⁻¹ := by
  rw [H.reverse.dilationFactor_eq (-b) (u₀ := H.isUnit_coeff_degree.unit)
    (uᵣ := H.isUnit_coeff_zero.unit) (by simp) (by simp)]
  simp [dilationFactor, posPart_neg, negPart_neg, mul_comm]

/-- Reversing `H` evaluates the dilation factor to the inverse at the negated exponent. -/
theorem dilationFactor_reverse (H : ExchangePolynomial 𝕂) (b : ℤ) :
    H.reverse.dilationFactor b = (H.dilationFactor (-b))⁻¹ := by
  simpa using H.dilationFactor_reverse_neg (-b)

/-- Scaling `H` by a unit `e` multiplies the dilation factor at `b` by `e ^ b`. -/
theorem dilationFactor_scale (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) (b : ℤ) :
    (H.scale e).dilationFactor b = e ^ b * H.dilationFactor b := by
  rw [(H.scale e).dilationFactor_eq b (u₀ := e * H.isUnit_coeff_zero.unit)
    (uᵣ := e * H.isUnit_coeff_degree.unit) (by simp) (by simp)]
  rw [mul_zpow, mul_zpow, dilationFactor, mul_mul_mul_comm, ← zpow_add, ← sub_eq_add_neg,
    posPart_sub_negPart]

/-- Dilating `H` by `κ` multiplies the dilation factor at `b` by `κ ^ (H.degree * b⁺)`. -/
theorem dilationFactor_dilate (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) (b : ℤ) :
    (H.dilate κ).dilationFactor b = κ ^ ((H.degree : ℤ) * b⁺) * H.dilationFactor b := by
  rw [(H.dilate κ).dilationFactor_eq b (u₀ := H.isUnit_coeff_zero.unit)
    (uᵣ := H.isUnit_coeff_degree.unit * κ ^ H.degree) (by simp) (by simp)]
  rw [mul_zpow, ← zpow_natCast κ H.degree, ← zpow_mul, dilationFactor, mul_right_comm, mul_comm]

/-! ### Endpoint-one, binary, and binomial polynomials -/

/-- An exchange polynomial has unit endpoints equal to `1`: `h₀ = 1` and `hᵣ = 1`. -/
def IsEndpointOne (H : ExchangePolynomial 𝕂) : Prop :=
  H.coeff 0 = 1 ∧ H.coeff H.degree = 1

theorem isEndpointOne_iff (H : ExchangePolynomial 𝕂) :
    H.IsEndpointOne ↔ H.coeff 0 = 1 ∧ H.coeff H.degree = 1 :=
  Iff.rfl

theorem IsEndpointOne.coeff_zero {H : ExchangePolynomial 𝕂} (h : H.IsEndpointOne) :
    H.coeff 0 = 1 :=
  h.1

theorem IsEndpointOne.coeff_degree {H : ExchangePolynomial 𝕂} (h : H.IsEndpointOne) :
    H.coeff H.degree = 1 :=
  h.2

theorem IsEndpointOne.reverse {H : ExchangePolynomial 𝕂} (h : H.IsEndpointOne) :
    H.reverse.IsEndpointOne :=
  ⟨by simpa using h.2, by simpa using h.1⟩

@[simp]
theorem isEndpointOne_reverse_iff (H : ExchangePolynomial 𝕂) :
    H.reverse.IsEndpointOne ↔ H.IsEndpointOne :=
  ⟨fun h ↦ by simpa using h.reverse, IsEndpointOne.reverse⟩

/-- An exchange polynomial with endpoints equal to `1` has trivial dilation factor. -/
theorem IsEndpointOne.dilationFactor_eq_one {H : ExchangePolynomial 𝕂} (h : H.IsEndpointOne)
    (b : ℤ) : H.dilationFactor b = 1 := by
  rw [H.dilationFactor_eq b (u₀ := 1) (uᵣ := 1) (by simpa using h.1.symm)
    (by simpa using h.2.symm)]
  simp

/-- The binary exchange polynomial `1 + T`. -/
def binary : ExchangePolynomial 𝕂 where
  degree := 1
  degree_pos := Nat.one_pos
  coeff l := if l ≤ 1 then 1 else 0
  coeff_of_gt l hl := by simp [Nat.not_le_of_gt hl]
  isUnit_coeff_zero := by simp
  isUnit_coeff_degree := by simp

@[simp]
theorem binary_degree : (binary (𝕂 := 𝕂)).degree = 1 :=
  (rfl)

theorem binary_coeff (l : ℕ) : (binary (𝕂 := 𝕂)).coeff l = if l ≤ 1 then 1 else 0 :=
  (rfl)

@[simp]
theorem binary_coeff_zero : (binary (𝕂 := 𝕂)).coeff 0 = 1 :=
  (rfl)

@[simp]
theorem binary_coeff_one : (binary (𝕂 := 𝕂)).coeff 1 = 1 :=
  (rfl)

@[simp]
theorem isEndpointOne_binary : (binary (𝕂 := 𝕂)).IsEndpointOne :=
  ⟨rfl, rfl⟩

@[simp]
theorem reverse_binary : (binary (𝕂 := 𝕂)).reverse = binary := by
  ext l hl
  · rfl
  · have hl' : l ≤ 1 := hl
    rw [reverse_coeff_of_le _ hl']
    simp [binary_coeff, hl']

@[simp]
theorem dilationFactor_binary (b : ℤ) : (binary (𝕂 := 𝕂)).dilationFactor b = 1 :=
  isEndpointOne_binary.dilationFactor_eq_one b

/-- The degree-one exchange polynomial `h₀ + h₁ T` with unit coefficients `h₀, h₁ : 𝕂ˣ`. -/
def binomial (h₀ h₁ : 𝕂ˣ) : ExchangePolynomial 𝕂 where
  degree := 1
  degree_pos := Nat.one_pos
  coeff
    | 0 => (h₀ : 𝕂)
    | 1 => (h₁ : 𝕂)
    | _ + 2 => 0
  coeff_of_gt l hl := by
    obtain _ | _ | l := l
    · omega
    · omega
    · rfl
  isUnit_coeff_zero := h₀.isUnit
  isUnit_coeff_degree := h₁.isUnit

@[simp]
theorem binomial_degree (h₀ h₁ : 𝕂ˣ) : (binomial h₀ h₁).degree = 1 :=
  (rfl)

@[simp]
theorem binomial_coeff_zero (h₀ h₁ : 𝕂ˣ) : (binomial h₀ h₁).coeff 0 = (h₀ : 𝕂) :=
  (rfl)

@[simp]
theorem binomial_coeff_one (h₀ h₁ : 𝕂ˣ) : (binomial h₀ h₁).coeff 1 = (h₁ : 𝕂) :=
  (rfl)

@[simp]
theorem binomial_one_one : binomial (1 : 𝕂ˣ) 1 = binary := by
  ext l hl
  · rfl
  · simp only [binomial_degree] at hl
    have hl' : l = 0 ∨ l = 1 := by omega
    rcases hl' with rfl | rfl <;> rfl

@[simp]
theorem reverse_binomial (h₀ h₁ : 𝕂ˣ) : (binomial h₀ h₁).reverse = binomial h₁ h₀ := by
  ext l hl
  · rfl
  · simp only [reverse_degree, binomial_degree] at hl
    have hl' : l = 0 ∨ l = 1 := by omega
    rcases hl' with rfl | rfl <;> simp

@[simp]
theorem scale_binomial (h₀ h₁ e : 𝕂ˣ) :
    (binomial h₀ h₁).scale e = binomial (e * h₀) (e * h₁) := by
  ext l hl
  · rfl
  · simp only [scale_degree, binomial_degree] at hl
    have hl' : l = 0 ∨ l = 1 := by omega
    rcases hl' with rfl | rfl <;> simp

@[simp]
theorem dilate_binomial (h₀ h₁ κ : 𝕂ˣ) :
    (binomial h₀ h₁).dilate κ = binomial h₀ (h₁ * κ) := by
  ext l hl
  · rfl
  · simp only [dilate_degree, binomial_degree] at hl
    have hl' : l = 0 ∨ l = 1 := by omega
    rcases hl' with rfl | rfl <;> simp

@[simp]
theorem dilationFactor_binomial (h₀ h₁ : 𝕂ˣ) (b : ℤ) :
    (binomial h₀ h₁).dilationFactor b = h₁ ^ b⁺ * h₀ ^ (-b⁻) :=
  (binomial h₀ h₁).dilationFactor_eq b rfl rfl

/-- Every degree-one exchange polynomial is a binomial built from its endpoint units. -/
theorem eq_binomial_of_degree_eq_one {H : ExchangePolynomial 𝕂} (hdeg : H.degree = 1) :
    H = binomial H.isUnit_coeff_zero.unit H.isUnit_coeff_degree.unit := by
  ext l hl
  · exact hdeg
  · have hl' : l = 0 ∨ l = 1 := by omega
    rcases hl' with rfl | rfl
    · simp
    · rw [binomial_coeff_one, IsUnit.unit_spec, hdeg]

/-! ### Coefficientwise pushforward -/

/-- Push forward an exchange polynomial coefficientwise along a `MonoidWithZeroHom`. -/
def map (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) : ExchangePolynomial 𝕂' where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff l := f (H.coeff l)
  coeff_of_gt l hl := by simp [H.coeff_of_gt l hl]
  isUnit_coeff_zero := H.isUnit_coeff_zero.map f
  isUnit_coeff_degree := H.isUnit_coeff_degree.map f

@[simp]
theorem map_degree (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) : (H.map f).degree = H.degree :=
  (rfl)

@[simp]
theorem map_coeff (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) (l : ℕ) :
    (H.map f).coeff l = f (H.coeff l) :=
  (rfl)

@[simp]
theorem map_id (H : ExchangePolynomial 𝕂) : H.map (MonoidWithZeroHom.id 𝕂) = H := by
  ext
  · rfl
  · simp

@[simp]
theorem map_comp (g : 𝕂' →*₀ 𝕂'') (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) :
    H.map (g.comp f) = (H.map f).map g := by
  ext
  · rfl
  · simp

@[simp]
theorem map_reverse (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) :
    H.reverse.map f = (H.map f).reverse := by
  ext l hl
  · rfl
  · simp only [map_degree, reverse_degree] at hl
    simp [hl]

@[simp]
theorem map_dilate (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) (κ : 𝕂ˣ) :
    (H.dilate κ).map f = (H.map f).dilate (Units.map f.toMonoidHom κ) := by
  ext
  · rfl
  · simp

@[simp]
theorem map_scale (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) (e : 𝕂ˣ) :
    (H.scale e).map f = (H.map f).scale (Units.map f.toMonoidHom e) := by
  ext
  · rfl
  · simp

@[simp]
theorem map_dilationFactor (f : 𝕂 →*₀ 𝕂') (H : ExchangePolynomial 𝕂) (b : ℤ) :
    (H.map f).dilationFactor b = Units.map f.toMonoidHom (H.dilationFactor b) := by
  rw [(H.map f).dilationFactor_eq b (u₀ := Units.map f.toMonoidHom H.isUnit_coeff_zero.unit)
    (uᵣ := Units.map f.toMonoidHom H.isUnit_coeff_degree.unit) (by simp) (by simp)]
  simp [dilationFactor]

@[simp]
theorem map_binary (f : 𝕂 →*₀ 𝕂') : (binary (𝕂 := 𝕂)).map f = binary := by
  ext l hl
  · rfl
  · simp only [map_degree, binary_degree] at hl
    have hl' : l = 0 ∨ l = 1 := by omega
    rcases hl' with rfl | rfl <;> simp

@[simp]
theorem map_binomial (f : 𝕂 →*₀ 𝕂') (h₀ h₁ : 𝕂ˣ) :
    (binomial h₀ h₁).map f =
      binomial (Units.map f.toMonoidHom h₀) (Units.map f.toMonoidHom h₁) := by
  ext l hl
  · rfl
  · simp only [map_degree, binomial_degree] at hl
    have hl' : l = 0 ∨ l = 1 := by omega
    rcases hl' with rfl | rfl <;> simp

theorem IsEndpointOne.map {H : ExchangePolynomial 𝕂} (h : H.IsEndpointOne) (f : 𝕂 →*₀ 𝕂') :
    (H.map f).IsEndpointOne :=
  ⟨by simp [h.1], by simp [h.2]⟩

end ExchangePolynomial

end TauCeti
