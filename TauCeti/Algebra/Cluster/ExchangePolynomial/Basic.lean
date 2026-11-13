/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Tactic.Ext

/-!
# Exchange polynomials

An exchange polynomial consists of a positive specified degree and a finite coefficient vector
with unit endpoints. The coefficients need only form a commutative monoid with zero: reversal,
unit dilation and unit scaling do not use addition. This allows the same data to describe both
scalar exchange polynomials and coefficients realized by a merely multiplicative map.

The endpoint dilation factor is the coefficient propagation used when mutating another
direction. Reversal and negation of the corresponding matrix entry invert this factor.

The coefficient transformations follow Chekhov–Shapiro, *Teichmüller spaces of Riemann surfaces
with orbifold points of arbitrary order and cluster variables*, §2.1, and Nakanishi,
*Structure of seeds in generalized cluster algebras*, Definition 2.2 and (2.5)–(2.6).
-/

public section

namespace TauCeti

/-- A positive-degree coefficient vector with unit constant and leading coefficients.
Coefficients above the specified degree are required to vanish. -/
structure ExchangePolynomial (K : Type*) [CommMonoidWithZero K] where
  /-- The specified positive degree. -/
  degree : ℕ
  degree_pos : 0 < degree
  /-- The coefficient function, extended by zero above the degree. -/
  coeff : ℕ → K
  coeff_eq_zero : ∀ i, degree < i → coeff i = 0
  isUnit_zero : IsUnit (coeff 0)
  isUnit_last : IsUnit (coeff degree)

namespace ExchangePolynomial

variable {K L M : Type*} [CommMonoidWithZero K] [CommMonoidWithZero L]
  [CommMonoidWithZero M]

/-- Exchange polynomials are determined by their degrees and coefficients. -/
@[ext]
theorem ext {H G : ExchangePolynomial K} (hd : H.degree = G.degree)
    (hc : ∀ i, H.coeff i = G.coeff i) : H = G := by
  cases H
  cases G
  simp_all [mk.injEq, funext_iff]

/-- Reversal reads the coefficient vector backwards. -/
def reverse (H : ExchangePolynomial K) : ExchangePolynomial K where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff i := if i ≤ H.degree then H.coeff (H.degree - i) else 0
  coeff_eq_zero i hi := by simp [Nat.not_le.mpr hi]
  isUnit_zero := by simpa using H.isUnit_last
  isUnit_last := by simpa using H.isUnit_zero

@[simp] theorem degree_reverse (H : ExchangePolynomial K) : H.reverse.degree = H.degree :=
  (rfl)

@[simp] theorem coeff_reverse (H : ExchangePolynomial K) (i : ℕ) :
    H.reverse.coeff i = if i ≤ H.degree then H.coeff (H.degree - i) else 0 := (rfl)

@[simp] theorem reverse_reverse (H : ExchangePolynomial K) : H.reverse.reverse = H := by
  apply ext (by simp)
  intro i
  by_cases hi : i ≤ H.degree
  · simp [hi, Nat.sub_sub_self hi]
  · simp [hi, H.coeff_eq_zero i (by omega)]

/-- Dilating by `κ` replaces the formal variable `T` by `κ T`. -/
def dilate (H : ExchangePolynomial K) (κ : Kˣ) : ExchangePolynomial K where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff i := (κ : K) ^ i * H.coeff i
  coeff_eq_zero i hi := by simp [H.coeff_eq_zero i hi]
  isUnit_zero := by simpa using H.isUnit_zero
  isUnit_last := (κ.isUnit.pow _).mul H.isUnit_last

@[simp] theorem degree_dilate (H : ExchangePolynomial K) (κ : Kˣ) :
    (H.dilate κ).degree = H.degree := (rfl)

@[simp] theorem coeff_dilate (H : ExchangePolynomial K) (κ : Kˣ)
    (i : ℕ) :
    (H.dilate κ).coeff i = (κ : K) ^ i * H.coeff i := (rfl)

@[simp] theorem dilate_one (H : ExchangePolynomial K) : H.dilate 1 = H := by
  apply ext (by simp)
  simp

@[simp] theorem dilate_dilate (H : ExchangePolynomial K) (κ η : Kˣ) :
    (H.dilate κ).dilate η = H.dilate (η * κ) := by
  apply ext (by simp)
  simp [mul_pow, mul_assoc]

/-- Scaling multiplies every coefficient by the same unit. -/
def scale (H : ExchangePolynomial K) (e : Kˣ) : ExchangePolynomial K where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff i := (e : K) * H.coeff i
  coeff_eq_zero i hi := by simp [H.coeff_eq_zero i hi]
  isUnit_zero := e.isUnit.mul H.isUnit_zero
  isUnit_last := e.isUnit.mul H.isUnit_last

@[simp] theorem degree_scale (H : ExchangePolynomial K) (e : Kˣ) :
    (H.scale e).degree = H.degree := (rfl)

@[simp] theorem coeff_scale (H : ExchangePolynomial K) (e : Kˣ)
    (i : ℕ) : (H.scale e).coeff i = (e : K) * H.coeff i := (rfl)

@[simp] theorem scale_one (H : ExchangePolynomial K) : H.scale 1 = H := by
  apply ext (by simp)
  simp

@[simp] theorem scale_scale (H : ExchangePolynomial K) (e f : Kˣ) :
    (H.scale e).scale f = H.scale (f * e) := by
  apply ext (by simp)
  simp [mul_assoc]

@[simp] theorem reverse_scale (H : ExchangePolynomial K) (e : Kˣ) :
    (H.scale e).reverse = H.reverse.scale e := by
  apply ext (by simp)
  intro i
  by_cases hi : i ≤ H.degree <;> simp [hi]

/-- Dilation and scaling commute. -/
theorem dilate_scale (H : ExchangePolynomial K) (κ e : Kˣ) :
    (H.scale e).dilate κ = (H.dilate κ).scale e := by
  apply ext (by simp)
  simp [mul_left_comm]

/-- Reversing a dilated polynomial inverts the dilation and introduces its degree power. -/
theorem reverse_dilate (H : ExchangePolynomial K) (κ : Kˣ) :
    (H.dilate κ).reverse = (H.reverse.dilate κ⁻¹).scale (κ ^ H.degree) := by
  apply ext (by simp)
  intro i
  by_cases hi : i ≤ H.degree
  · have hp : κ ^ H.degree * (κ⁻¹) ^ i = κ ^ (H.degree - i) := by
      conv_lhs => rw [← Nat.sub_add_cancel hi]
      rw [pow_add]
      simp [mul_assoc]
    have hv := congrArg (fun u : Kˣ => (u : K)) hp
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hv
    simp only [coeff_reverse, degree_dilate, hi, ite_true, coeff_dilate,
      coeff_scale, Units.val_pow_eq_pow_val, ← mul_assoc, hv]
  · simp [hi]

/-- Apply a zero-preserving multiplicative coefficient map, keeping the specified degree. -/
def map (H : ExchangePolynomial K) (f : K →*₀ L) : ExchangePolynomial L where
  degree := H.degree
  degree_pos := H.degree_pos
  coeff i := f (H.coeff i)
  coeff_eq_zero i hi := by simp [H.coeff_eq_zero i hi]
  isUnit_zero := H.isUnit_zero.map f
  isUnit_last := H.isUnit_last.map f

@[simp] theorem degree_map (H : ExchangePolynomial K) (f : K →*₀ L) :
    (H.map f).degree = H.degree := (rfl)

@[simp] theorem coeff_map (H : ExchangePolynomial K) (f : K →*₀ L)
    (i : ℕ) : (H.map f).coeff i = f (H.coeff i) := (rfl)

@[simp] theorem map_id (H : ExchangePolynomial K) : H.map (.id K) = H := by
  apply ext (by simp)
  simp

@[simp] theorem map_map (H : ExchangePolynomial K) (f : K →*₀ L) (g : L →*₀ M) :
    (H.map f).map g = H.map (g.comp f) := by
  apply ext (by simp)
  simp

@[simp] theorem map_reverse (H : ExchangePolynomial K) (f : K →*₀ L) :
    H.reverse.map f = (H.map f).reverse := by
  apply ext (by simp)
  intro i
  by_cases hi : i ≤ H.degree <;> simp [hi]

@[simp] theorem map_dilate (H : ExchangePolynomial K) (f : K →*₀ L) (κ : Kˣ) :
    (H.dilate κ).map f = (H.map f).dilate (Units.map f.toMonoidHom κ) := by
  apply ext (by simp)
  simp

@[simp] theorem map_scale (H : ExchangePolynomial K) (f : K →*₀ L) (e : Kˣ) :
    (H.scale e).map f = (H.map f).scale (Units.map f.toMonoidHom e) := by
  apply ext (by simp)
  simp

/-- The binary exchange polynomial `1 + T`. -/
def binary : ExchangePolynomial K where
  degree := 1
  degree_pos := by decide
  coeff i := if i ≤ 1 then 1 else 0
  coeff_eq_zero i hi := by simp [Nat.not_le.mpr hi]
  isUnit_zero := by simp
  isUnit_last := by simp

@[simp] theorem degree_binary : (binary : ExchangePolynomial K).degree = 1 := (rfl)

@[simp] theorem coeff_binary (i : ℕ) :
    (binary : ExchangePolynomial K).coeff i = if i ≤ 1 then 1 else 0 :=
  (rfl)

@[simp] theorem reverse_binary : (binary : ExchangePolynomial K).reverse = binary := by
  apply ext (by simp)
  intro i
  by_cases hi : i ≤ 1 <;> simp [hi]

@[simp] theorem map_binary (f : K →*₀ L) : (binary : ExchangePolynomial K).map f = binary := by
  apply ext (by simp)
  intro i
  by_cases hi : i ≤ 1 <;> simp [hi]

/-- The unit represented by the constant coefficient. -/
noncomputable def constantUnit (H : ExchangePolynomial K) : Kˣ := H.isUnit_zero.unit

/-- The unit represented by the highest coefficient. -/
noncomputable def leadingUnit (H : ExchangePolynomial K) : Kˣ := H.isUnit_last.unit

@[simp] theorem coe_constantUnit (H : ExchangePolynomial K) :
    (H.constantUnit : K) = H.coeff 0 := H.isUnit_zero.unit_spec

@[simp] theorem coe_leadingUnit (H : ExchangePolynomial K) :
    (H.leadingUnit : K) = H.coeff H.degree := H.isUnit_last.unit_spec

@[simp] theorem constantUnit_reverse (H : ExchangePolynomial K) :
    H.reverse.constantUnit = H.leadingUnit := by
  ext
  simp

@[simp] theorem leadingUnit_reverse (H : ExchangePolynomial K) :
    H.reverse.leadingUnit = H.constantUnit := by
  ext
  simp

@[simp] theorem constantUnit_dilate (H : ExchangePolynomial K) (κ : Kˣ) :
    (H.dilate κ).constantUnit = H.constantUnit := by
  ext
  simp

@[simp] theorem leadingUnit_dilate (H : ExchangePolynomial K) (κ : Kˣ) :
    (H.dilate κ).leadingUnit = κ ^ H.degree * H.leadingUnit := by
  ext
  simp

@[simp] theorem constantUnit_scale (H : ExchangePolynomial K) (e : Kˣ) :
    (H.scale e).constantUnit = e * H.constantUnit := by
  ext
  simp

@[simp] theorem leadingUnit_scale (H : ExchangePolynomial K) (e : Kˣ) :
    (H.scale e).leadingUnit = e * H.leadingUnit := by
  ext
  simp

@[simp] theorem constantUnit_map (H : ExchangePolynomial K) (f : K →*₀ L) :
    (H.map f).constantUnit = Units.map f.toMonoidHom H.constantUnit := by
  ext
  simp

@[simp] theorem leadingUnit_map (H : ExchangePolynomial K) (f : K →*₀ L) :
    (H.map f).leadingUnit = Units.map f.toMonoidHom H.leadingUnit := by
  ext
  simp

/-- The propagation factor `h_r^[b]₊ h_0^(-[-b]₊)` for an integer matrix entry `b`. -/
noncomputable def dilationFactor (H : ExchangePolynomial K) (b : ℤ) : Kˣ :=
  H.leadingUnit ^ b.toNat * (H.constantUnit ^ (-b).toNat)⁻¹

/-- Propagation is expressed entirely in terms of the two endpoint units. -/
theorem dilationFactor_def (H : ExchangePolynomial K) (b : ℤ) :
    H.dilationFactor b = H.leadingUnit ^ b.toNat * (H.constantUnit ^ (-b).toNat)⁻¹ := (rfl)

@[simp] theorem dilationFactor_zero (H : ExchangePolynomial K) : H.dilationFactor 0 = 1 := by
  simp [dilationFactor]

/-- Reversal together with the sign change of the matrix entry inverts the propagation factor. -/
@[simp] theorem dilationFactor_reverse_neg (H : ExchangePolynomial K) (b : ℤ) :
    H.reverse.dilationFactor (-b) = (H.dilationFactor b)⁻¹ := by
  simp [dilationFactor, mul_comm]

/-- Coefficient realization preserves endpoint propagation, without requiring additivity. -/
@[simp] theorem dilationFactor_map (H : ExchangePolynomial K) (f : K →*₀ L) (b : ℤ) :
    (H.map f).dilationFactor b = Units.map f.toMonoidHom (H.dilationFactor b) := by
  simp [dilationFactor]

/-- Unit endpoint coefficients equal to one make propagation trivial. -/
theorem dilationFactor_eq_one (H : ExchangePolynomial K)
    (h0 : H.coeff 0 = 1) (hr : H.coeff H.degree = 1) (b : ℤ) :
    H.dilationFactor b = 1 := by
  have hc : H.constantUnit = 1 := Units.ext (by simp [h0])
  have hl : H.leadingUnit = 1 := Units.ext (by simp [hr])
  simp [dilationFactor, hc, hl]

@[simp] theorem dilationFactor_binary (b : ℤ) :
    (binary : ExchangePolynomial K).dilationFactor b = 1 := by
  apply dilationFactor_eq_one <;> simp

end ExchangePolynomial

end TauCeti
