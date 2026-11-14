/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearIndependent.Powers
public import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Tactic.Group

/-!
# Faithfulness under one skew exchange

Let `C` be a subsemiring of `B`, let `x` be a unit whose inverse conjugation preserves
`C`, and let `E` belong to `C` and be a unit of `B`. The exchange `y = E * x⁻¹`
preserves linear independence of integer powers with left coefficients in `C`.
Thus a faithful skew Laurent coordinate remains faithful after exchange, even when
`E` is not a unit of `C` and `B` has zero divisors.

The ordered exchange products `P n` satisfy `y ^ n = P n * x ^ (-n)` and
`P (n+1) = P n * x ^ (-n) * E * x ^ n`. They are units of the ambient semiring
with values in `C`; their right cancellation transfers uniqueness of coefficients
from powers of `x⁻¹` to powers of `y`. Shifting finite relations then gives
uniqueness for all integer powers.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), Lemmas 5.5–5.6, for skew exchange and ordered exchange factors.
* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and
  double Bruhat cells*, Duke Mathematical Journal 126 (2005), Lemmas 4.1–4.2,
  for the commutative exchange.
-/

public section

namespace Units

variable {B : Type*} [Monoid B]

/-- The ordered coefficient in the `n`th power of the exchange `E * x⁻¹`.
It is a unit of the ambient monoid, without asserting that it is a coefficient unit. -/
def exchangeProduct (x E : Bˣ) (n : ℕ) : Bˣ :=
  (E * x⁻¹) ^ n * x ^ n

/-- The defining formula for the ordered exchange coefficient. -/
theorem exchangeProduct_def (x E : Bˣ) (n : ℕ) :
    exchangeProduct x E n = (E * x⁻¹) ^ n * x ^ n := (rfl)

@[simp]
theorem exchangeProduct_one_left (E : Bˣ) (n : ℕ) : exchangeProduct 1 E n = E ^ n := by
  simp [exchangeProduct_def]

@[simp]
theorem exchangeProduct_one_right (x : Bˣ) (n : ℕ) : exchangeProduct x 1 n = 1 := by
  simp [exchangeProduct_def]

@[simp]
theorem exchangeProduct_zero (x E : Bˣ) : exchangeProduct x E 0 = 1 := by
  simp [exchangeProduct]

@[simp]
theorem exchangeProduct_one (x E : Bˣ) : exchangeProduct x E 1 = E := by
  simp [exchangeProduct, mul_assoc]

/-- The ordered recurrence, with the next conjugated factor on the right. -/
theorem exchangeProduct_succ (x E : Bˣ) (n : ℕ) :
    exchangeProduct x E (n + 1) = exchangeProduct x E n * x⁻¹ ^ n * E * x ^ n := by
  unfold exchangeProduct
  rw [pow_succ (E * x⁻¹), pow_succ x]
  group

/-- The recurrence by inverse conjugation, useful for coefficient membership. -/
theorem exchangeProduct_succ' (x E : Bˣ) (n : ℕ) :
    exchangeProduct x E (n + 1) = E * (x⁻¹ * exchangeProduct x E n * x) := by
  unfold exchangeProduct
  group

/-- Powers of an exchange have the ordered coefficient `exchangeProduct`. -/
theorem mul_inv_pow_eq_exchangeProduct_mul_inv_pow (x E : Bˣ) (n : ℕ) :
    (E * x⁻¹) ^ n = exchangeProduct x E n * x⁻¹ ^ n := by
  unfold exchangeProduct
  group

/-- If `E` commutes with `x`, ordered exchange products are ordinary powers of `E`. -/
theorem exchangeProduct_eq_pow_of_commute {x E : Bˣ} (h : Commute x E) (n : ℕ) :
    exchangeProduct x E n = E ^ n := by
  rw [exchangeProduct_def, (h.symm.inv_right).mul_pow]
  simp [mul_assoc]

end Units

namespace Units

variable {B : Type*} [CommMonoid B]

/-- Ordered exchange products in a commutative monoid are ordinary powers. -/
@[simp]
theorem exchangeProduct_eq_pow (x E : Bˣ) (n : ℕ) : exchangeProduct x E n = E ^ n :=
  exchangeProduct_eq_pow_of_commute (.all x E) n

end Units

namespace Units

variable {B : Type*} [Monoid B]

/-- Multiplicative maps transport the ordered exchange coefficients. -/
@[simp]
theorem map_exchangeProduct {A F : Type*} [Monoid A] [FunLike F Bˣ Aˣ]
    [MonoidHomClass F Bˣ Aˣ] (f : F) (x E : Bˣ) (n : ℕ) :
    f (exchangeProduct x E n) = exchangeProduct (f x) (f E) n := by
  simp [exchangeProduct_def]

end Units

namespace SubmonoidClass

variable {B S : Type*} [Monoid B] [SetLike S B] [SubmonoidClass S B] (C : S) (x E : Bˣ)

/-- Ordered exchange products remain in the coefficient submonoid if inverse
conjugation by the old coordinate preserves it. -/
theorem exchangeProduct_mem
    (hx : ∀ c ∈ C, (↑x⁻¹ : B) * c * x ∈ C) (hE : (E : B) ∈ C) (n : ℕ) :
    (Units.exchangeProduct x E n : B) ∈ C := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [Units.exchangeProduct_succ', Units.val_mul] using mul_mem hE (hx _ ih)

end SubmonoidClass

namespace SubsemiringClass

variable {B S : Type*} [Semiring B] [SetLike S B] [SubsemiringClass S B] (C : S) (x E : Bˣ)

/-- Independence of natural powers of `x` implies independence of natural powers of
`E * x⁻¹`, with left coefficients in `C`. The numerator need only be a unit in the
ambient semiring. -/
theorem linearIndependent_mul_inv_pow
    (hx : ∀ c ∈ C, (↑x⁻¹ : B) * c * x ∈ C) (hE : (E : B) ∈ C)
    (hli : LinearIndependent C (fun n : ℕ ↦ (↑(x ^ n) : B))) :
    LinearIndependent C (fun n : ℕ ↦ (↑((E * x⁻¹) ^ n) : B)) := by
  classical
  let p (n : ℕ) : C := ⟨Units.exchangeProduct x E n,
    SubmonoidClass.exchangeProduct_mem C x E hx hE n⟩
  have hp (n : ℕ) : IsRightRegular (p n) :=
    fun _ _ h ↦ Subtype.ext <| (Units.exchangeProduct x E n).isRegular.right
      (congrArg ((↑) : C → B) h)
  have hi := ((Units.linearIndependent_zpow_iff x).mpr hli).comp (fun n : ℕ ↦ -(n : ℤ))
    (neg_injective.comp Nat.cast_injective)
  have hsmul (c : C) (b : B) : c • b = (c : B) * b := by
    change (c : B) • b = _
    rw [smul_eq_mul]
  have hfactor : (p • ((fun n : ℤ ↦ (↑(x ^ n) : B)) ∘ fun n : ℕ ↦ -(n : ℤ))) =
      fun n : ℕ ↦ (↑((E * x⁻¹) ^ n) : B) := by
    funext n
    rw [Units.mul_inv_pow_eq_exchangeProduct_mul_inv_pow]
    simp only [Pi.smul_apply', Function.comp_apply, hsmul, p, Units.val_mul,
      zpow_neg, zpow_natCast, inv_pow]
  simpa only [hfactor] using hi.smul_of_isRightRegular hp

/-- A skew exchange preserves unique Laurent coefficients. No domain, centrality,
additive cancellation, or invertibility of the numerator inside `C` is required. -/
theorem linearIndependent_mul_inv_zpow
    (hx : ∀ c ∈ C, (↑x⁻¹ : B) * c * x ∈ C) (hE : (E : B) ∈ C)
    (hli : LinearIndependent C (fun n : ℤ ↦ (↑(x ^ n) : B))) :
    LinearIndependent C (fun n : ℤ ↦ (↑((E * x⁻¹) ^ n) : B)) :=
  (Units.linearIndependent_zpow_iff (R := C) _).mpr
    (linearIndependent_mul_inv_pow C x E hx hE ((Units.linearIndependent_zpow_iff x).mp hli))

end SubsemiringClass
