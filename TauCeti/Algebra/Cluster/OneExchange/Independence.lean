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
theorem exchange_pow_eq (x E : Bˣ) (n : ℕ) :
    (E * x⁻¹) ^ n = exchangeProduct x E n * x⁻¹ ^ n := by
  unfold exchangeProduct
  group

/-- If `E` commutes with `x`, ordered exchange products are ordinary powers of `E`. -/
theorem exchangeProduct_eq_pow (x E : Bˣ) (h : Commute x E) (n : ℕ) :
    exchangeProduct x E n = E ^ n := by
  rw [exchangeProduct, (h.symm.inv_right).mul_pow]
  simp [mul_assoc]

/-- Multiplicative maps transport the ordered exchange coefficients. -/
@[simp]
theorem map_exchangeProduct {A : Type*} [Monoid A] (x E : Bˣ) (n : ℕ) (f : B →* A) :
    Units.map f (exchangeProduct x E n) =
      exchangeProduct (Units.map f x) (Units.map f E) n := by
  simp [exchangeProduct]

end Units

namespace Subsemiring

variable {B : Type*} [Semiring B] (C : Subsemiring B) (x E : Bˣ)

/-- Ordered exchange products remain in the coefficient subsemiring if inverse
conjugation by the old coordinate preserves it. -/
theorem exchangeProduct_mem
    (hx : ∀ c ∈ C, (↑x⁻¹ : B) * c * x ∈ C) (hE : (E : B) ∈ C) (n : ℕ) :
    (Units.exchangeProduct x E n : B) ∈ C := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [Units.exchangeProduct_succ', Units.val_mul] using C.mul_mem hE (hx _ ih)

/-- A skew exchange preserves independence of natural powers, with left coefficients
in `C`. The numerator need only be a unit in the ambient semiring. -/
theorem linearIndependent_pow_exchange
    (hx : ∀ c ∈ C, (↑x⁻¹ : B) * c * x ∈ C) (hE : (E : B) ∈ C)
    (hli : LinearIndependent C (fun n : ℤ ↦ (↑(x ^ n) : B))) :
    LinearIndependent C (fun n : ℕ ↦ (↑((E * x⁻¹) ^ n) : B)) := by
  classical
  let p (n : ℕ) : C := ⟨Units.exchangeProduct x E n, C.exchangeProduct_mem x E hx hE n⟩
  have hinj : Function.Injective (fun n : ℕ ↦ -(n : ℤ)) := by
    intro a b hab
    exact Nat.cast_injective (neg_injective hab)
  have hi := hli.comp _ hinj
  apply linearIndependent_iff'ₛ.mpr
  intro s f g hfg n hn
  have hsum (c : ℕ → C) :
      (∑ i ∈ s, c i • (↑((E * x⁻¹) ^ i) : B)) =
        ∑ i ∈ s, (c i * p i) • (↑(x ^ (-(i : ℤ))) : B) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Units.exchange_pow_eq, Units.val_mul, zpow_neg, zpow_natCast,
      Subsemiring.smul_def, smul_eq_mul, Subsemiring.coe_mul, mul_assoc, inv_pow, p]
  rw [hsum f, hsum g] at hfg
  have he := linearIndependent_iff'ₛ.mp hi s (fun i ↦ f i * p i)
    (fun i ↦ g i * p i) hfg n hn
  apply Subtype.ext
  exact (Units.exchangeProduct x E n).isUnit.mul_left_injective
    (congrArg (fun c : C ↦ (c : B)) he)

/-- A skew exchange preserves unique Laurent coefficients. No domain, centrality,
additive cancellation, or invertibility of the numerator inside `C` is required. -/
theorem linearIndependent_zpow_exchange
    (hx : ∀ c ∈ C, (↑x⁻¹ : B) * c * x ∈ C) (hE : (E : B) ∈ C)
    (hli : LinearIndependent C (fun n : ℤ ↦ (↑(x ^ n) : B))) :
    LinearIndependent C (fun n : ℤ ↦ (↑((E * x⁻¹) ^ n) : B)) :=
  (Units.linearIndependent_zpow_iff (R := C) _).mpr
    (C.linearIndependent_pow_exchange x E hx hE hli)

end Subsemiring
