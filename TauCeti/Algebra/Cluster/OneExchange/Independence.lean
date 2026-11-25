/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Submonoid.MulAction
public import TauCeti.Algebra.Ring.Action.ConjAct
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

open scoped Pointwise

namespace TauCeti

section Group

variable {G : Type*} [Group G]

/-- The ordered coefficient in the `n`th power of the exchange `E * x⁻¹` in a group.
For units of a monoid, it is a unit of the ambient monoid, without asserting that it is a
coefficient unit. -/
def exchangeProduct (x E : G) (n : ℕ) : G :=
  (E * x⁻¹) ^ n * x ^ n

/-- The defining formula for the ordered exchange coefficient. -/
theorem exchangeProduct_def (x E : G) (n : ℕ) :
    exchangeProduct x E n = (E * x⁻¹) ^ n * x ^ n := (rfl)

@[simp]
theorem exchangeProduct_one_left (E : G) (n : ℕ) : exchangeProduct 1 E n = E ^ n := by
  simp [exchangeProduct_def]

@[simp]
theorem exchangeProduct_one_right (x : G) (n : ℕ) : exchangeProduct x 1 n = 1 := by
  simp [exchangeProduct_def]

@[simp]
theorem exchangeProduct_zero (x E : G) : exchangeProduct x E 0 = 1 := by
  simp [exchangeProduct]

@[simp]
theorem exchangeProduct_one (x E : G) : exchangeProduct x E 1 = E := by
  simp [exchangeProduct, mul_assoc]

/-- The ordered recurrence, with the next conjugated factor on the right. -/
theorem exchangeProduct_succ (x E : G) (n : ℕ) :
    exchangeProduct x E (n + 1) = exchangeProduct x E n * x⁻¹ ^ n * E * x ^ n := by
  unfold exchangeProduct
  rw [pow_succ (E * x⁻¹), pow_succ x]
  group

/-- The recurrence by inverse conjugation, useful for coefficient membership. -/
theorem exchangeProduct_succ' (x E : G) (n : ℕ) :
    exchangeProduct x E (n + 1) = E * (x⁻¹ * exchangeProduct x E n * x) := by
  unfold exchangeProduct
  group

/-- Length-`2` ordered exchange product: `exchangeProduct x E 2 = E * (x⁻¹ * E * x)`. -/
theorem exchangeProduct_two (x E : G) : exchangeProduct x E 2 = E * (x⁻¹ * E * x) := by
  rw [exchangeProduct_succ, exchangeProduct_one]
  simp [mul_assoc]

/-- Twisted cocycle law for `exchangeProduct` under addition of lengths. -/
theorem exchangeProduct_add (x E : G) (s t : ℕ) :
    exchangeProduct x E (s + t) =
      exchangeProduct x E s * ((x ^ s)⁻¹ * exchangeProduct x E t * x ^ s) := by
  simp only [exchangeProduct_def, pow_add]
  group

/-- Powers of an exchange have the ordered coefficient `exchangeProduct`. -/
theorem mul_inv_pow_eq_exchangeProduct_mul_inv_pow (x E : G) (n : ℕ) :
    (E * x⁻¹) ^ n = exchangeProduct x E n * x⁻¹ ^ n := by
  unfold exchangeProduct
  group

/-- Nonnegative integer powers of `E * x⁻¹` factor on the left through `exchangeProduct x E r`. -/
theorem mul_inv_zpow_natCast_eq_exchangeProduct_mul_zpow_neg (x E : G) (r : ℕ) :
    (E * x⁻¹) ^ (r : ℤ) = exchangeProduct x E r * x ^ (-(r : ℤ)) := by
  rw [zpow_natCast, mul_inv_pow_eq_exchangeProduct_mul_inv_pow, zpow_neg, zpow_natCast, inv_pow]

/-- Shifting `(E * x⁻¹) ^ (k - N)` on the right by `exchangeProduct x E N` yields
`exchangeProduct x E k * x ^ (N - k)`. -/
theorem mul_inv_zpow_sub_mul_exchangeProduct (x E : G) (k N : ℕ) :
    (E * x⁻¹) ^ ((k : ℤ) - (N : ℤ)) * exchangeProduct x E N =
      exchangeProduct x E k * x ^ ((N : ℤ) - (k : ℤ)) := by
  rw [exchangeProduct_def, exchangeProduct_def]
  group

/-- If `E` commutes with `x`, ordered exchange products are ordinary powers of `E`. -/
theorem exchangeProduct_eq_pow_of_commute {x E : G} (h : Commute x E) (n : ℕ) :
    exchangeProduct x E n = E ^ n := by
  rw [exchangeProduct_def, (h.symm.inv_right).mul_pow]
  simp [mul_assoc]

/-- Multiplicative maps transport the ordered exchange coefficients. -/
@[simp]
theorem map_exchangeProduct {H F : Type*} [Group H] [FunLike F G H]
    [MonoidHomClass F G H] (f : F) (x E : G) (n : ℕ) :
    f (exchangeProduct x E n) = exchangeProduct (f x) (f E) n := by
  simp [exchangeProduct_def]

end Group

/-- Ordered exchange products in a commutative group are ordinary powers. -/
@[simp]
theorem exchangeProduct_eq_pow {G : Type*} [CommGroup G] (x E : G) (n : ℕ) :
    exchangeProduct x E n = E ^ n :=
  exchangeProduct_eq_pow_of_commute (.all x E) n

end TauCeti

namespace TauCeti

variable {B S : Type*} [Monoid B] [SetLike S B] [SubmonoidClass S B] (C : S) (x E : Bˣ)

/-- Ordered exchange products remain in the coefficient submonoid if inverse
conjugation by the old coordinate preserves it. -/
theorem exchangeProduct_mem
    (hx : ∀ c ∈ C, (↑x⁻¹ : B) * c * x ∈ C) (hE : (E : B) ∈ C) (n : ℕ) :
    (↑(exchangeProduct x E n) : B) ∈ C := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [exchangeProduct_succ', Units.val_mul] using mul_mem hE (hx _ ih)

end TauCeti

namespace Subsemiring

/-- When `x` normalizes a subsemiring `C` under `ConjAct` and `(E : B) ∈ C`, every ordered exchange
product lies in `C`. -/
theorem coe_exchangeProduct_mem {B : Type*} [Semiring B] {C : Subsemiring B} {x E : Bˣ}
    (hx : ConjAct.toConjAct x • C = C) (hEC : (E : B) ∈ C) (r : ℕ) :
    ((TauCeti.exchangeProduct x E r : Bˣ) : B) ∈ C :=
  TauCeti.exchangeProduct_mem C x E
    (fun _ hc ↦ by simpa [zpow_neg_one] using conj_zpow_mem hx (-1) hc) hEC r

end Subsemiring

namespace TauCeti

variable {B S : Type*} [Semiring B] [SetLike S B] [SubsemiringClass S B] (C : S) (x E : Bˣ)

/-- Independence of natural powers of `x` implies independence of natural powers of
`E * x⁻¹`, with left coefficients in `C`. The numerator need only be a unit in the
ambient semiring. -/
theorem linearIndependent_mul_inv_pow
    (hx : ∀ c ∈ C, (↑x⁻¹ : B) * c * x ∈ C) (hE : (E : B) ∈ C)
    (hli : LinearIndependent C (fun n : ℕ ↦ (↑(x ^ n) : B))) :
    LinearIndependent C (fun n : ℕ ↦ (↑((E * x⁻¹) ^ n) : B)) := by
  classical
  let p (n : ℕ) : C := ⟨↑(exchangeProduct x E n),
    exchangeProduct_mem C x E hx hE n⟩
  have hp (n : ℕ) : IsRightRegular (p n) :=
    fun _ _ h ↦ Subtype.ext <| (exchangeProduct x E n).isRegular.right
      (congrArg ((↑) : C → B) h)
  have hi := ((Units.linearIndependent_zpow_iff x).mpr hli).comp (fun n : ℕ ↦ -(n : ℤ))
    (neg_injective.comp Nat.cast_injective)
  have hsmul (c : C) (b : B) : c • b = (c : B) * b := by
    rw [setLike_smul_def, smul_eq_mul]
  have hfactor : (p • ((fun n : ℤ ↦ (↑(x ^ n) : B)) ∘ fun n : ℕ ↦ -(n : ℤ))) =
      fun n : ℕ ↦ (↑((E * x⁻¹) ^ n) : B) := by
    funext n
    rw [mul_inv_pow_eq_exchangeProduct_mul_inv_pow]
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

end TauCeti
