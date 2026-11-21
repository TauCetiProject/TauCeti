/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import TauCeti.NumberTheory.MulChar.Basic

/-!
# Transport of Jacobi sums

Mathlib's `jacobiSum_ringHomComp` moves a Jacobi sum `J(χ, ψ) = ∑ x, χ x * ψ (1 - x)` along a
homomorphism of the coefficient ring. Here we also change the domain: if a ring isomorphism
`e : R ≃+* S` of finite rings and a coefficient homomorphism `f` carry `χ` to `χ'` and `ψ` to
`ψ'`, in the sense that `f (χ a) = χ' (e a)` and `f (ψ a) = ψ' (e a)`, then
`f (J(χ, ψ)) = J(χ', ψ')`. This is how a ring isomorphism of rings of integers acts on Jacobi
sums of characters of their residue fields, such as power residue symbols.

Point counts give the sum `∑ x, χ x * ψ (c - x)` with a general `c` in place of `1`. For a unit `c`
the substitution `x = c y` turns it into `(χ ψ)(c) J(χ, ψ)`. A unit factor `b` in `ψ (a - b x)`
comes out as `χ(b⁻¹)`, for every `a`. For `c = 0` the sum is `ψ(-1) ∑ x, (χ ψ)(x)`. If the
coefficient ring is a domain, this is `χ(-1) #Fˣ` if `χ ψ = 1` and zero otherwise; for a finite
field `F` with `q` elements, `#Fˣ = q - 1` (Mathlib's `Fintype.card_units`).

## Main results

* `TauCeti.map_jacobiSum`: transport of Jacobi sums along `e` and `f`.
* `MulChar.sum_mul_apply_sub_eq_mul_jacobiSum`: for a unit `c`,
  `∑ x, χ x ψ (c - x) = (χ ψ)(c) J(χ, ψ)`.
* `MulChar.sum_mul_apply_sub_mul_eq`: for a unit `b`,
  `∑ x, χ x ψ (a - b x) = χ(b⁻¹) ∑ x, χ x ψ (a - x)`.
* `MulChar.sum_mul_apply_sub_mul_eq_mul_jacobiSum`: for units `a` and `b`,
  `∑ x, χ x ψ (a - b x) = χ(b⁻¹) (χ ψ)(a) J(χ, ψ)`.
* `MulChar.sum_mul_apply_neg_eq_ite`: with values in a domain, `∑ x, χ x ψ (-x)` is `χ(-1) #Fˣ`
  if `χ ψ = 1` and zero otherwise.
-/

public section

namespace TauCeti

variable {R S R' R'' F : Type*} [CommRing R] [Fintype R] [CommRing S] [Fintype S] [CommRing R']
  [CommRing R''] [FunLike F R' R''] [RingHomClass F R' R'']

/-- **Transport of Jacobi sums.** If a ring isomorphism `e` of the domains and a homomorphism
`f` of the coefficients carry `χ` to `χ'` and `ψ` to `ψ'`, then `f (J(χ, ψ)) = J(χ', ψ')`. -/
theorem map_jacobiSum {f : F} {e : R ≃+* S} {χ ψ : MulChar R R'} {χ' ψ' : MulChar S R''}
    (hχ : ∀ a, f (χ a) = χ' (e a)) (hψ : ∀ a, f (ψ a) = ψ' (e a)) :
    f (jacobiSum χ ψ) = jacobiSum χ' ψ' := by
  simp only [jacobiSum, map_sum, map_mul, hχ, hψ, map_sub, map_one]
  exact e.toEquiv.sum_comp fun x => χ' x * ψ' (1 - x)

end TauCeti

namespace MulChar

open Finset

variable {F R : Type*} [CommRing F] [Fintype F] [CommRing R]

/-- **Scaling a shifted sum.** For a unit `b`, `∑ x, χ x ψ (a - b x) = χ(b⁻¹) ∑ x, χ x ψ (a - x)`,
by the substitution `x = b⁻¹ y`. -/
theorem sum_mul_apply_sub_mul_eq (χ ψ : MulChar F R) (a : F) (b : Fˣ) :
    ∑ x, χ x * ψ (a - b * x) = χ ↑b⁻¹ * ∑ x, χ x * ψ (a - x) := by
  rw [mul_sum, ← Fintype.sum_bijective ((↑b⁻¹ : F) * ·) b⁻¹.mulLeft_bijective _ _ fun _ ↦ rfl]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [Units.mul_inv_cancel_left, map_mul, mul_assoc]

/-- **The shifted Jacobi sum.** For a unit `c`, `∑ x, χ x ψ (c - x) = (χ ψ)(c) J(χ, ψ)`, by the
substitution `x = c y`. -/
theorem sum_mul_apply_sub_eq_mul_jacobiSum (χ ψ : MulChar F R) (c : Fˣ) :
    ∑ x, χ x * ψ (c - x) = (χ * ψ) c * jacobiSum χ ψ := by
  rw [jacobiSum, mul_sum,
    ← Fintype.sum_bijective ((c : F) * ·) c.mulLeft_bijective _ _ fun _ ↦ rfl]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [← mul_one_sub, map_mul, map_mul, mul_apply]
  ring

/-- **The scaled Jacobi sum.** For units `a` and `b`,
`∑ x, χ x ψ (a - b x) = χ(b⁻¹) (χ ψ)(a) J(χ, ψ)`. -/
theorem sum_mul_apply_sub_mul_eq_mul_jacobiSum (χ ψ : MulChar F R) (a b : Fˣ) :
    ∑ x, χ x * ψ (a - b * x) = χ ↑b⁻¹ * ((χ * ψ) a * jacobiSum χ ψ) := by
  rw [sum_mul_apply_sub_mul_eq, sum_mul_apply_sub_eq_mul_jacobiSum]

/-- **The Jacobi sum at `c = 0`.** With values in a domain, `∑ x, χ x ψ (-x)` is `χ(-1) #Fˣ` if
`χ ψ = 1` and zero otherwise. -/
theorem sum_mul_apply_neg_eq_ite [IsDomain R] (χ ψ : MulChar F R) [Decidable (χ * ψ = 1)] :
    ∑ x, χ x * ψ (-x) = if χ * ψ = 1 then χ (-1) * (Nat.card Fˣ : R) else 0 := by
  have h (x : F) : χ x * ψ (-x) = ψ (-1) * (χ * ψ) x := by
    rw [neg_eq_neg_one_mul x, map_mul, mul_apply]
    ring
  simp_rw [h, ← mul_sum]
  split_ifs with hχψ
  · classical
    rw [hχψ, sum_one_eq_card_units, Nat.card_eq_fintype_card]
    -- `χ(-1) ψ(-1) = 1` and `ψ(-1) ^ 2 = 1` give `ψ(-1) = χ(-1)`.
    have h1 : χ (-1) * ψ (-1) = 1 := by rw [← mul_apply, hχψ, one_apply isUnit_one.neg]
    congr 1
    linear_combination (-ψ (-1)) * h1 + χ (-1) * ψ.apply_neg_one_mul_self
  · rw [sum_eq_zero_of_ne_one hχψ, mul_zero]

end MulChar
