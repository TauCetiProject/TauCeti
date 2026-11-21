/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Shifted and scaled Jacobi sums

Mathlib's `jacobiSum χ ψ` is the Jacobi sum `J(χ, ψ) = ∑ x, χ x * ψ (1 - x)` of two
multiplicative characters of a finite commutative ring `F`. Mathlib also has its symmetry
(`jacobiSum_comm`) and its values in the trivial cases over a finite field (`jacobiSum_one_one`,
`jacobiSum_one_nontrivial` and `jacobiSum_nontrivial_inv`).

Point counts give the sum `∑ x, χ x * ψ (c - x)` with a general `c` in place of `1`. For a unit `c`
the substitution `x = c y` turns it into `(χ ψ)(c) J(χ, ψ)`. For `c = 0` it is
`ψ(-1) ∑ x, (χ ψ)(x)`, which is `χ(-1) #Fˣ` if `χ ψ = 1` and zero otherwise. For a finite field
`F` with `q` elements, `#Fˣ = q - 1` (Mathlib's `Fintype.card_units`).

## Main results

* `TauCeti.sum_mul_apply_sub_eq_mul_jacobiSum`: for a unit `c`,
  `∑ x, χ x ψ (c - x) = (χ ψ)(c) J(χ, ψ)`.
* `TauCeti.sum_mul_apply_sub_mul_eq_mul_jacobiSum`: for units `a` and `b`,
  `∑ x, χ x ψ (a - b x) = χ(b⁻¹) (χ ψ)(a) J(χ, ψ)`.
* `TauCeti.sum_mul_apply_neg_eq_ite`: `∑ x, χ x ψ (-x)` is `χ(-1) #Fˣ` if `χ ψ = 1` and zero
  otherwise.
-/

public section

open Finset

namespace TauCeti

variable {F R : Type*} [CommRing F] [Fintype F] [CommRing R]

/-- **The shifted Jacobi sum.** For a unit `c`, `∑ x, χ x ψ (c - x) = (χ ψ)(c) J(χ, ψ)`. -/
theorem sum_mul_apply_sub_eq_mul_jacobiSum (χ ψ : MulChar F R) (c : Fˣ) :
    ∑ x, χ x * ψ (c - x) = (χ * ψ) c * jacobiSum χ ψ := by
  rw [jacobiSum, mul_sum,
    ← Fintype.sum_bijective ((c : F) * ·) c.mulLeft_bijective _ _ fun _ ↦ rfl]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [show (c : F) - c * y = c * (1 - y) by ring, map_mul, map_mul, MulChar.coeToFun_mul,
    Pi.mul_apply]
  ring

/-- **The scaled Jacobi sum.** For units `a` and `b`,
`∑ x, χ x ψ (a - b x) = χ(b⁻¹) (χ ψ)(a) J(χ, ψ)`. -/
theorem sum_mul_apply_sub_mul_eq_mul_jacobiSum (χ ψ : MulChar F R) (a b : Fˣ) :
    ∑ x, χ x * ψ (a - b * x) = χ ↑b⁻¹ * ((χ * ψ) a * jacobiSum χ ψ) := by
  rw [← sum_mul_apply_sub_eq_mul_jacobiSum χ ψ a, mul_sum,
    ← Fintype.sum_bijective ((↑b⁻¹ : F) * ·) b⁻¹.mulLeft_bijective _ _ fun _ ↦ rfl]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [Units.mul_inv_cancel_left, map_mul, mul_assoc]

/-- **The Jacobi sum at `c = 0`.** The sum `∑ x, χ x ψ (-x)` is `χ(-1) #Fˣ` if `χ ψ = 1` and zero
otherwise. -/
theorem sum_mul_apply_neg_eq_ite [IsDomain R] (χ ψ : MulChar F R) [Decidable (χ * ψ = 1)] :
    ∑ x, χ x * ψ (-x) = if χ * ψ = 1 then χ (-1) * (Nat.card Fˣ : R) else 0 := by
  have h (x : F) : χ x * ψ (-x) = ψ (-1) * (χ * ψ) x := by
    rw [neg_eq_neg_one_mul x, map_mul, MulChar.coeToFun_mul, Pi.mul_apply]
    ring
  simp_rw [h, ← mul_sum]
  split_ifs with hχψ
  · classical
    rw [hχψ, MulChar.sum_one_eq_card_units, Nat.card_eq_fintype_card]
    -- `χ(-1) ψ(-1) = 1` and `ψ(-1) ^ 2 = 1` give `ψ(-1) = χ(-1)`.
    have h1 : χ (-1) * ψ (-1) = 1 := by
      rw [← Pi.mul_apply (f := ⇑χ), ← MulChar.coeToFun_mul, hχψ,
        MulChar.one_apply isUnit_one.neg]
    have h2 : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
    congr 1
    linear_combination (-ψ (-1)) * h1 + χ (-1) * h2
  · rw [MulChar.sum_eq_zero_of_ne_one hχψ, mul_zero]

end TauCeti
