/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import TauCeti.NumberTheory.JacobiSum.Basic

/-!
# Sums over a finite field weighted by the quadratic character

Let `F` be a finite field of odd characteristic with quadratic character `χ`. For `a ≠ 0`, the
value `u = a t²` has `1 + χ(a u)` preimages `t`, by Mathlib's `quadraticChar_card_sqrts`. Hence a
sum over `t` of a function of `a t²` is a sum over `u` weighted by `1 + χ(a u)`. Similarly the
quadratic character sums to zero against any nonzero dilation, and the quadratic Jacobi sum
`∑ᵤ χ(u (c - u))` is evaluated through `MulChar.sum_mul_apply_neg_eq_ite` at `c = 0`, and through
`MulChar.sum_mul_apply_sub_eq_mul_jacobiSum` and Mathlib's `jacobiSum_nontrivial_inv` otherwise.

## Main results

* `TauCeti.sum_comp_mul_sq`: `∑ₜ g(a t²) = ∑ᵤ (1 + χ(a u)) • g(u)` for `a ≠ 0`.
* `TauCeti.sum_quadraticChar_mul`: `∑ᵤ χ(a u) = 0`.
* `TauCeti.sum_quadraticChar_mul_sub`: the quadratic Jacobi sum `∑ᵤ χ(u (c - u))`.
-/

public section

open Finset

namespace TauCeti

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Grouping a sum by squares**: for `a ≠ 0` in a finite field of odd characteristic, the value
`u = a t²` has `1 + χ(a u)` preimages `t`, so `∑ₜ g(a t²) = ∑ᵤ (1 + χ(a u)) • g(u)`. -/
theorem sum_comp_mul_sq {M : Type*} [AddCommGroup M] (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0)
    (g : F → M) : ∑ t : F, g (a * t ^ 2) = ∑ u : F, (1 + quadraticChar F (a * u)) • g u := by
  -- Group by `s = t²`, which has `χ s + 1` square roots, then substitute `u = a s`.
  have hfib : ∑ t : F, g (a * t ^ 2) = ∑ s : F, (quadraticChar F s + 1) • g (a * s) := by
    rw [← sum_fiberwise univ (fun t : F ↦ t ^ 2) (fun t ↦ g (a * t ^ 2))]
    refine sum_congr rfl fun s _ ↦ ?_
    rw [sum_congr rfl fun t ht ↦ by rw [(mem_filter.1 ht).2], sum_const,
      ← natCast_zsmul, ← quadraticChar_card_sqrts hF s, Set.toFinset_ofPred]
  rw [hfib]
  refine Fintype.sum_bijective (a * ·) (mulLeft_bijective₀ a ha) _ _ fun s ↦ ?_
  rw [← mul_assoc, ← sq, map_mul, quadraticChar_sq_one' ha, one_mul, add_comm (1 : ℤ)]

/-- The quadratic character sums to zero against any dilation. -/
theorem sum_quadraticChar_mul (hF : ringChar F ≠ 2) (a : F) :
    ∑ u : F, quadraticChar F (a * u) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rw [Fintype.sum_bijective (a * ·) (mulLeft_bijective₀ a ha) _ (quadraticChar F) fun _ ↦ rfl,
    quadraticChar_sum_zero hF]

/-- **The quadratic Jacobi sum**: in a finite field of odd characteristic, `∑ᵤ χ(u (c - u))` is
`χ(-1) (q - 1)` for `c = 0` and `-χ(-1)` otherwise. -/
theorem sum_quadraticChar_mul_sub (hF : ringChar F ≠ 2) (c : F) :
    ∑ u : F, quadraticChar F (u * (c - u)) =
      quadraticChar F (-1) * if c = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
  classical
  have hη := quadraticChar_isQuadratic F
  simp_rw [map_mul]
  split_ifs with hc
  · subst hc
    simp_rw [zero_sub]
    rw [MulChar.sum_mul_apply_neg_eq_ite, ite_eq_left (by rw [← sq, hη.sq_eq_one]),
      Nat.card_eq_fintype_card, Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  · -- With `c` a unit, the sum is `(χ χ)(c) J(χ, χ) = J(χ, χ⁻¹)`.
    have hJ := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
    rw [hη.inv] at hJ
    have := MulChar.sum_mul_apply_sub_eq_mul_jacobiSum (quadraticChar F) (quadraticChar F)
      (Units.mk0 c hc)
    rw [Units.val_mk0] at this
    rw [this, ← sq, hη.sq_eq_one, MulChar.one_apply (IsUnit.mk0 c hc), one_mul, hJ, mul_neg_one]

end TauCeti
