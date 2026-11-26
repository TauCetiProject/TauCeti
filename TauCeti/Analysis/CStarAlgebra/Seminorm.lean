/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Suprema of C⋆-seminorms

Universal C⋆-norms, such as the full crossed-product norm and the norm of the universal
C⋆-algebra on unitary generators, are suprema `‖x‖ᵤ = sup ‖ρ x‖` over families of
⋆-homomorphisms `ρ` into C⋆-algebras. Each seminorm `x ↦ ‖ρ x‖` is submultiplicative,
star-invariant and satisfies the C⋆-identity, and these properties pass to the supremum of a
bounded-above family: `Seminorm.sSup_mul_le`, `Seminorm.sSup_star` and
`Seminorm.sSup_star_mul_self`.
-/

public section

namespace Seminorm

variable {𝕜 D : Type*} [NormedField 𝕜] [AddCommGroup D] [Module 𝕜 D]
  {S : Set (Seminorm 𝕜 D)}

/-- The supremum of a bounded-above set of seminorms is at most a nonnegative common bound of its
members. -/
theorem sSup_apply_le (hS : BddAbove S) {x : D} {c : ℝ} (hc : 0 ≤ c) (h : ∀ p ∈ S, p x ≤ c) :
    sSup S x ≤ c := by
  rw [Seminorm.sSup_apply hS]
  exact Real.iSup_le (fun p => h p p.property) hc

/-- The supremum of a bounded-above set of submultiplicative seminorms is submultiplicative. -/
theorem sSup_mul_le [Mul D] (hS : BddAbove S) (h : ∀ p ∈ S, ∀ x y, p (x * y) ≤ p x * p y)
    (x y : D) :
    sSup S (x * y) ≤ sSup S x * sSup S y :=
  sSup_apply_le hS (mul_nonneg (apply_nonneg _ x) (apply_nonneg _ y)) fun p hp =>
    (h p hp x y).trans (mul_le_mul (le_csSup hS hp x) (le_csSup hS hp y) (apply_nonneg _ y)
      (apply_nonneg _ x))

/-- The supremum of a bounded-above set of star-invariant seminorms is star-invariant. -/
theorem sSup_star [Star D] (hS : BddAbove S) (h : ∀ p ∈ S, ∀ x, p (star x) = p x) (x : D) :
    sSup S (star x) = sSup S x := by
  rw [Seminorm.sSup_apply hS, Seminorm.sSup_apply hS]
  exact iSup_congr fun p => h p p.property x

/-- The supremum of a bounded-above set of seminorms satisfying the C⋆-identity
`p (x⋆ * x) = p x * p x` satisfies it too. -/
theorem sSup_star_mul_self [Mul D] [Star D] (hS : BddAbove S)
    (h : ∀ p ∈ S, ∀ x, p (star x * x) = p x * p x) (x : D) :
    sSup S (star x * x) = sSup S x * sSup S x := by
  refine le_antisymm (sSup_apply_le hS (mul_self_nonneg _) fun p hp => (h p hp x).trans_le
    (mul_le_mul (le_csSup hS hp x) (le_csSup hS hp x) (apply_nonneg _ x) (apply_nonneg _ x))) ?_
  -- Each `p x` is the square root of `p (x⋆ * x) ≤ sSup S (x⋆ * x)`.
  have hsqrt : sSup S x ≤ √(sSup S (star x * x)) :=
    sSup_apply_le hS (Real.sqrt_nonneg _) fun p hp => Real.le_sqrt_of_sq_le <| by
      rw [sq, ← h p hp x]
      exact le_csSup hS hp _
  exact (mul_self_le_mul_self (apply_nonneg _ x) hsqrt).trans_eq
    (Real.mul_self_sqrt (apply_nonneg _ _))

end Seminorm
