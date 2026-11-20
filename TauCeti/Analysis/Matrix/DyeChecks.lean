/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Star.Prod
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Algebra.Star.StarProjection

/-!
# Finite projection symmetries

Transpose preserves orthogonality of complex matrix projections. In the
two-dimensional commutative algebra the idempotents are the four coordinate
projections, and swapping the coordinates preserves orthogonality.

Reference: Hamhalter, Dye’s theorem and Gleason’s theorem for AW*-algebras (2015),
Theorem 4.3, for the extension theorem illustrated by these examples.
-/

open scoped Matrix

public section

namespace IsStarProjection

/-- Transpose preserves orthogonality of complex matrix projections. -/
theorem matrix_mul_eq_zero_iff_transpose_mul_eq_zero {n : Type*} [Fintype n]
    {p q : Matrix n n ℂ} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p * q = 0 ↔ pᵀ * qᵀ = 0 := by
  constructor
  · intro h
    have h' : q * p = 0 := by
      have := congrArg star h
      simpa [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using this
    rw [← Matrix.transpose_mul, h', Matrix.transpose_zero]
  · intro h
    have h' : q * p = 0 := by
      have := congrArg Matrix.transpose h
      simpa [Matrix.transpose_mul, Matrix.transpose_zero] using this
    have := congrArg star h'
    simpa [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using this

end IsStarProjection

namespace Prod

/-- The idempotents of the product of two copies of the complex field are its four coordinate
projections. -/
theorem complex_mul_self_eq_self_iff (x : ℂ × ℂ) :
    x * x = x ↔ x = 0 ∨ x = (1, 0) ∨ x = (0, 1) ∨ x = 1 := by
  constructor
  · intro h
    obtain ⟨a, b⟩ := x
    have ha : a * a = a := congrArg Prod.fst h
    have hb : b * b = b := congrArg Prod.snd h
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp ha with rfl | rfl <;>
      rcases IsIdempotentElem.iff_eq_zero_or_one.mp hb with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl) <;> simp

end Prod

namespace TauCeti

/-- Swapping the two complex coordinates preserves products and orthogonality. -/
theorem exists_swap_starRingEquiv :
    ∃ φ : ℂ × ℂ ≃⋆+* ℂ × ℂ,
      (∀ x, φ x = (x.snd, x.fst)) ∧
        (∀ p q : ℂ × ℂ, p * q = 0 ↔ φ p * φ q = 0) ∧
          φ (1, 0) = (0, 1) ∧ φ (0, 1) = (1, 0) ∧ φ 0 = 0 ∧ φ 1 = 1 := by
  refine ⟨{ RingEquiv.prodComm with map_star' := ?_ }, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro p q
    change (p.fst * q.fst, p.snd * q.snd) = (0, 0) ↔
      (p.snd * q.snd, p.fst * q.fst) = (0, 0)
    constructor
    · intro h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · rfl
  · rfl
  · rfl
  · rfl

end TauCeti
