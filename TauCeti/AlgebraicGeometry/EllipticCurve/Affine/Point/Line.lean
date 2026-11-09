/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.LinearCombination

/-!
# Three points on a line

Mathlib defines the sum of two affine points `P₁ = (x₁, y₁)` and `P₂ = (x₂, y₂)` of a Weierstrass
curve `W` through the third intersection of `W` with the line through `P₁` and `P₂`, computed
from the slope of that line. This file records the converse reading of that construction: if three
affine points with pairwise distinct `X`-coordinates lie on a common line `Y = μ X + ν`, then they
sum to zero. Substituting the line into the Weierstrass equation gives a cubic in `X` whose roots
are `x₁`, `x₂` and the `X`-coordinate of `-(P₁ + P₂)`
(`WeierstrassCurve.Affine.addPolynomial_slope`), and `x₃` is a root distinct from `x₁` and `x₂`.

This is the form in which the group law is recognised for a curve parametrised by other means,
such as the Tate curve, where collinearity of three parametrised points is known directly.

## Main results

* `WeierstrassCurve.Affine.Point.some_add_some_add_some_eq_zero`: three affine points with
  pairwise distinct `X`-coordinates on a line `Y = μ X + ν` sum to zero.
-/

public section

namespace WeierstrassCurve.Affine.Point

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

/-- **Three points on a line sum to zero.** If three affine points of a Weierstrass curve with
pairwise distinct `X`-coordinates lie on a common line `Y = μ X + ν`, their sum is zero. -/
theorem some_add_some_add_some_eq_zero {x₁ x₂ x₃ y₁ y₂ y₃ μ ν : F} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (h₃ : W.Nonsingular x₃ y₃) (hx₁₂ : x₁ ≠ x₂) (hx₁₃ : x₁ ≠ x₃)
    (hx₂₃ : x₂ ≠ x₃) (hy₁ : y₁ = μ * x₁ + ν) (hy₂ : y₂ = μ * x₂ + ν) (hy₃ : y₃ = μ * x₃ + ν) :
    some x₁ y₁ h₁ + some x₂ y₂ h₂ + some x₃ y₃ h₃ = 0 := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := fun h ↦ hx₁₂ h.1
  have hs : W.slope x₁ x₂ y₁ y₂ = μ := by
    rw [slope_of_X_ne hx₁₂, div_eq_iff (sub_ne_zero.mpr hx₁₂), hy₁, hy₂]
    ring
  -- `x₃` is a root of the cubic cut out on `W` by the line, other than `x₁` and `x₂`
  have hev : (W.addPolynomial x₁ y₁ μ).eval x₃ = 0 := by
    have e₃ := h₃.1
    rw [show y₃ = μ * (x₃ - x₁) + y₁ by rw [hy₃, hy₁]; ring, equation_iff] at e₃
    rw [addPolynomial, linePolynomial, polynomial]
    simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow]
    linear_combination e₃
  rw [← hs, addPolynomial_slope h₁.1 h₂.1 hxy, hs] at hev
  simp only [eval_neg, eval_mul, eval_sub, eval_X, eval_C, neg_eq_zero, mul_eq_zero,
    sub_eq_zero] at hev
  have hx₃ : x₃ = W.addX x₁ x₂ μ :=
    hev.resolve_left fun h ↦ h.elim (hx₁₃ ∘ Eq.symm) (hx₂₃ ∘ Eq.symm)
  rw [add_some hxy, ← neg_neg (some x₃ y₃ h₃), neg_some, add_neg_eq_zero, some.injEq]
  simp only [hs]
  refine ⟨hx₃.symm, ?_⟩
  rw [addY, negAddY, ← hx₃, hy₃, hy₁]
  congr 1
  ring

end WeierstrassCurve.Affine.Point

end
