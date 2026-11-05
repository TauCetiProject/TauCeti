/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.AddPolynomial

/-!
# Three points on a line

Let `W` be a Weierstrass curve over a field `F`. Three nonsingular affine points `P₁`, `P₂`, `P₃`
of `W` add to zero exactly when they are the three intersections, counted with multiplicity, of a
non-vertical line `y = ℓ x + ν` with `W`. That is, the points lie on the line, and substituting the
line into the Weierstrass polynomial gives `W(X, ℓ X + ν) = -(X - x₁) (X - x₂) (X - x₃)`
(`WeierstrassCurve.Affine.Point.some_add_some_add_some_eq_zero_iff`). This is the
chord-and-tangent description of the group law, stated for Mathlib's group of points, whose
addition is defined by explicit formulas instead. The multiplicity condition is what distinguishes
a tangent line: when two of the points coincide, the line must be tangent to `W` there.

When the three `x`-coordinates are pairwise distinct, the multiplicity condition is automatic,
so three points on a common non-vertical line add to zero
(`WeierstrassCurve.Affine.Point.some_add_some_add_some_eq_zero_of_X_ne`). This is the form in
which the group law is checked for points given by explicit parametrisations, where a line through
three points can be exhibited directly.

## Main results

* `WeierstrassCurve.Affine.Point.some_add_some_add_some_eq_zero_iff`: three affine points add to
  zero exactly when they are the intersections of a non-vertical line with `W`.
* `WeierstrassCurve.Affine.Point.some_add_some_add_some_eq_zero_of_X_ne`: three affine points with
  pairwise distinct `x`-coordinates on a common non-vertical line add to zero.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.
-/

public section

namespace WeierstrassCurve.Affine

open Polynomial

variable {F : Type*} [Field F] {W : Affine F} {x₁ x₂ x₃ y₁ y₂ y₃ ℓ ν : F}

namespace Point

variable [DecidableEq F]

/-- **Three points add to zero exactly when they are the intersections of a line with the curve.**
Three nonsingular affine points `(xᵢ, yᵢ)` of `W` add to zero if and only if they lie on a line
`y = ℓ x + ν` that meets `W` exactly in them, counted with multiplicity:
`W(X, ℓ X + ν) = -(X - x₁) (X - x₂) (X - x₃)`. -/
theorem some_add_some_add_some_eq_zero_iff (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (h₃ : W.Nonsingular x₃ y₃) :
    some _ _ h₁ + some _ _ h₂ + some _ _ h₃ = 0 ↔ ∃ ℓ ν : F,
      y₁ = ℓ * x₁ + ν ∧ y₂ = ℓ * x₂ + ν ∧ y₃ = ℓ * x₃ + ν ∧
        W.polynomial.eval (C ℓ * X + C ν) = -((X - C x₁) * (X - C x₂) * (X - C x₃)) := by
  constructor
  · intro h
    have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
      rintro ⟨hx, hy⟩
      rw [add_of_Y_eq hx hy, zero_add] at h
      exact some_ne_zero h₃ h
    rw [add_some hxy] at h
    obtain ⟨hx₃, hy₃⟩ := some.inj ((eq_neg_of_add_eq_zero_right h).trans (neg_some _))
    rw [addY, negY_negY] at hy₃
    set ℓ := W.slope x₁ x₂ y₁ y₂
    refine ⟨ℓ, y₁ - ℓ * x₁, by ring, Y_eq_slope_mul_add h₁.1 h₂.1 hxy,
      by rw [hy₃, negAddY, ← hx₃]; ring, ?_⟩
    rw [← addPolynomial_eq_eval (x₁ := x₁) (y₁ := y₁) (by ring), addPolynomial_slope h₁.1 h₂.1 hxy,
      hx₃]
  · rintro ⟨ℓ, ν, hy₁, hy₂, hy₃, hW⟩
    obtain ⟨hb, hc, -⟩ := coeffs_of_addPolynomial_eq ((addPolynomial_eq_eval hy₁).trans hW)
    -- When the first two points coincide, the line has the slope of the tangent there.
    have htangent (hx : x₁ = x₂) :
        ℓ * (2 * y₁ + W.a₁ * x₁ + W.a₃) = 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ := by
      subst hx
      linear_combination 2 * x₁ * hb - hc
    have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
      rintro ⟨hx, hy⟩
      have hY : 2 * y₁ + W.a₁ * x₁ + W.a₃ = 0 := by
        rw [negY, ← hx, hy₂, ← hx, ← hy₁] at hy
        linear_combination hy
      rcases ((nonsingular_iff' x₁ y₁).1 h₁).2 with hX | hY'
      · exact hX (by linear_combination htangent hx - ℓ * hY)
      · exact hY' hY
    have hℓ : W.slope x₁ x₂ y₁ y₂ = ℓ := by
      by_cases hx : x₁ = x₂
      · have hy : y₁ ≠ W.negY x₂ y₂ := fun hy ↦ hxy ⟨hx, hy⟩
        have hy' : y₁ ≠ W.negY x₁ y₁ := by
          rw [← hx, hy₂, ← hx, ← hy₁] at hy
          exact hy
        rw [slope_of_Y_ne hx hy, div_eq_iff (sub_ne_zero.2 hy'), negY]
        linear_combination -htangent hx
      · rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.2 hx), hy₁, hy₂]
        ring
    rw [add_some hxy]
    refine add_of_Y_eq (by rw [hℓ, addX]; linear_combination hb) ?_
    rw [addY, hℓ, hy₃]
    congr 1
    · rw [addX]
      linear_combination hb
    · rw [negAddY, addX, hy₁]
      linear_combination ℓ * hb

/-- **Three points on a line with distinct `x`-coordinates add to zero.** Three nonsingular
affine points `(xᵢ, yᵢ)` of `W` with pairwise distinct `x`-coordinates, lying on a common line
`y = ℓ x + ν`, add to zero. -/
theorem some_add_some_add_some_eq_zero_of_X_ne (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (h₃ : W.Nonsingular x₃ y₃) (hx₁₂ : x₁ ≠ x₂) (hx₁₃ : x₁ ≠ x₃)
    (hx₂₃ : x₂ ≠ x₃) (hy₁ : y₁ = ℓ * x₁ + ν) (hy₂ : y₂ = ℓ * x₂ + ν) (hy₃ : y₃ = ℓ * x₃ + ν) :
    some _ _ h₁ + some _ _ h₂ + some _ _ h₃ = 0 := by
  refine (some_add_some_add_some_eq_zero_iff h₁ h₂ h₃).2 ⟨ℓ, ν, hy₁, hy₂, hy₃, ?_⟩
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := fun h ↦ hx₁₂ h.1
  have hℓ : W.slope x₁ x₂ y₁ y₂ = ℓ := by
    rw [slope_of_X_ne hx₁₂, div_eq_iff (sub_ne_zero.2 hx₁₂), hy₁, hy₂]
    ring
  -- The cubic `W(X, ℓ X + ν)` vanishes at `x₃`, so `x₃` is its third root `addX x₁ x₂ ℓ`.
  have hsum : x₃ = W.addX x₁ x₂ ℓ := by
    have h := congrArg (eval x₃) (W.addPolynomial_slope h₁.1 h₂.1 hxy)
    rw [hℓ, addPolynomial_eq_eval hy₁, polynomial] at h
    simp only [eval_neg, eval_mul, eval_sub, eval_add, eval_pow, eval_C, eval_X] at h
    have e₃ := (equation_iff x₃ y₃).1 h₃.1
    rw [hy₃] at e₃
    have h' : (x₃ - x₁) * (x₃ - x₂) * (x₃ - W.addX x₁ x₂ ℓ) = 0 := by
      linear_combination h - e₃
    simpa [sub_eq_zero, hx₁₃.symm, hx₂₃.symm] using h'
  rw [← addPolynomial_eq_eval hy₁, ← hℓ, addPolynomial_slope h₁.1 h₂.1 hxy, hℓ, ← hsum]

end Point

end WeierstrassCurve.Affine
