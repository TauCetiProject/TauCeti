/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.FieldTheory.IsSepClosed
-- Proof-only: a quadratic with nonvanishing derivative has a root in a separably closed field.
import TauCeti.FieldTheory.IsSepClosed

/-!
# Which `x`-coordinates of a Weierstrass curve are attained over a separably closed field

Fixing `x = a` in the Weierstrass equation leaves the monic quadratic
`Y² + (a₁a + a₃)Y − (a³ + a₂a² + a₄a + a₆)` in `Y`, whose derivative is `2Y + (a₁a + a₃)`. A
separably closed field has a root of it unless that derivative vanishes identically, which happens
only in characteristic `2` at an `a` with `a₁a + a₃ = 0`. So `a` is the `x`-coordinate of a
solution away from that case, and a solution whose `x`-coordinate is already rational has a
rational `y`-coordinate too: the two roots of a monic quadratic sum to minus its linear
coefficient, so one of them is rational as soon as the other is.

The excluded case is real. Over the separable closure of `𝔽₂(t)` the equation `y² + y = x³ + t`
has `a₁a + a₃ = 1`, but `y² = x³ + t` — where `a₁ = a₃ = 0` — has `y = √(a³ + t)`, which is purely
inseparable over the base field and need not lie in it. Both statements are about
`Affine.Equation` alone: no nonsingularity and no ellipticity is involved.

The two results are the separably closed companions of `exists_point_on_curve` and
`mem_range_y_of_equation_of_mem_range_x`, which need no side condition because an algebraically
closed field also extracts the inseparable square root.

## Main results

* `WeierstrassCurve.Affine.exists_point_on_curve_of_isSepClosed`: over a separably closed field,
  an element at which the quadratic in `y` is separable is the `x`-coordinate of a solution of
  `W.Equation`.
* `WeierstrassCurve.mem_range_y_of_equation_of_mem_range_x_of_exists_point`: over any field, a
  solution whose `x`-coordinate is rational has rational `y`-coordinate as soon as the equation
  at that `x` has one rational solution.
* `WeierstrassCurve.mem_range_y_of_equation_of_mem_range_x_of_isSepClosed`: such a solution over an
  extension, with `x`-coordinate in the image of the base field, has its `y`-coordinate there too.
-/

public section

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] [IsSepClosed F] (W : Affine F)

/-- **Over a separably closed field an `x`-coordinate is realised by a point** as soon as the
quadratic in `y` it leaves behind is separable, which is the hypothesis `2 ≠ 0 ∨ a₁a + a₃ ≠ 0`.
In characteristic `2` at an `a` with `a₁a + a₃ = 0` the equation reads `y² = a³ + a₂a² + a₄a + a₆`,
whose solution is purely inseparable over the base field and need not lie in it. -/
theorem exists_point_on_curve_of_isSepClosed (a : F) (h : (2 : F) ≠ 0 ∨ W.a₁ * a + W.a₃ ≠ 0) :
    ∃ b : F, W.Equation a b := by
  obtain ⟨b, hb⟩ := TauCeti.exists_quadratic_eq_zero_of_isSepClosed (one_ne_zero (α := F))
    (W.a₁ * a + W.a₃) (-(a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆)) h
  exact ⟨b, (W.equation_iff a b).mpr (by linear_combination hb)⟩

end Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F)
  {Ω : Type*} [Field Ω] [Algebra F Ω] {x y : Ω}

/-- **The `y`-coordinate of a point with rational `x` is rational** whenever the Weierstrass
equation at that `x` has one rational solution: the two roots of the resulting monic quadratic
sum to minus its linear coefficient, so the other one is rational as well. -/
theorem mem_range_y_of_equation_of_mem_range_x_of_exists_point
    (heq : (W.baseChange Ω).toAffine.Equation x y) {x₀ : F} (hx : algebraMap F Ω x₀ = x)
    (hex : ∃ y₀ : F, W.toAffine.Equation x₀ y₀) :
    y ∈ Set.range (algebraMap F Ω) := by
  subst hx
  obtain ⟨y₀, hy₀⟩ := hex
  rw [Affine.equation_iff] at heq hy₀
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
  have hy₀' := congrArg (algebraMap F Ω) hy₀
  simp only [map_add, map_mul, map_pow] at hy₀'
  -- The two roots of the quadratic in `y`, one of which is the image of `y₀`.
  have hroots : (y - algebraMap F Ω y₀) *
      (y + algebraMap F Ω y₀ + (algebraMap F Ω W.a₁ * algebraMap F Ω x₀ + algebraMap F Ω W.a₃))
        = 0 := by linear_combination heq - hy₀'
  rcases mul_eq_zero.mp hroots with hk | hk
  · exact ⟨y₀, by linear_combination -hk⟩
  · refine ⟨-y₀ - W.a₁ * x₀ - W.a₃, ?_⟩
    simp only [map_sub, map_neg, map_mul]
    linear_combination -hk

/-- **The `y`-coordinate of a point with rational `x` is rational** over a separably closed field,
under the same separability side condition as `Affine.exists_point_on_curve_of_isSepClosed`. -/
theorem mem_range_y_of_equation_of_mem_range_x_of_isSepClosed [IsSepClosed F]
    (heq : (W.baseChange Ω).toAffine.Equation x y) {x₀ : F} (hx : algebraMap F Ω x₀ = x)
    (h : (2 : F) ≠ 0 ∨ W.a₁ * x₀ + W.a₃ ≠ 0) :
    y ∈ Set.range (algebraMap F Ω) :=
  W.mem_range_y_of_equation_of_mem_range_x_of_exists_point heq hx
    (W.toAffine.exists_point_on_curve_of_isSepClosed x₀ h)

end WeierstrassCurve

end
