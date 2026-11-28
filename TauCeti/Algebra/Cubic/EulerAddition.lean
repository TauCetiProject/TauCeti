/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Derivation.Basic

import Mathlib.Tactic.Ring

/-!
# Euler's algebraic addition formula on the cubic `y² + a x y = x³ + x`

This file defines Euler's algebraic formula for the `y`-coordinate of the sum of two points
`(x₀, y₀)` and `(x₁, y₁)` on the cubic `y² + a x y = x³ + x` with origin `(0, 0)`, where `u`
represents `(1 - x₀ x₁)⁻¹`. It proves its zero-left normalization, symmetry, subring closure, and
invariance under any derivation acting along the invariant vector field
`(2 y + a x, 1 + 3 x² - a y)` in opposite directions on the two points.

## Main definitions and results

* `TauCeti.eulerAddition`: Euler's addition formula in an arbitrary commutative ring `A`.
* `TauCeti.eulerAddition_def`: defining polynomial expression for `TauCeti.eulerAddition`.
* `TauCeti.eulerAddition_zero_left`: `eulerAddition a 0 0 x₁ y₁ u = y₁`.
* `TauCeti.eulerAddition_comm`: `eulerAddition a x₁ y₁ x₀ y₀ u = eulerAddition a x₀ y₀ x₁ y₁ u`.
* `TauCeti.eulerAddition_mem`: any subring containing `a, x₀, y₀, x₁, y₁, u` contains
  `eulerAddition a x₀ y₀ x₁ y₁ u`.
* `Derivation.eulerAddition_eq_zero`: any `R`-derivation `D` with `D a = 0` moving `(x₀, y₀)` and
  `(x₁, y₁)` along the invariant vector field in opposite directions kills `eulerAddition`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/Lib/CM/Integrality/LogTheta.lean`
(`New.eulerAddition`, `New.eulerAddition_mem`, `New.derivation_eulerAddition`).
-/

public section

section AdditionFormula

variable {A : Type*} [CommRing A] (a x₀ y₀ x₁ y₁ u : A)

namespace TauCeti

/-- Euler's formula for the `y`-coordinate of the sum of two points `(x₀, y₀)` and `(x₁, y₁)` on
the cubic `y² + a x y = x³ + x` with origin `(0, 0)`; here `u` stands for `1 / (1 - x₀ x₁)`.
In this form the value at `x₀ = y₀ = 0` is `y₁` for every `u`. -/
def eulerAddition : A :=
  (1 + x₀ * x₁ * u) ^ 2 * ((1 + x₀ * x₁) * (y₀ + y₁) - a * (y₀ * y₁)) +
    u ^ 3 * ((3 + x₀ * x₁) * (x₀ + x₁) + a ^ 2 * (x₀ * x₁)) * (x₀ * y₁ + x₁ * y₀ + a * (x₀ * x₁))

/-- Defining polynomial expression for `TauCeti.eulerAddition`. -/
theorem eulerAddition_def :
    eulerAddition a x₀ y₀ x₁ y₁ u =
      (1 + x₀ * x₁ * u) ^ 2 * ((1 + x₀ * x₁) * (y₀ + y₁) - a * (y₀ * y₁)) +
        u ^ 3 * ((3 + x₀ * x₁) * (x₀ + x₁) + a ^ 2 * (x₀ * x₁)) *
          (x₀ * y₁ + x₁ * y₀ + a * (x₀ * x₁)) := by
  rfl

/-- At the origin `x₀ = y₀ = 0`, Euler's addition formula reduces to `y₁` for every `u`. -/
@[simp]
theorem eulerAddition_zero_left : eulerAddition a 0 0 x₁ y₁ u = y₁ := by
  simp [eulerAddition]

/-- Euler's addition formula is symmetric in the two points `(x₀, y₀)` and `(x₁, y₁)`. -/
theorem eulerAddition_comm :
    eulerAddition a x₁ y₁ x₀ y₀ u = eulerAddition a x₀ y₀ x₁ y₁ u := by
  unfold eulerAddition
  ring

variable {a x₀ y₀ x₁ y₁ u}

/-- A subring that contains `a`, the coordinates `x₀`, `y₀`, `x₁`, `y₁`, and `u` contains the value
of Euler's formula at them. -/
theorem eulerAddition_mem {S : Subring A} (ha : a ∈ S) (hx₀ : x₀ ∈ S) (hy₀ : y₀ ∈ S)
    (hx₁ : x₁ ∈ S) (hy₁ : y₁ ∈ S) (hu : u ∈ S) : eulerAddition a x₀ y₀ x₁ y₁ u ∈ S := by
  unfold eulerAddition
  repeat' apply_rules [add_mem, sub_mem, mul_mem, pow_mem, one_mem, ofNat_mem]

end TauCeti

variable {a x₀ y₀ x₁ y₁ u}

/-- Euler's formula is constant when the two points move on the cubic `y² + a x y = x³ + x` in
opposite directions along the invariant vector field `x' = 2 y + a x`, `y' = 1 + 3 x² - a y`:
a derivation `D` with `D a = 0` acting in this way kills `TauCeti.eulerAddition`, provided
`u * (1 - x₀ * x₁) = 1`. -/
theorem Derivation.eulerAddition_eq_zero {R : Type*} [CommRing R] [Algebra R A]
    (D : Derivation R A A)
    (h₀ : y₀ ^ 2 + a * x₀ * y₀ = x₀ ^ 3 + x₀) (h₁ : y₁ ^ 2 + a * x₁ * y₁ = x₁ ^ 3 + x₁)
    (hu : u * (1 - x₀ * x₁) = 1) (ha : D a = 0)
    (hx₀ : D x₀ = 2 * y₀ + a * x₀) (hy₀ : D y₀ = 1 + 3 * x₀ ^ 2 - a * y₀)
    (hx₁ : D x₁ = -(2 * y₁ + a * x₁)) (hy₁ : D y₁ = -(1 + 3 * x₁ ^ 2 - a * y₁)) :
    D (TauCeti.eulerAddition a x₀ y₀ x₁ y₁ u) = 0 := by
  have h3 : D 3 = 0 := D.map_natCast 3
  simp only [TauCeti.eulerAddition_def, map_add, map_sub, D.leibniz, D.leibniz_pow,
    D.map_one_eq_zero, h3, D.leibniz_of_mul_eq_one hu, ha, hx₀, hy₀, hx₁, hy₁,
    smul_eq_mul, nsmul_eq_mul]
  grind

end AdditionFormula
