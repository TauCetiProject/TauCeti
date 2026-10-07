/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic.Algebra.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.Data.ZMod.Two

/-!
# Binary quadratic forms over rings of integers modulo a power of two

This file supplies the elementary normal form used for binary quadratic forms over
`ℤ/2^{k+1}` whose middle coefficient is a unit. Such a form is equivalent either to the
hyperbolic form `mn` or to the form `m² + mn + n²`, by an invertible change of coordinates.

The key input is that, for a unit `u`, the map `s ↦ 2cs² + us` is a bijection. Its difference
quotient is `2c(s + t) + u`, which is a unit because `2` is nilpotent in `ℤ/2^{k+1}`.

## Main results

* `ZMod.two_mul_sq_add_bijective`: `s ↦ 2cs² + us` is bijective when `u` is a unit.
* `ZMod.BinaryQuadraticForm.exists_basis`: a binary form with unit middle coefficient
  has one of the two standard normal forms in a basis of `(ℤ/2^{k+1})²`.
-/

public section

namespace ZMod

variable {k : ℕ}

/-- For a unit `u`, the map `s ↦ 2cs² + us` is a bijection of `ℤ/2^{k+1}`. -/
theorem two_mul_sq_add_bijective {c u : ZMod (2 ^ (k + 1))} (hu : IsUnit u) :
    Function.Bijective fun s : ZMod (2 ^ (k + 1)) ↦ 2 * c * s ^ 2 + u * s := by
  refine Finite.injective_iff_bijective.1 fun s t hst ↦ ?_
  have h : (s - t) * (2 * (c * (s + t)) + u) = 0 := by
    linear_combination hst
  exact sub_eq_zero.1 ((isUnit_two_mul_add hu).mul_left_eq_zero.1 h)

namespace BinaryQuadraticForm

/-- **The hyperbolic normal form.** For a unit `u`, the binary form `2a'm² + umn + bn²` over
`ℤ/2^{k+1}` becomes `mn` in a suitable basis. -/
private theorem exists_hyperbolic_of_two_mul (a' b : ZMod (2 ^ (k + 1)))
    {u : ZMod (2 ^ (k + 1))} (hu : IsUnit u) :
    ∃ e₁ e₂ f₁ f₂ : ZMod (2 ^ (k + 1)), ∀ m n,
      2 * a' * (m * e₁ + n * f₁) ^ 2 + u * (m * e₁ + n * f₁) * (m * e₂ + n * f₂) +
        b * (m * e₂ + n * f₂) ^ 2 = m * n := by
  obtain ⟨m₀, hm₀⟩ := (two_mul_sq_add_bijective (c := a') hu).2 (-b)
  simp only at hm₀
  obtain ⟨v, hv⟩ := (isUnit_two_mul_add (c := 2 * a' * m₀) hu).exists_right_inv
  set t := -(v * (2 * a') * v)
  refine ⟨m₀, 1, v + t * m₀, t, fun m n ↦ ?_⟩
  linear_combination (m ^ 2 + n ^ 2 * t ^ 2 + 2 * m * n * t) * hm₀ +
    (m * n - n ^ 2 * v ^ 2 * (2 * a')) * hv

/-- **The odd normal form.** For a unit `u`, the binary form
`(2a' + 1)m² + umn + (2b' + 1)n²` over `ℤ/2^{k+1}` becomes `m² + mn + n²` in a suitable
basis. -/
private theorem exists_sq_add_mul_add_sq_of_odd (a' b' : ZMod (2 ^ (k + 1)))
    {u : ZMod (2 ^ (k + 1))} (hu : IsUnit u) :
    ∃ e₁ e₂ f₁ f₂ : ZMod (2 ^ (k + 1)), ∀ m n,
      (2 * a' + 1) * (m * e₁ + n * f₁) ^ 2 +
          u * (m * e₁ + n * f₁) * (m * e₂ + n * f₂) +
        (2 * b' + 1) * (m * e₂ + n * f₂) ^ 2 = m ^ 2 + m * n + n ^ 2 := by
  set a := 2 * a' + 1
  obtain ⟨j, hj⟩ := (two_mul_sq_add_bijective (c := a) hu).2 (-b')
  simp only at hj
  obtain ⟨v, hv⟩ := (isUnit_two_mul_add (c := 2 * a * j) hu).exists_right_inv
  -- `v` is a unit, hence odd.
  obtain ⟨v', rfl⟩ | ⟨v', rfl⟩ := eq_two_mul_or_eq_two_mul_add_one v
  · exact absurd (IsUnit.of_mul_eq_one (1 : ZMod (2 ^ (k + 1))) (by linear_combination hv))
      (not_isUnit_two_mul ((2 * (2 * a * j) + u) * v'))
  -- `c - 1 = 2r`, and `z` inverts `4c - 1`.
  set c := a * (2 * v' + 1) ^ 2
  set r := a' * (2 * v' + 1) ^ 2 + 2 * v' ^ 2 + 2 * v'
  obtain ⟨z, hz⟩ := (isUnit_two_mul_add (c := 2 * c) isUnit_one.neg).exists_right_inv
  obtain ⟨s, hs⟩ := (two_mul_sq_add_bijective (c := 1) isUnit_one.neg).2 (-(r * z))
  simp only at hs
  set t := 2 * s
  set s₀ := (1 - 2 * t) * (2 * v' + 1)
  refine ⟨2 * j, 1, s₀ + 2 * j * t, t, fun m n ↦ ?_⟩
  linear_combination (2 * m ^ 2 + 2 * n ^ 2 * t ^ 2 + 4 * m * n * t) * hj +
    (n ^ 2 * (1 - 2 * t) * t + m * n * (1 - 2 * t)) * hv +
    2 * n ^ 2 * (4 * c - 1) * hs - 2 * n ^ 2 * r * hz

/-- If the binary form `am² + umn + bn²` becomes `Am² + Cmn + Bn²` under the
coordinate change with matrix `!![e₁, f₁; e₂, f₂]`, and `4AB - C²` is a unit, then that matrix
has unit determinant: the discriminants satisfy `4AB - C² = (e₁f₂ - f₁e₂)² (4ab - u²)`. -/
private theorem isUnit_det_of_forall {a b u e₁ e₂ f₁ f₂ A B C : ZMod (2 ^ (k + 1))}
    (hdisc : IsUnit (4 * A * B - C ^ 2))
    (h : ∀ m n, a * (m * e₁ + n * f₁) ^ 2 + u * (m * e₁ + n * f₁) * (m * e₂ + n * f₂) +
      b * (m * e₂ + n * f₂) ^ 2 = A * m ^ 2 + C * m * n + B * n ^ 2) :
    IsUnit (e₁ * f₂ - f₁ * e₂) := by
  have hdet : (e₁ * f₂ - f₁ * e₂) ^ 2 * (4 * a * b - u ^ 2) = 4 * A * B - C ^ 2 := by
    linear_combination 4 * (a * e₁ ^ 2 + u * e₁ * e₂ + b * e₂ ^ 2) * h 0 1 + 4 * B * h 1 0 -
      (2 * a * e₁ * f₁ + u * (e₁ * f₂ + f₁ * e₂) + 2 * b * e₂ * f₂ + C) *
        (h 1 1 - h 1 0 - h 0 1)
  rw [← hdet] at hdisc
  exact (isUnit_pow_iff two_ne_zero).1 (isUnit_of_mul_isUnit_left hdisc)

/-- **Normal forms of binary forms with unit middle coefficient over `ℤ/2^{k+1}`.** There is a
change of coordinates `(m, n) ↦ (me₁ + nf₁, me₂ + nf₂)` with unit determinant `e₁f₂ - f₁e₂`
under which the form `am² + umn + bn²` becomes `mn` or `m² + mn + n²`. -/
theorem exists_basis (a b : ZMod (2 ^ (k + 1))) {u : ZMod (2 ^ (k + 1))}
    (hu : IsUnit u) :
    ∃ e₁ e₂ f₁ f₂ : ZMod (2 ^ (k + 1)), IsUnit (e₁ * f₂ - f₁ * e₂) ∧
      ((∀ m n, a * (m * e₁ + n * f₁) ^ 2 + u * (m * e₁ + n * f₁) * (m * e₂ + n * f₂) +
        b * (m * e₂ + n * f₂) ^ 2 = m * n) ∨
      (∀ m n, a * (m * e₁ + n * f₁) ^ 2 + u * (m * e₁ + n * f₁) * (m * e₂ + n * f₂) +
        b * (m * e₂ + n * f₂) ^ 2 = m ^ 2 + m * n + n ^ 2)) := by
  have hU {a b e₁ e₂ f₁ f₂ : ZMod (2 ^ (k + 1))}
      (h : ∀ m n, a * (m * e₁ + n * f₁) ^ 2 + u * (m * e₁ + n * f₁) * (m * e₂ + n * f₂) +
        b * (m * e₂ + n * f₂) ^ 2 = m * n) :
      IsUnit (e₁ * f₂ - f₁ * e₂) :=
    isUnit_det_of_forall (a := a) (b := b) (u := u) (A := 0) (B := 0) (C := 1) (by simp)
      fun m n ↦ by linear_combination h m n
  have hV {a b e₁ e₂ f₁ f₂ : ZMod (2 ^ (k + 1))}
      (h : ∀ m n, a * (m * e₁ + n * f₁) ^ 2 + u * (m * e₁ + n * f₁) * (m * e₂ + n * f₂) +
        b * (m * e₂ + n * f₂) ^ 2 = m ^ 2 + m * n + n ^ 2) :
      IsUnit (e₁ * f₂ - f₁ * e₂) :=
    isUnit_det_of_forall (a := a) (b := b) (u := u) (A := 1) (B := 1) (C := 1)
      (by convert isUnit_two_mul_add (c := 1) isUnit_one using 1; ring)
      fun m n ↦ by linear_combination h m n
  obtain ⟨a', rfl⟩ | ⟨a', rfl⟩ := eq_two_mul_or_eq_two_mul_add_one a
  · obtain ⟨e₁, e₂, f₁, f₂, h⟩ := exists_hyperbolic_of_two_mul a' b hu
    exact ⟨e₁, e₂, f₁, f₂, hU h, Or.inl h⟩
  obtain ⟨b', rfl⟩ | ⟨b', rfl⟩ := eq_two_mul_or_eq_two_mul_add_one b
  · -- Even `b`: exchange the two coordinates.
    obtain ⟨e₁, e₂, f₁, f₂, h⟩ := exists_hyperbolic_of_two_mul b' (2 * a' + 1) hu
    have h' : ∀ m n, (2 * a' + 1) * (m * e₂ + n * f₂) ^ 2 +
        u * (m * e₂ + n * f₂) * (m * e₁ + n * f₁) + 2 * b' * (m * e₁ + n * f₁) ^ 2 = m * n :=
      fun m n ↦ by linear_combination h m n
    exact ⟨e₂, e₁, f₂, f₁, hU h', Or.inl h'⟩
  · obtain ⟨e₁, e₂, f₁, f₂, h⟩ := exists_sq_add_mul_add_sq_of_odd a' b' hu
    exact ⟨e₁, e₂, f₁, f₂, hV h, Or.inr h⟩

end BinaryQuadraticForm

end ZMod
