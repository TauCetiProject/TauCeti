/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Algebra.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Binary quadratic forms over rings of integers modulo a power of two

This file supplies the elementary normal form used for binary quadratic forms over
`ℤ/2^{k+1}` whose middle coefficient is a unit. Such a form is equivalent either to the
hyperbolic form `mn` or to the anisotropic form `m² + mn + n²`.

The key input is that, for a unit `u`, the map `s ↦ 2cs² + us` is a bijection. Its difference
quotient is `2c(s + t) + u`, which is a unit because `2` is nilpotent in `ℤ/2^{k+1}`.

## Main results

* `TauCeti.ZMod.bijective_two_mul_sq_add`: `s ↦ 2cs² + us` is bijective when `u` is a unit.
* `TauCeti.ZMod.BinaryQuadraticForm.exists_basis`: a binary form with unit middle coefficient
  has one of the two standard normal forms.
-/

public section

namespace TauCeti

namespace ZMod

variable {k : ℕ}

private theorem isNilpotent_two : IsNilpotent (2 : ZMod (2 ^ (k + 1))) :=
  ⟨k + 1, by exact_mod_cast ZMod.natCast_self (2 ^ (k + 1))⟩

/-- An even element plus a unit is a unit in `ℤ/2^{k+1}`. -/
theorem isUnit_two_mul_add {c u : ZMod (2 ^ (k + 1))} (hu : IsUnit u) :
    IsUnit (2 * c + u) :=
  ((Commute.all 2 c).isNilpotent_mul_right isNilpotent_two).isUnit_add_right_of_commute hu
    (Commute.all _ _)

/-- An even element of `ℤ/2^{k+1}` is not a unit. -/
private theorem not_isUnit_two_mul (c : ZMod (2 ^ (k + 1))) : ¬ IsUnit (2 * c) :=
  have : Nontrivial (ZMod (2 ^ (k + 1))) :=
    ZMod.nontrivial_iff.2 (Nat.one_lt_two_pow k.succ_ne_zero).ne'
  fun h ↦ h.not_isNilpotent ((Commute.all 2 c).isNilpotent_mul_right isNilpotent_two)

/-- Every element of `ℤ/2^{k+1}` is even or odd, according to the parity of an integer lift. -/
theorem eq_two_mul_or_eq_two_mul_add_one (x : ZMod (2 ^ (k + 1))) :
    (∃ c, x = 2 * c) ∨ ∃ c, x = 2 * c + 1 := by
  obtain ⟨X, rfl⟩ := ZMod.intCast_surjective x
  rcases Int.even_or_odd' X with ⟨c, rfl | rfl⟩
  · exact Or.inl ⟨c, by push_cast; ring⟩
  · exact Or.inr ⟨c, by push_cast; ring⟩

/-- For a unit `u`, the map `s ↦ 2cs² + us` is a bijection of `ℤ/2^{k+1}`. -/
theorem bijective_two_mul_sq_add {c u : ZMod (2 ^ (k + 1))} (hu : IsUnit u) :
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
  obtain ⟨m₀, hm₀⟩ := (bijective_two_mul_sq_add (c := a') hu).2 (-b)
  simp only at hm₀
  obtain ⟨v, hv⟩ := (isUnit_two_mul_add (c := 2 * a' * m₀) hu).exists_right_inv
  set t := -(v * (2 * a') * v)
  refine ⟨m₀, 1, v + t * m₀, t, fun m n ↦ ?_⟩
  linear_combination (m ^ 2 + n ^ 2 * t ^ 2 + 2 * m * n * t) * hm₀ +
    (m * n - n ^ 2 * v ^ 2 * (2 * a')) * hv

/-- **The anisotropic normal form.** For a unit `u`, the binary form
`(2a' + 1)m² + umn + (2b' + 1)n²` over `ℤ/2^{k+1}` becomes `m² + mn + n²` in a suitable
basis. -/
private theorem exists_sq_add_mul_add_sq_of_odd (a' b' : ZMod (2 ^ (k + 1)))
    {u : ZMod (2 ^ (k + 1))} (hu : IsUnit u) :
    ∃ e₁ e₂ f₁ f₂ : ZMod (2 ^ (k + 1)), ∀ m n,
      (2 * a' + 1) * (m * e₁ + n * f₁) ^ 2 +
          u * (m * e₁ + n * f₁) * (m * e₂ + n * f₂) +
        (2 * b' + 1) * (m * e₂ + n * f₂) ^ 2 = m ^ 2 + m * n + n ^ 2 := by
  set a := 2 * a' + 1
  obtain ⟨j, hj⟩ := (bijective_two_mul_sq_add (c := a) hu).2 (-b')
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
  obtain ⟨s, hs⟩ := (bijective_two_mul_sq_add (c := 1) isUnit_one.neg).2 (-(r * z))
  simp only at hs
  set t := 2 * s
  set s₀ := (1 - 2 * t) * (2 * v' + 1)
  refine ⟨2 * j, 1, s₀ + 2 * j * t, t, fun m n ↦ ?_⟩
  linear_combination (2 * m ^ 2 + 2 * n ^ 2 * t ^ 2 + 4 * m * n * t) * hj +
    (n ^ 2 * (1 - 2 * t) * t + m * n * (1 - 2 * t)) * hv +
    2 * n ^ 2 * (4 * c - 1) * hs - 2 * n ^ 2 * r * hz

/-- **Normal forms of binary forms with unit middle coefficient over `ℤ/2^{k+1}`.** The form
`am² + umn + bn²` becomes `mn` in some basis, or `m² + mn + n²` in some basis. -/
theorem exists_basis (a b : ZMod (2 ^ (k + 1))) {u : ZMod (2 ^ (k + 1))}
    (hu : IsUnit u) :
    ∃ e₁ e₂ f₁ f₂ : ZMod (2 ^ (k + 1)),
      (∀ m n, a * (m * e₁ + n * f₁) ^ 2 + u * (m * e₁ + n * f₁) * (m * e₂ + n * f₂) +
        b * (m * e₂ + n * f₂) ^ 2 = m * n) ∨
      (∀ m n, a * (m * e₁ + n * f₁) ^ 2 + u * (m * e₁ + n * f₁) * (m * e₂ + n * f₂) +
        b * (m * e₂ + n * f₂) ^ 2 = m ^ 2 + m * n + n ^ 2) := by
  obtain ⟨a', rfl⟩ | ⟨a', rfl⟩ := eq_two_mul_or_eq_two_mul_add_one a
  · obtain ⟨e₁, e₂, f₁, f₂, h⟩ := exists_hyperbolic_of_two_mul a' b hu
    exact ⟨e₁, e₂, f₁, f₂, Or.inl h⟩
  obtain ⟨b', rfl⟩ | ⟨b', rfl⟩ := eq_two_mul_or_eq_two_mul_add_one b
  · -- Even `b`: exchange the two coordinates.
    obtain ⟨e₁, e₂, f₁, f₂, h⟩ := exists_hyperbolic_of_two_mul b' (2 * a' + 1) hu
    exact ⟨e₂, e₁, f₂, f₁, Or.inl fun m n ↦ by linear_combination h m n⟩
  · obtain ⟨e₁, e₂, f₁, f₂, h⟩ := exists_sq_add_mul_add_sq_of_odd a' b' hu
    exact ⟨e₁, e₂, f₁, f₂, Or.inr h⟩

end BinaryQuadraticForm

end ZMod

end TauCeti
