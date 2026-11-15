/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Data.ZMod.BinaryQuadraticForm
public import TauCeti.Data.ZMod.UnitSquare

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Cyclic vectors and hyperbolic plane complements over dyadic residues

The binary polynomial `θt²(2x+y)² + x² + xy + y²` admits hyperbolic
coordinates when `θt²` is a unit. For an odd integer coefficient `θ`, a unit
square supplies `u` with
`θu² + 4 = 5θ`, an inverse `t` with `θut = 1`, and coefficients expressing the
complement's quadratic polynomial as `mn`. These arithmetic results provide
coordinates for mixed dyadic plane and cyclic discriminant relations.

## Main declarations

* `ZMod.BinaryQuadraticForm.exists_hyperbolic_complement_of_isUnit`:
  hyperbolic coordinates for the restricted plane norm.
* `ZMod.BinaryQuadraticForm.exists_plane_cyclic_coefficients_of_odd`:
  rotation, inverse, and complement coordinates modulo every positive dyadic power.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(e), (f).
-/

public section

namespace ZMod.BinaryQuadraticForm

/-- Coordinates expressing `θt²(2x+y)² + x² + xy + y²` as the hyperbolic
polynomial `mn` when `θt²` is a unit. -/
theorem exists_hyperbolic_complement_of_isUnit (k : ℕ)
    {θ t : ZMod (2 ^ (k + 1))} (hq : IsUnit (θ * t ^ 2)) :
    ∃ a b c d : ZMod (2 ^ (k + 1)), ∀ m n,
      θ * (-t * (2 * (a * m + b * n) + (c * m + d * n))) ^ 2 +
        (a * m + b * n) ^ 2 + (a * m + b * n) * (c * m + d * n) +
        (c * m + d * n) ^ 2 = m * n := by
  obtain ⟨s, hs⟩ | ⟨s, hs⟩ := ZMod.eq_two_mul_or_eq_two_mul_add_one (θ * t ^ 2)
  · exact (ZMod.not_isUnit_two_mul s (hs ▸ hq)).elim
  · have hmid : IsUnit (1 + 4 * θ * t ^ 2) := by
      convert ZMod.isUnit_two_mul_add (c := 2 * θ * t ^ 2) isUnit_one using 1
      ring
    obtain ⟨e₁, e₂, f₁, f₂, h⟩ := ZMod.BinaryQuadraticForm.exists_hyperbolic_of_two_mul
      (s + 1) (1 + 4 * θ * t ^ 2) hmid
    refine ⟨e₂, f₂, e₁, f₁, fun m n ↦ ?_⟩
    linear_combination h m n + (e₁ * m + f₁ * n) ^ 2 * hs

/-- An odd integer coefficient admits a norm-five rotation coefficient, its inverse,
and coordinates that make its orthogonal dyadic plane complement hyperbolic. -/
theorem exists_plane_cyclic_coefficients_of_odd (k : ℕ) {θ : ℤ} (hθ : Odd θ) :
    ∃ u t a b c d : ZMod (2 ^ (k + 1)),
      (θ : ZMod (2 ^ (k + 1))) * u ^ 2 + 4 = 5 * θ ∧
      (θ : ZMod (2 ^ (k + 1))) * u * t = 1 ∧
      ∀ m n, (θ : ZMod (2 ^ (k + 1))) *
          (-t * (2 * (a * m + b * n) + (c * m + d * n))) ^ 2 +
        (a * m + b * n) ^ 2 + (a * m + b * n) * (c * m + d * n) +
        (c * m + d * n) ^ 2 = m * n := by
  have hunit : IsUnit (θ : ZMod (2 ^ (k + 1))) := by
    obtain ⟨s, rfl⟩ := hθ
    convert ZMod.isUnit_two_mul_add (c := (s : ZMod (2 ^ (k + 1)))) isUnit_one using 1
    push_cast
    ring
  obtain ⟨Θ, hΘ⟩ := hunit
  obtain ⟨U, hU⟩ := ZMod.exists_unit_sq_eq_five_sub_four_mul (k := k)
    (Units.isUnit Θ⁻¹)
  let t : ZMod (2 ^ (k + 1)) := ((Θ * U)⁻¹ : (ZMod (2 ^ (k + 1)))ˣ)
  have hinv : (θ : ZMod (2 ^ (k + 1))) * (U : ZMod (2 ^ (k + 1))) * t = 1 := by
    rw [← hΘ]
    exact Units.mul_inv (Θ * U)
  have hroot : (θ : ZMod (2 ^ (k + 1))) * (U : ZMod (2 ^ (k + 1))) ^ 2 + 4 = 5 * θ := by
    rw [hU, ← hΘ]
    have hcancel := Units.mul_inv Θ
    linear_combination -(4 : ZMod (2 ^ (k + 1))) * hcancel
  have hq : IsUnit ((θ : ZMod (2 ^ (k + 1))) * t ^ 2) := by
    rw [← hΘ]
    exact (Units.isUnit Θ).mul ((Units.isUnit (Θ * U)⁻¹).pow 2)
  obtain ⟨a, b, c, d, h⟩ := exists_hyperbolic_complement_of_isUnit k hq
  exact ⟨U, t, a, b, c, d, hroot, hinv, h⟩

end ZMod.BinaryQuadraticForm
