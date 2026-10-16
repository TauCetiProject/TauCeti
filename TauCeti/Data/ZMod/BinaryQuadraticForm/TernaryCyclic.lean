/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Data.ZMod.BinaryQuadraticForm
public import Mathlib.Data.Int.ModEq

import TauCeti.Data.ZMod.Two
import TauCeti.Data.ZMod.Units
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Binary complements in dyadic ternary cyclic norms

For odd coefficients `θ, θ, η`, this file constructs coordinates of the form
`(X, Y, -r(X+Y))`, where `ηr = θ`. Their pairing with `(1,1,1)` vanishes, and
their diagonal ternary norm equals either `2(m² + mn + n²)` or `2mn`.
The mod-four relation between `θ` and `η` selects the identity. These public
arithmetic identities supply coordinates for Nikulin's ternary cyclic relations.

## Main declarations

* `ZMod.BinaryQuadraticForm.exists_ternary_complement_sq_add_mul_add_sq_of_modEq_four`:
  square–product–square complement coordinates when `θ ≡ η (mod 4)`.
* `ZMod.BinaryQuadraticForm.exists_ternary_complement_mul_of_modEq_four_neg`:
  hyperbolic complement coordinates when `θ ≡ -η (mod 4)`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(d).
-/

public section

namespace ZMod.BinaryQuadraticForm

/-- Complement coordinates whose diagonal ternary norm with coefficients `θ, θ, η`
equals `2(m² + mn + n²)` when `θ ≡ η (mod 4)`. -/
theorem exists_ternary_complement_sq_add_mul_add_sq_of_modEq_four (k : ℕ) {θ η : ℤ}
    (hθ : Odd θ) (hmod : θ ≡ η [ZMOD 4]) :
    ∃ r a b c d : ZMod (2 ^ (k + 1)), (η : ZMod (2 ^ (k + 1))) * r = θ ∧
      ∀ m n, (θ : ZMod (2 ^ (k + 1))) * (a * m + b * n) ^ 2 +
        θ * (c * m + d * n) ^ 2 + η * (-r * ((a * m + b * n) + (c * m + d * n))) ^ 2 =
          2 * (m ^ 2 + m * n + n ^ 2) := by
  have hη : Odd η := by
    obtain ⟨e, he⟩ := Int.modEq_iff_dvd.mp hmod
    obtain ⟨s, hs⟩ := hθ
    refine ⟨s + 2 * e, ?_⟩
    omega
  obtain ⟨Η, hΗ⟩ := ZMod.isUnit_intCast_two_pow_of_odd (k + 1) hη
  obtain ⟨e, he⟩ := Int.modEq_iff_dvd.mp hmod.symm
  let s : ZMod (2 ^ (k + 1)) := (e : ZMod (2 ^ (k + 1))) * (Η⁻¹ : (ZMod (2 ^ (k + 1)))ˣ)
  let r : ZMod (2 ^ (k + 1)) := 1 + 4 * s
  have hs : (η : ZMod (2 ^ (k + 1))) * s = e := by
    rw [← hΗ]
    dsimp [s]
    rw [mul_left_comm, Units.mul_inv, mul_one]
  have hr : (η : ZMod (2 ^ (k + 1))) * r = θ := by
    have he' := congrArg (fun n : ℤ ↦ (n : ZMod (2 ^ (k + 1)))) he
    push_cast at he'
    dsimp [r]
    linear_combination 4 * hs - he'
  have hA : IsUnit ((θ : ZMod (2 ^ (k + 1))) * (1 + 2 * s)) :=
    (ZMod.isUnit_intCast_two_pow_of_odd (k + 1) hθ).mul (by
      convert ZMod.isUnit_two_mul_add (c := s) isUnit_one using 1
      ring)
  have hC : IsUnit ((θ : ZMod (2 ^ (k + 1))) * r) :=
    (ZMod.isUnit_intCast_two_pow_of_odd (k + 1) hθ).mul (by
      convert ZMod.isUnit_two_mul_add (c := 2 * s) isUnit_one using 1
      ring)
  obtain ⟨t, ht⟩ | ⟨t, ht⟩ :=
    ZMod.eq_two_mul_or_eq_two_mul_add_one ((θ : ZMod (2 ^ (k + 1))) * (1 + 2 * s))
  · exact (ZMod.not_isUnit_two_mul t (ht ▸ hA)).elim
  · obtain ⟨a, c, b, d, h⟩ :=
      ZMod.BinaryQuadraticForm.exists_sq_add_mul_add_sq_of_odd t t hC
    refine ⟨r, a, b, c, d, hr, fun m n ↦ ?_⟩
    have hm := h m n
    rw [← ht] at hm
    dsimp [r] at hr hm ⊢
    linear_combination 2 * hm +
      (1 + 4 * s) * ((a * m + b * n) + (c * m + d * n)) ^ 2 * hr

/-- Complement coordinates whose diagonal ternary norm with coefficients `θ, θ, η`
equals `2mn` when `θ ≡ -η (mod 4)`. -/
theorem exists_ternary_complement_mul_of_modEq_four_neg (k : ℕ) {θ η : ℤ}
    (hθ : Odd θ) (hmod : θ ≡ -η [ZMOD 4]) :
    ∃ r a b c d : ZMod (2 ^ (k + 1)), (η : ZMod (2 ^ (k + 1))) * r = θ ∧
      ∀ m n, (θ : ZMod (2 ^ (k + 1))) * (a * m + b * n) ^ 2 +
        θ * (c * m + d * n) ^ 2 + η * (-r * ((a * m + b * n) + (c * m + d * n))) ^ 2 =
          2 * m * n := by
  have hη : Odd η := by
    obtain ⟨e, he⟩ := Int.modEq_iff_dvd.mp hmod
    obtain ⟨s, hs⟩ := hθ
    refine ⟨-s - 2 * e - 1, ?_⟩
    omega
  obtain ⟨Η, hΗ⟩ := ZMod.isUnit_intCast_two_pow_of_odd (k + 1) hη
  obtain ⟨e, he⟩ := Int.modEq_iff_dvd.mp hmod.symm
  let s : ZMod (2 ^ (k + 1)) := (e : ZMod (2 ^ (k + 1))) * (Η⁻¹ : (ZMod (2 ^ (k + 1)))ˣ)
  let r : ZMod (2 ^ (k + 1)) := -1 + 4 * s
  have hs : (η : ZMod (2 ^ (k + 1))) * s = e := by
    rw [← hΗ]
    dsimp [s]
    rw [mul_left_comm, Units.mul_inv, mul_one]
  have hr : (η : ZMod (2 ^ (k + 1))) * r = θ := by
    have he' := congrArg (fun n : ℤ ↦ (n : ZMod (2 ^ (k + 1)))) he
    push_cast at he'
    dsimp [r]
    linear_combination 4 * hs - he'
  have hC : IsUnit ((θ : ZMod (2 ^ (k + 1))) * r) :=
    (ZMod.isUnit_intCast_two_pow_of_odd (k + 1) hθ).mul (by
      convert ZMod.isUnit_two_mul_add (c := 2 * s) isUnit_one.neg using 1
      ring)
  obtain ⟨a, c, b, d, h⟩ :=
    ZMod.BinaryQuadraticForm.exists_hyperbolic_of_two_mul ((θ : ZMod (2 ^ (k + 1))) * s)
      (2 * (θ : ZMod (2 ^ (k + 1))) * s) hC
  refine ⟨r, a, b, c, d, hr, fun m n ↦ ?_⟩
  have hm := h m n
  dsimp [r] at hr hm ⊢
  linear_combination 2 * hm +
    (-1 + 4 * s) * ((a * m + b * n) + (c * m + d * n)) ^ 2 * hr

end ZMod.BinaryQuadraticForm
