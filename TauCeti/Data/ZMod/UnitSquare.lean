/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Data.ZMod.Two
import TauCeti.Data.ZMod.BinaryQuadraticForm
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Unit squares modulo powers of two

Every element of the form `1 + 8a` is the square of a unit modulo `2^{k+1}`.
The square root has the form `1 + 4t`: the bijection `t ↦ 2t² + t` supplies `t`.
In particular, an integer congruent to one modulo eight gives a unit square at every
positive dyadic exponent. The variant `5 - 4r`, for a unit `r`, provides the rotation
coefficient for pairs of odd cyclic dyadic forms.

For any modulus divisible by sixteen, the kernel of reduction to half the modulus
consists of squares (`ZMod.isSquare_of_cast_half_eq_one`). This also applies when the
modulus has odd factors and gives the dyadic conductor bound for quadratic characters.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(c).
-/

public section

namespace ZMod

variable {k : ℕ}

/-- If sixteen divides the modulus, every residue that becomes one modulo half the
modulus is a square. The modulus may be zero, in which case the hypothesis forces `x = 1`. -/
theorem isSquare_of_cast_half_eq_one {N : ℕ} (x : ZMod N) (hN : 16 ∣ N)
    (hx : (x.cast : ZMod (N / 2)) = 1) : IsSquare x := by
  obtain ⟨m, rfl⟩ := hN
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  have hhalf : 16 * m / 2 = 8 * m := by omega
  have hd : 8 * m ∣ 16 * m := ⟨2, by omega⟩
  have ha : (a : ZMod (8 * m)) = 1 := by
    rw [hhalf] at hx
    simpa only [ZMod.cast_intCast hd] using hx
  have ht : (8 * (m : ℤ)) ∣ a - 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) (8 * m)).mp
      (by simpa using sub_eq_zero.mpr ha)
    simpa using this
  obtain ⟨t, ht⟩ := ht
  have ht' := congrArg (fun z : ℤ ↦ (z : ZMod (16 * m))) ht
  push_cast at ht'
  have hz : (16 : ZMod (16 * m)) * m = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using ZMod.natCast_self (16 * m)
  -- Squaring `1 + 4mt` gives `1 + 8mt`: its remaining term is a multiple of `16m`.
  refine (isSquare_iff_exists_sq _).mpr ⟨1 + 4 * (m : ZMod (16 * m)) * t, ?_⟩
  linear_combination ht' - (m * (t : ZMod (16 * m)) ^ 2) * hz

/-- Every residue `1 + 8a` modulo `2^{k+1}` is the square of a unit. -/
theorem exists_unit_sq_eq_one_add_eight_mul (a : ZMod (2 ^ (k + 1))) :
    ∃ u : (ZMod (2 ^ (k + 1)))ˣ, (u : ZMod (2 ^ (k + 1))) ^ 2 = 1 + 8 * a := by
  obtain ⟨t, ht⟩ := (two_mul_sq_add_bijective (c := 1) isUnit_one).2 a
  have hu : IsUnit (2 * (2 * t) + 1) := isUnit_two_mul_add (c := 2 * t) isUnit_one
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  linear_combination 8 * ht

/-- The residue `5 - 4r` is a unit square whenever `r` is a unit modulo `2^{k+1}`. -/
theorem exists_unit_sq_eq_five_sub_four_mul {r : ZMod (2 ^ (k + 1))} (hr : IsUnit r) :
    ∃ u : (ZMod (2 ^ (k + 1)))ˣ, (u : ZMod (2 ^ (k + 1))) ^ 2 = 5 - 4 * r := by
  obtain ⟨s, rfl⟩ | ⟨s, rfl⟩ := eq_two_mul_or_eq_two_mul_add_one r
  · exact (not_isUnit_two_mul s hr).elim
  · obtain ⟨u, hu⟩ := exists_unit_sq_eq_one_add_eight_mul (-s)
    refine ⟨u, ?_⟩
    rw [hu]
    ring

/-- Odd integer coefficients congruent modulo eight differ by a unit square modulo
any positive power of two. The square multiplies the second coefficient to the first. -/
theorem exists_unit_sq_mul_intCast_eq_of_modEq_eight (k : ℕ) {θ η : ℤ}
    (hη : Odd η) (h : θ ≡ η [ZMOD 8]) :
    ∃ u : (ZMod (2 ^ (k + 1)))ˣ, (η : ZMod (2 ^ (k + 1))) * (u : ZMod (2 ^ (k + 1))) ^ 2 = θ := by
  have hunit : IsUnit (η : ZMod (2 ^ (k + 1))) := by
    obtain ⟨t, rfl⟩ := hη
    convert isUnit_two_mul_add (c := (t : ZMod (2 ^ (k + 1)))) isUnit_one using 1
    push_cast
    ring
  obtain ⟨Η, hΗ⟩ := hunit
  obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.mp h
  have hcast : (η : ZMod (2 ^ (k + 1))) - θ = 8 * d := by
    have hc := congrArg (fun z : ℤ ↦ (z : ZMod (2 ^ (k + 1)))) hd
    push_cast at hc
    exact hc
  let c : ZMod (2 ^ (k + 1)) := -(d : ZMod (2 ^ (k + 1))) *
    (Η⁻¹ : (ZMod (2 ^ (k + 1)))ˣ)
  obtain ⟨u, hu⟩ := exists_unit_sq_eq_one_add_eight_mul c
  refine ⟨u, ?_⟩
  rw [hu]
  dsimp [c]
  have hinv : (η : ZMod (2 ^ (k + 1))) * (Η⁻¹ : (ZMod (2 ^ (k + 1)))ˣ) = 1 := by
    rw [← hΗ, Units.mul_inv]
  calc
    (η : ZMod (2 ^ (k + 1))) * (1 + 8 * (-d * (Η⁻¹ : (ZMod (2 ^ (k + 1)))ˣ))) =
        η - 8 * d * ((η : ZMod (2 ^ (k + 1))) * (Η⁻¹ : (ZMod (2 ^ (k + 1)))ˣ)) := by ring
    _ = θ := by
      rw [hinv, mul_one]
      linear_combination hcast

end ZMod
