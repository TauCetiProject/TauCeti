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

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(c).
-/

public section

namespace ZMod

variable {k : ℕ}

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

end ZMod
