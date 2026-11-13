/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TriangleGroup.Basic
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect triangle groups

An oriented triangle group with pairwise coprime parameters is perfect. Consequently every
quotient of such a triangle group is perfect, without any finiteness assumption. This gives
perfectness tests for two-generator presentations containing three suitable power relations.

The parameters may be zero: the coprimality conditions, rather than positivity or a geometric
realization of the triangle group, are what the argument uses.
-/

public section

namespace TauCeti.TriangleGroup

/-- An oriented triangle group with pairwise coprime parameters is perfect. -/
theorem isPerfect_of_coprime {a b c : ℕ} (hab : a.Coprime b) (hac : a.Coprime c)
    (hbc : b.Coprime c) : Group.IsPerfect (TriangleGroup a b c) := by
  let f : TriangleGroup a b c →* Group.Abelianization (TriangleGroup a b c) :=
    Group.Abelianization.of
  have hx : f (x a b c) ^ a = 1 := by rw [← map_pow, x_pow, map_one]
  have hy : f (y a b c) ^ b = 1 := by rw [← map_pow, y_pow, map_one]
  have hxy : (f (y a b c) * f (x a b c)) ^ c = 1 := by
    rw [← map_mul, ← map_pow, y_mul_x_pow, map_one]
  -- In the abelianization, eliminating the other generator gives a second annihilating
  -- exponent for each generator. Coprimality forces both orders to be one.
  have hxb : f (x a b c) ^ (b * c) = 1 := by
    have h := congrArg (fun t => t ^ b) hxy
    simpa only [mul_pow, pow_right_comm _ c b, hy, one_pow, one_mul, ← pow_mul] using h
  have hya : f (y a b c) ^ (a * c) = 1 := by
    have h := congrArg (fun t => t ^ a) hxy
    simpa only [mul_pow, pow_right_comm _ c a, hx, one_pow, mul_one, ← pow_mul] using h
  have hfx : f (x a b c) = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hab.mul_right hac)
      (orderOf_dvd_of_pow_eq_one hx) (orderOf_dvd_of_pow_eq_one hxb))
  have hfy : f (y a b c) = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hab.symm.mul_right hbc)
      (orderOf_dvd_of_pow_eq_one hy) (orderOf_dvd_of_pow_eq_one hya))
  have hf : f = 1 := hom_ext a b c hfx hfy
  constructor
  rw [← Group.Abelianization.ker_of]
  exact (congrArg MonoidHom.ker hf).trans MonoidHom.ker_one

end TauCeti.TriangleGroup
