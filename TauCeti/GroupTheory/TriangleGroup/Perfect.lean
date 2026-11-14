/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TriangleGroup.Basic
public import TauCeti.GroupTheory.IsPerfect

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
  apply isPerfect_of_coprime_pow_eq_one (x := y a b c) (y := x a b c)
    (a := b) (b := a) (c := c)
  · simpa only [Set.pair_comm] using closure_x_y a b c
  · exact y_pow a b c
  · exact x_pow a b c
  · exact y_mul_x_pow a b c
  · exact hab.symm
  · exact hbc
  · exact hac

end TauCeti.TriangleGroup
