/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Cast

/-!
# Integrality arguments in ordered rings

An element of an ordered ring strictly between two consecutive integers, congruent modulo integers
to `c`, shows that `c` is not an integer (`TauCeti.not_exists_eq_intCast_of_lt_of_lt_add_one`).
-/

public section

namespace TauCeti

/-- An element of an ordered ring strictly between two consecutive integers, congruent modulo
integers to `c`, shows that `c` is not an integer. -/
theorem not_exists_eq_intCast_of_lt_of_lt_add_one {R : Type*} [Ring R] [PartialOrder R]
    [IsStrictOrderedRing R] {x c : R} {z : ℤ}
    (hx : ∃ m : ℤ, x - c = m) (h₁ : (z : R) < x) (h₂ : x < z + 1) : ¬∃ m : ℤ, c = m := by
  rintro ⟨m, rfl⟩
  obtain ⟨m', hm'⟩ := hx
  have hk' : x = ((m' + m : ℤ) : R) := by
    push_cast
    rw [← hm', sub_add_cancel]
  rw [hk'] at h₁ h₂
  have h₁' : z < m' + m := by exact_mod_cast h₁
  have h₂' : m' + m < z + 1 := by exact_mod_cast h₂
  omega

end TauCeti
