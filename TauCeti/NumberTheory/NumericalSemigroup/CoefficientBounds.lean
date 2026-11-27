/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.GCD.Basic
import TauCeti.NumberTheory.NumericalSemigroup.TwoGenerator

/-!
# Lower bounds on coefficients for two coprime generators

Sylvester's conductor formula still gives a representation when the coefficients have prescribed
lower bounds: reserve the contribution of those bounds before applying the formula.
-/

public section

namespace Nat.Coprime

/-- A number at least the two-generator conductor plus the contribution of `r` copies of `q` and
`s` copies of `h` has a representation with at least those many copies of the two generators. -/
theorem exists_le_and_eq_add_mul {q h m r s : ℕ} (hqh : q.Coprime h)
    (hm : (q - 1) * (h - 1) + (r * q + s * h) ≤ m) :
    ∃ a b : ℕ, r ≤ a ∧ s ≤ b ∧ m = a * q + b * h := by
  have hS := (AddSubmonoid.isNumericalSemigroup_closure_pair_iff q h).mpr hqh
  have hmem := AddSubmonoid.mem_of_numericalConductor_le hS
    (n := m - (r * q + s * h)) (by
      rw [AddSubmonoid.numericalConductor_closure_pair hqh]
      omega)
  obtain ⟨a, b, hab⟩ := (AddSubmonoid.mem_closure_pair _ _ _).mp hmem
  simp only [smul_eq_mul] at hab
  refine ⟨a + r, b + s, Nat.le_add_left _ _, Nat.le_add_left _ _, ?_⟩
  rw [Nat.add_mul, Nat.add_mul]
  omega

end Nat.Coprime
