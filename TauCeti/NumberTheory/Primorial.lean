/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Primorial
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Primorial divisibility

A factorial is divisible by the product of the primes up to the same cutoff.
-/

public section

open Finset Nat

namespace TauCeti

/-- The primorial of `n` divides `n!`. -/
theorem primorial_dvd_factorial (n : ℕ) : primorial n ∣ n.factorial := by
  rw [primorial, ← prod_Ico_id_eq_factorial]
  apply prod_dvd_prod_of_subset
  intro p hp
  simp only [mem_filter, mem_range] at hp
  exact mem_Ico.mpr ⟨hp.2.one_lt.le, hp.1⟩

end TauCeti
