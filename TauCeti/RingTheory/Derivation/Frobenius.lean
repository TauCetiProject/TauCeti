/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.Subfield.Basic
public import TauCeti.RingTheory.Derivation.Basic

/-!
# Derivations and the Frobenius subfield

Every derivation out of a field `k` of prime characteristic `p` vanishes on the Frobenius subfield
`k ^ p = (frobenius k p).fieldRange`.

## Main results

* `Derivation.map_eq_zero_of_mem_fieldRange_frobenius`: any derivation out of `k` vanishes on
  `k ^ p`.
-/

public section

namespace Derivation

/-- Every element of the Frobenius subfield `k ^ p` is annihilated by any derivation out of `k`. -/
theorem map_eq_zero_of_mem_fieldRange_frobenius {p : ℕ} [Fact p.Prime] {R k M : Type*}
    [CommSemiring R] [Field k] [ExpChar k p] [Algebra R k] [AddCommMonoid M] [Module R M]
    [Module k M] (d : Derivation R k M) {x : k} (hx : x ∈ (frobenius k p).fieldRange) :
    d x = 0 := by
  have : CharP k p := (expChar_prime_iff k Fact.out).mp ‹_›
  obtain ⟨a, rfl⟩ := hx
  rw [frobenius_def, d.map_pow_eq_zero_of_charP]

end Derivation
