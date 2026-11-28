/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.ZMod.PrimitiveRoot

/-!
# Primitive roots modulo `p` congruent to `1` modulo `N` in `ℤ_[p]`-algebras

Given a prime `p` and a natural number `N` coprime to `p`,
`ZMod.exists_modEq_one_coprime_isPrimitiveRoot` lifts a primitive `(p - 1)`-st root of unity in
`ZMod p` to a natural number `a ≡ 1 [MOD N]` coprime to `p`.

Consequently, for any ring `R` equipped with a `ℤ_[p]`-algebra structure, `(a : R) ^ k - 1` is a
unit in `R` for every `k : ℕ` not divisible by `p - 1`
(`PadicInt.exists_modEq_one_forall_isUnit_pow_sub_one`).

## Main results

* `PadicInt.exists_modEq_one_forall_isUnit_pow_sub_one`: for a prime `p` coprime to `N` and any
  `ℤ_[p]`-algebra `R`, there is `a : ℕ` with `a ≡ 1 [MOD N]`, `p.Coprime a`, and
  `IsUnit ((a : R) ^ k - 1)` for all `k : ℕ` with `¬ (p - 1) ∣ k`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
src/Lib/Cyclotomic/Kolyvagin/ReciprocityComponentBounds.lean
(`exists_modEq_one_forall_isUnit_pow_sub_one`).
-/

public section

namespace PadicInt

/-- For a prime `p` coprime to `N` and any `ℤ_[p]`-algebra `R`, there exists `a : ℕ` congruent to
`1` modulo `N` and coprime to `p` such that `(a : R) ^ k - 1` is a unit in `R` for every `k : ℕ`
not divisible by `p - 1`. -/
theorem exists_modEq_one_forall_isUnit_pow_sub_one {p N : ℕ} [Fact p.Prime]
    {R : Type*} [Ring R] [Algebra ℤ_[p] R] (hN : p.Coprime N) :
    ∃ a : ℕ, a ≡ 1 [MOD N] ∧ p.Coprime a ∧
      ∀ k : ℕ, ¬ (p - 1) ∣ k → IsUnit ((a : R) ^ k - 1) := by
  obtain ⟨a, ha, hpa, hb⟩ := ZMod.exists_modEq_one_coprime_isPrimitiveRoot hN
  refine ⟨a, ha, hpa, fun k hk ↦ ?_⟩
  have h_unit : IsUnit ((a : ℤ_[p]) ^ k - 1) :=
    .of_map PadicInt.toZMod _ (by
      simpa [sub_eq_zero] using (hb.pow_eq_one_iff_dvd k).not.2 hk)
  simpa using h_unit.map (algebraMap ℤ_[p] R)

end PadicInt
