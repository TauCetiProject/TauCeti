/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Primitive roots modulo `p` congruent to `1` modulo `N`

Given a prime `p` and a natural number `N` coprime to `p`, the Chinese remainder theorem lifts a
primitive `(p - 1)`-st root of unity in `ZMod p` to a natural number `a ≡ 1 [MOD N]` coprime to
`p` (`ZMod.exists_modEq_one_coprime_isPrimitiveRoot`).

Consequently, for any ring `R` equipped with a `ℤ_[p]`-algebra structure, `a ^ k - 1` is a unit
in `R` for every `0 < k < p - 1` (`PadicInt.exists_modEq_one_forall_isUnit_pow_sub_one`).

## Main results

* `ZMod.exists_modEq_one_coprime_isPrimitiveRoot`: for a prime `p` coprime to `N`, there is
  `a : ℕ` with `a ≡ 1 [MOD N]`, `p.Coprime a`, and `IsPrimitiveRoot (a : ZMod p) (p - 1)`.
* `PadicInt.exists_modEq_one_forall_isUnit_pow_sub_one`: for a prime `p` coprime to `N` and any
  `ℤ_[p]`-algebra `R`, there is `a : ℕ` with `a ≡ 1 [MOD N]`, `p.Coprime a`, and
  `IsUnit ((a : R) ^ k - 1)` for all `0 < k < p - 1`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
src/Lib/Cyclotomic/Kolyvagin/ReciprocityComponentBounds.lean
(`exists_modEq_one_forall_isUnit_pow_sub_one`).
-/

public section

namespace ZMod

/-- For a prime `p` and a natural number `N` coprime to `p`, there exists `a : ℕ` congruent to `1`
modulo `N` and coprime to `p` whose reduction modulo `p` is a primitive `(p - 1)`-st root of unity
in `ZMod p`. -/
theorem exists_modEq_one_coprime_isPrimitiveRoot {p N : ℕ} [Fact p.Prime] (hN : p.Coprime N) :
    ∃ a : ℕ, a ≡ 1 [MOD N] ∧ p.Coprime a ∧ IsPrimitiveRoot (a : ZMod p) (p - 1) := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hord : orderOf (u : ZMod p) = p - 1 := by
    rw [← Units.coeHom_apply, orderOf_injective (Units.coeHom (ZMod p)) Units.val_injective u, hu,
      Nat.card_eq_fintype_card, ZMod.card_units]
  have hb : IsPrimitiveRoot (u : ZMod p) (p - 1) := by
    rw [← hord]
    exact IsPrimitiveRoot.orderOf (u : ZMod p)
  obtain ⟨a, hab, ha⟩ := Nat.chineseRemainder hN (u : ZMod p).val 1
  have hab' : (a : ZMod p) = (u : ZMod p) := by
    simpa [← ZMod.natCast_eq_natCast_iff] using hab
  have hp_pos : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt
  have hpa : p.Coprime a :=
    ((ZMod.isUnit_iff_coprime a p).1 (hab' ▸ hb.isUnit hp_pos)).symm
  exact ⟨a, ha, hpa, hab' ▸ hb⟩

end ZMod

namespace PadicInt

/-- For a prime `p` coprime to `N` and any `ℤ_[p]`-algebra `R`, there exists `a : ℕ` congruent to
`1` modulo `N` and coprime to `p` such that `(a : R) ^ k - 1` is a unit in `R` for every
`0 < k < p - 1`. -/
theorem exists_modEq_one_forall_isUnit_pow_sub_one {p N : ℕ} [Fact p.Prime]
    {R : Type*} [Ring R] [Algebra ℤ_[p] R] (hN : p.Coprime N) :
    ∃ a : ℕ, a ≡ 1 [MOD N] ∧ p.Coprime a ∧
      ∀ k : ℕ, 0 < k → k < p - 1 → IsUnit ((a : R) ^ k - 1) := by
  obtain ⟨a, ha, hpa, hb⟩ := ZMod.exists_modEq_one_coprime_isPrimitiveRoot hN
  refine ⟨a, ha, hpa, fun k hk hkp ↦ ?_⟩
  have h_unit : IsUnit ((a : ℤ_[p]) ^ k - 1) :=
    .of_map PadicInt.toZMod _ (by
      simpa [sub_eq_zero] using hb.pow_ne_one_of_pos_of_lt hk.ne' hkp)
  simpa using h_unit.map (algebraMap ℤ_[p] R)

end PadicInt
