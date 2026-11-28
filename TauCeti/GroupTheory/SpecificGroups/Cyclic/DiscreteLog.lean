/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Discrete logarithms on `(ℤ/p)ˣ`

Specialising `IsCyclic.exists_monoidHom_apply_eq_of_orderOf_dvd_natCard` to the cyclic unit group
`(ℤ/p)ˣ` of a prime `p ≡ 1 [MOD k]` and `y = Multiplicative.ofAdd (1 : ZMod k)` produces a
surjective homomorphism `(ℤ/p)ˣ →* Multiplicative (ZMod k)`, i.e. a discrete logarithm modulo `k`.

## Main results

* `ZMod.exists_monoidHom_units_eq_ofAdd_one`: for a prime `p ≡ 1 [MOD k]`, there exist a
  homomorphism `L : (ZMod p)ˣ →* Multiplicative (ZMod k)` and a unit `g : (ZMod p)ˣ` with
  `L g = Multiplicative.ofAdd 1`.

## Provenance

Adapted from grh-lean
(https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cyclotomic/Kolyvagin/DerivativeCocycles.lean`
(`New.exists_monoidHom_units_zmod_eq_ofAdd_one`).
-/

public section

namespace ZMod

/-- Discrete logarithm modulo `k`: for a prime `p ≡ 1 [MOD k]`, there exist a group homomorphism
`L : (ZMod p)ˣ →* Multiplicative (ZMod k)` and a unit `g : (ZMod p)ˣ` with
`L g = Multiplicative.ofAdd 1`. -/
theorem exists_monoidHom_units_eq_ofAdd_one {p k : ℕ} (hp : p.Prime) (hpk : p ≡ 1 [MOD k]) :
    ∃ (L : (ZMod p)ˣ →* Multiplicative (ZMod k)) (g : (ZMod p)ˣ),
      L g = Multiplicative.ofAdd 1 := by
  have : Fact p.Prime := ⟨hp⟩
  refine IsCyclic.exists_monoidHom_apply_eq_of_orderOf_dvd_natCard ?_
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [hcard, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  exact hpk.symm.dvd'

end ZMod
