/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Order
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Examples.NumberTheory.NumberField.RestrictedRamification
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.NumberTheory.NumberField.RestrictedRamification.Cyclotomic

/-!
# Checks: the primes `ℓ` with `ℓ^∞ ∣ [ℚ_S : ℚ]`

* For `S` the set of finite places of `ℚ` above `2`, `ℚ(μ_{2^∞}) ≤ ℚ_S` and `2^∞` divides the
  supernatural order of `G_{ℚ,S}`: `2 ∈ P`.
* For `S = ∅`, `ℚ_S = ℚ`, so `G_{ℚ,S}` is trivial and no prime divides its supernatural order:
  `P = ∅`.
-/

public section

open IsDedekindDomain

open scoped NumberField

namespace TauCeti.Examples.RestrictedRamification

open TauCeti.RestrictedRamification

/-- `ℚ(μ_{2^∞}) ≤ ℚ_S` for `S` the places above `2`. -/
example (Ω : Type*) [Field Ω] [Algebra ℚ Ω] :
    IntermediateField.adjoin ℚ {x : Ω | ∃ n : ℕ, x ^ (2 ^ n) = 1} ≤
      maxUnramifiedOutside ℚ Ω {v | (2 : 𝓞 ℚ) ∈ v.asIdeal} :=
  adjoin_setOf_pow_pow_eq_one_le_maxUnramifiedOutside two_ne_zero fun _ hv h ↦
    hv (by exact_mod_cast h)

/-- `2 ∈ P` for `S` the places above `2`: `2^∞` divides the supernatural order of `G_{ℚ,S}`. -/
example :
    profiniteOrder (galoisGroupS ℚ (AlgebraicClosure ℚ) {v | (2 : 𝓞 ℚ) ∈ v.asIdeal})
      ⟨2, Nat.prime_two⟩ = ⊤ :=
  profiniteOrder_galoisGroupS_apply_eq_top ⟨2, Nat.prime_two⟩ fun _ hv h ↦ hv (by exact_mod_cast h)

/-- `P = ∅` for `S = ∅`: no prime divides the supernatural order of `G_{ℚ,∅} = 1`. -/
example (Ω : Type*) [Field Ω] [Algebra ℚ Ω] (p : Nat.Primes) :
    profiniteOrder (galoisGroupS ℚ Ω ∅) p = 0 := by
  have : Subsingleton (galoisGroupS ℚ Ω ∅) :=
    IntermediateField.subsingleton_algEquiv_of_eq_bot (maxUnramifiedOutside_rat_empty Ω)
  refine (profiniteOrder_apply_eq_zero_iff _ p).2 fun U ↦ ?_
  rw [Nat.card_eq_one_iff_unique.2 ⟨QuotientGroup.mk_surjective.subsingleton, inferInstance⟩]
  exact p.prop.not_dvd_one

end TauCeti.Examples.RestrictedRamification
