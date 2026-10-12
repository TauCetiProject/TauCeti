/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
import TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter
import TauCeti.NumberTheory.LocalField.NatCastValuation

/-!
# The cyclotomic character on inertia and on Frobenius lifts

Let `K` be a nonarchimedean local field whose residue field has `q` elements, and let `p` be a
prime different from the residue characteristic. The roots of unity of `p`-power order of `K^{alg}`
lie in the maximal unramified extension of `K`, so the `p`-adic cyclotomic character of
`G_K = Gal(K^{alg}/K)` factors through the unramified quotient `G_K ⧸ I_K`: it is trivial on the
inertia subgroup, and it takes the value `q` on every arithmetic Frobenius lift.

## Main results

* `TauCeti.localCyclotomicCharacter_eq_one_of_mem_inertiaSubgroup`: the `p`-adic cyclotomic
  character is trivial on inertia.
* `TauCeti.IsArithFrobeniusLift.coe_localCyclotomicCharacter`: the `p`-adic cyclotomic character
  of an arithmetic Frobenius lift is `q`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9.
-/

public section

namespace TauCeti

open ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime]

/-- **The cyclotomic character is unramified away from the residue characteristic**: for a prime
`p` different from the residue characteristic of `K`, the `p`-adic cyclotomic character is trivial
on the inertia subgroup. -/
theorem localCyclotomicCharacter_eq_one_of_mem_inertiaSubgroup
    (hp : p.Coprime (ringChar 𝓀[K])) {σ : Field.absoluteGaloisGroup K}
    (hσ : σ ∈ inertiaSubgroup K) :
    localCyclotomicCharacter p K σ = 1 := by
  have : NeZero (p : K) := ⟨natCast_ne_zero_of_coprime_ringChar hp⟩
  refine Units.ext ?_
  rw [localCyclotomicCharacter_apply, Units.val_one, ← Nat.cast_one]
  refine coe_cyclotomicCharacter_eq_natCast p fun n t ht ↦ ?_
  rw [pow_one]
  exact apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one hσ (hp.pow_left n) ht

/-- **The cyclotomic character of a Frobenius lift**: for a prime `p` different from the residue
characteristic of `K`, the `p`-adic cyclotomic character of an arithmetic Frobenius lift is the
cardinality `q` of the residue field. -/
theorem IsArithFrobeniusLift.coe_localCyclotomicCharacter (hp : p.Coprime (ringChar 𝓀[K]))
    {σ : Field.absoluteGaloisGroup K} (hσ : IsArithFrobeniusLift K σ) :
    (localCyclotomicCharacter p K σ : ℤ_[p]) = Nat.card 𝓀[K] := by
  have : NeZero (p : K) := ⟨natCast_ne_zero_of_coprime_ringChar hp⟩
  rw [localCyclotomicCharacter_apply]
  exact coe_cyclotomicCharacter_eq_natCast p fun n t ht ↦
    hσ.apply_of_pow_eq_one (hp.pow_left n) ht

end TauCeti
