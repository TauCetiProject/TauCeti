/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.RegularNormal
public import TauCeti.GroupTheory.GroupAction.Simple.Suborbit
public import TauCeti.GroupTheory.SpecificGroups.Sporadic.HigmanSims.Order
public import TauCeti.GroupTheory.SpecificGroups.Sporadic.HigmanSims.Perfect
public import TauCeti.GroupTheory.SpecificGroups.Sporadic.HigmanSims.Primitive
public import TauCeti.GroupTheory.Subgroup.NormalGeneration

/-!
# Simplicity of the Higman--Sims permutation model

The canonical ATLAS model `TauCeti.Sporadic.HS` on 100 points is simple.

The degree `100 = 2² * 5²` has no prime divisor occurring only once in the order
`44352000 = 2⁹ * 3² * 5³ * 7 * 11`, so the prime `11` is brought in through a suborbit instead.
The stabilizer of `0` has a 22-point orbit, on which it acts doubly transitively
(`TauCeti.Sporadic.HS.isMultiplyPretransitive_stabilizer_orbit`). By
`TauCeti.MulAction.natCard_orbit_stabilizer_dvd_natCard_stabilizer_of_normal`, the order of every
nontrivial normal subgroup that does not act regularly is therefore divisible by `22`, and such a
subgroup contains the element `a * b`, whose `11`-th power is `1`, because `11 ^ 2` does not
divide the order of the model. That element normally generates the perfect group `HS`. Finally
no normal subgroup acts regularly: a group of order `100` has a unique Sylow `5`-subgroup
(`TauCeti.stabilizer_ne_bot_of_forall_dvd_natCard_modEq_one`).

This proves simplicity of the permutation model, not recognition of the abstract Higman--Sims
presentation. The point stabilizer is not identified with `M₂₂`, and its simplicity is not used.

## Main results

* `TauCeti.Sporadic.isSimpleGroup_HS`: the ATLAS permutation model of `HS` is simple.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representation `HSG1-p100B0`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/HSG1-p100B0>.
* D. G. Higman and C. C. Sims, *A simple group of order 44,352,000*, Math. Z. **105** (1968),
  110–113, for the rank-three action with suborbits of lengths 1, 22 and 77.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, §1.6 and Chapter 4, for normal subgroups of
  primitive groups.
-/

public section

namespace TauCeti.Sporadic

/-- The canonical 100-point permutation model of the Higman--Sims group is simple. -/
instance isSimpleGroup_HS : IsSimpleGroup HS := by
  have hgen : Subgroup.closure ({⟨HS.a, HS.a_mem⟩, ⟨HS.b, HS.b_mem⟩} : Set HS) = ⊤ := by
    have h : Subgroup.closure (HS.subtype ⁻¹' {HS.a, HS.b}) = ⊤ := by
      rw [HS_def]
      exact Subgroup.closure_preimage_eq_top _
    rw [← h]
    congr 1
    ext x
    simp [Subtype.ext_iff]
  have : MulAction.IsPreprimitive (MulAction.stabilizer HS (0 : Fin 100))
      (MulAction.orbit (MulAction.stabilizer HS (0 : Fin 100)) (4 : Fin 100)) :=
    MulAction.isPreprimitive_of_is_two_pretransitive HS.isMultiplyPretransitive_stabilizer_orbit
  have hdvd : 11 ∣ Nat.card (MulAction.orbit (MulAction.stabilizer HS (0 : Fin 100))
      (4 : Fin 100)) := by
    rw [Nat.card_coe_set_eq, HS.orbit_stabilizer_zero, HS.ncard_orbit_stabilizerChain_one_four]
    norm_num
  have hcard : ¬ 11 ^ 2 ∣ Nat.card HS := by
    rw [card_HS]
    norm_num
  -- A group of order `100` has a unique Sylow `5`-subgroup.
  have hmod : ∀ d, d ∣ Nat.card (Fin 100) → d ≡ 1 [MOD 5] → d = 1 := by
    have h : ∀ d ∈ Nat.divisors 100, d ≡ 1 [MOD 5] → d = 1 := by decide
    intro d hd
    exact h d (Nat.mem_divisors.mpr ⟨by simpa using hd, by norm_num⟩)
  have hpow : (⟨HS.a, HS.a_mem⟩ * ⟨HS.b, HS.b_mem⟩ : HS) ^ 11 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]
    decide +kernel
  exact isSimpleGroup_of_normalClosure_eq_top_of_prime_dvd_card_orbit_stabilizer
    (X := Fin 100) 0 4 Nat.prime_eleven hdvd hcard
    (fun N _ _ ↦ stabilizer_ne_bot_of_forall_dvd_natCard_modEq_one (q := 5) (r := 2)
      Nat.prime_five Nat.prime_two (by norm_num) (by simp) (by simp) hmod N 0)
    _ hpow (Subgroup.normalClosure_singleton_mul_eq_top _ _ hgen)

end TauCeti.Sporadic
