/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Simple.RegularNormal
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
The stabilizer of `0` has a 22-point orbit, on which it acts doubly transitively: explicit words
in the ATLAS generators fix `0` and `4` and carry `8` to each of the other 20 points. By
`TauCeti.natCard_orbit_stabilizer_dvd_natCard_of_normal`, the order of every nontrivial normal
subgroup that does not act regularly is therefore divisible by `22`, and such a subgroup contains
the element `a * b`, whose `11`-th power is `1`, because `11 ^ 2` does not divide the order of the
model. That element normally generates the perfect group `HS`. Finally no normal subgroup acts
regularly: a group of order `100` has a unique Sylow `5`-subgroup
(`TauCeti.stabilizer_ne_bot_of_forall_dvd_natCard_modEq_one`).

This proves simplicity of the permutation model, not recognition of the abstract Higman--Sims
presentation. The point stabilizer is not identified with `M₂₂`, and its simplicity is not used.

## Main results

* `TauCeti.Sporadic.HS.isMultiplyPretransitive_stabilizer_orbit`: the stabilizer of `0` acts
  doubly transitively on its 22-point orbit.
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

namespace HS

open _root_.MulAction

-- The points other than 4 in the 22-point orbit of the stabilizer of 0.
private def restPoints : Fin 21 → Fin 100 :=
  ![8, 9, 10, 11, 12, 26, 28, 32, 38, 39, 40, 44, 47, 49, 50, 52, 66, 67, 70, 71, 91]

-- Breadth-first paths on ordered triples, from (0, 4, 8) to (0, 4, restPoints i). A word is
-- read in Mathlib's product convention: its last letter acts first.
private def restWords : Fin 21 → List HS :=
  let aa : HS := ⟨a, a_mem⟩
  let bb : HS := ⟨b, b_mem⟩
  ![[],
    [bb, aa, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa, bb],
    [bb, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, aa, bb, aa, bb, bb, aa, bb, bb, bb, aa],
    [aa, bb, bb, aa, bb, bb, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, aa, bb],
    [aa, bb, bb, aa, bb, bb, bb, aa],
    [bb, aa, bb, aa, bb, bb, aa, bb, bb, aa, bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa,
      bb, bb, aa, bb, aa],
    [aa, bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, bb, bb, aa, bb, aa],
    [bb, aa, bb, bb, aa, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, aa, bb, bb, bb, bb, aa, bb,
      bb, bb, bb],
    [bb, aa, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, bb],
    [aa, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, bb, bb, bb, aa, bb, bb, aa],
    [bb, aa, bb, aa, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, aa, bb, bb, bb, bb, aa, bb, aa,
      bb],
    [bb, bb, bb, aa, bb, aa, bb, aa, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, bb, bb, aa, bb,
      bb, aa, bb, bb, bb],
    [bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa, bb],
    [bb, bb, bb, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, bb, aa, bb, bb, bb, aa],
    [bb, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, aa, bb],
    [bb, aa, bb, aa, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, bb],
    [bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa, bb, aa, bb, bb, aa, bb, bb, bb, aa],
    [bb, bb, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, aa, bb, bb, bb, aa],
    [bb, bb, bb, bb, aa, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, bb, bb, aa, bb],
    [bb, bb, bb, bb, aa, bb, bb, aa, bb, bb, bb, bb, aa, bb, aa, bb, bb, bb, aa, bb],
    [bb, bb, bb, aa, bb, aa, bb, bb, bb, bb, aa, bb, bb]]

private theorem restWords_apply : ∀ i,
    ((restWords i).prod : Equiv.Perm (Fin 100)) 0 = 0 ∧
      ((restWords i).prod : Equiv.Perm (Fin 100)) 4 = 4 ∧
      ((restWords i).prod : Equiv.Perm (Fin 100)) 8 = restPoints i := by
  decide +kernel

private theorem exists_restPoints_eq : ∀ x ∈ ({4, 8, 9, 10, 11, 12, 26, 28, 32, 38, 39, 40, 44,
    47, 49, 50, 52, 66, 67, 70, 71, 91} : Finset (Fin 100)), x ≠ 4 → ∃ i, restPoints i = x := by
  decide +kernel

-- The stabilizer of 0 in the model has the orbits of the second member of the stabilizer chain.
private theorem orbit_stabilizer_zero (x : Fin 100) :
    orbit (stabilizer HS (0 : Fin 100)) x = orbit (HS.stabilizerChain pointSequence 1) x := by
  have h0 : pointSequence 0 = 0 := by
    rw [pointSequence_apply]
    decide
  rw [Subgroup.orbit_stabilizerChain_succ, Subgroup.stabilizerChain_zero, h0]

/-- The stabilizer of `0` in the Higman--Sims model acts doubly transitively on its 22-point
orbit, the orbit of `4`. -/
instance isMultiplyPretransitive_stabilizer_orbit :
    IsMultiplyPretransitive (stabilizer HS (0 : Fin 100))
      (orbit (stabilizer HS (0 : Fin 100)) (4 : Fin 100)) 2 := by
  have h8 : (8 : Fin 100) ∈ orbit (stabilizer HS (0 : Fin 100)) (4 : Fin 100) := by
    rw [orbit_stabilizer_zero, orbit_stabilizerChain_one_four]
    decide
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (a := (⟨4, mem_orbit_self 4⟩ : orbit (stabilizer HS (0 : Fin 100)) (4 : Fin 100)))).mpr
  apply is_one_pretransitive_iff.mpr
  have h84 : (8 : Fin 100) ≠ 4 := by decide
  refine IsPretransitive.of_orbit
    (x₀ := ⟨⟨8, h8⟩, fun h ↦ h84 (congrArg Subtype.val h)⟩) fun c ↦ ?_
  have hc : c.1.1 ∈ orbit (HS.stabilizerChain pointSequence 1) (4 : Fin 100) :=
    orbit_stabilizer_zero 4 ▸ c.1.2
  rw [orbit_stabilizerChain_one_four, Finset.mem_coe] at hc
  have hc4 : c.1.1 ≠ 4 := fun h ↦ (SubMulAction.mem_ofStabilizer_iff _ _).mp c.2 (Subtype.ext h)
  obtain ⟨i, hi⟩ := exists_restPoints_eq _ hc hc4
  obtain ⟨h0, h4, h8'⟩ := restWords_apply i
  refine ⟨⟨⟨(restWords i).prod, mem_stabilizer_iff.mpr h0⟩,
    mem_stabilizer_iff.mpr (Subtype.ext h4)⟩, ?_⟩
  exact Subtype.ext (Subtype.ext (h8'.trans hi))

end HS

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
