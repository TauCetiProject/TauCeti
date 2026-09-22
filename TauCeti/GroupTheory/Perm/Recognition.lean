/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import TauCeti.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.GroupAction.Jordan

/-!
# Recognizing cycles and transpositions in a permutation group

This file supplies recognition steps that read off structure of a permutation group from cycle
data. A transitive subgroup of a finite symmetric group whose degree is prime contains a full
cycle. A permutation with exactly one 2-cycle and all its other cycles of odd length has an odd
power that is a transposition, and the exponent is given explicitly as the product of those odd
lengths.

Both feed the recognition of a full symmetric group, which needs a primitive group containing a
transposition: a transitive group of prime degree is primitive, and a transposition is what the
second result produces. In the Galois-theoretic application the cycle pattern of the element fed
to the second result is the degree pattern of a factorization of a polynomial modulo a prime, read
through the Frobenius element.

A subgroup of `Sₙ`, `n ≥ 5`, of index less than `n` contains `Aₙ`. This recognizes the large
subgroups in the low-degree classification, where the order of a subgroup bounds its index.

## Main results

* `TauCeti.card_dvd_natCard_and_natCard_dvd_factorial_of_isPretransitive`: the order of a
  transitive permutation group of degree `n` is a multiple of `n` and a divisor of `n !`.
* `TauCeti.exists_isCycle_mem_of_isPretransitive_of_prime_card`: a transitive permutation group
  of prime degree contains a full cycle.
* `TauCeti.subgroup_eq_top_of_isPretransitive_of_prime_card_of_isSwap_mem`: a transitive
  permutation group of prime degree that contains a transposition is the full symmetric group.
* `TauCeti.alternatingGroup_le_of_isPretransitive_of_orderOf_eq_three`: a transitive subgroup of
  `S₅` containing an element of order `3` contains `A₅`.
* `TauCeti.subgroup_eq_top_of_isPretransitive_of_orderOf_eq_six`: a transitive subgroup of `S₅`
  containing an element of order `6` is the full symmetric group.
* `TauCeti.alternatingGroup_le_of_index_lt`: a subgroup of `Sₙ`, `n ≥ 5`, of index less than
  `n` contains `Aₙ`.
* `Equiv.Perm.isSwap_pow_prod_erase_two_cycleType_and_odd`: if a permutation has exactly one
  2-cycle and all its other cycles have odd length, an explicit odd power is a transposition.
* `Equiv.Perm.exists_odd_isSwap_pow`: the corresponding existential form.
-/

public section

namespace TauCeti

open MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- The order of a transitive permutation group on a nonempty finite set `α` is a multiple of the
degree `Fintype.card α`, by `TauCeti.natCard_dvd_natCard_of_isPretransitive`, and a divisor of
`(Fintype.card α)!`, by Lagrange's theorem. -/
theorem card_dvd_natCard_and_natCard_dvd_factorial_of_isPretransitive
    (G : Subgroup (Equiv.Perm α)) [IsPretransitive G α] [Nonempty α] :
    Fintype.card α ∣ Nat.card G ∧ Nat.card G ∣ (Fintype.card α).factorial := by
  classical
  refine ⟨by simpa using natCard_dvd_natCard_of_isPretransitive G (X := α), ?_⟩
  simpa [Fintype.card_perm] using Subgroup.card_subgroup_dvd_card G

/-- A transitive permutation group of prime degree contains a full cycle.

The returned permutation has order and support cardinality equal to the degree, so its support
is all of `α`. This is intended as a prime-degree recognition input for the low-degree
classification and for the prime-degree branch of the `Sₙ` realization argument.
-/
theorem exists_isCycle_mem_of_isPretransitive_of_prime_card
    {G : Subgroup (Equiv.Perm α)} (hG : IsPretransitive G α)
    (hp : Nat.Prime (Fintype.card α)) :
    ∃ g : Equiv.Perm α, g ∈ G ∧ g.IsCycle ∧ g.support = Finset.univ := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let a : α := Classical.choice (Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hp.ne_zero))
  have horbit : orbit G a = Set.univ :=
    (isPretransitive_iff_orbit_eq_univ a).mp hG
  have hcard : Fintype.card α ∣ Fintype.card G := by
    refine ⟨Fintype.card (stabilizer G a), ?_⟩
    simpa [horbit, Nat.mul_comm] using
      (card_orbit_mul_card_stabilizer_eq_card_group (G := G) a).symm
  let _ : Fact (Fintype.card α).Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) hcard
  have horder : orderOf (g : Equiv.Perm α) = Fintype.card α :=
    (Subgroup.orderOf_coe g).trans hg
  have hcycle : (g : Equiv.Perm α).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order'' hp horder
  have hsupport : (g : Equiv.Perm α).support = Finset.univ :=
    Finset.eq_univ_of_card (g : Equiv.Perm α).support (hcycle.orderOf.symm.trans horder)
  exact ⟨g, g.property, hcycle, hsupport⟩

/-- A transitive subgroup of a symmetric group of prime degree that contains a transposition is
the full symmetric group, the prime-degree form of Jordan's transposition recognition theorem.

This recognition result identifies Galois groups from an irreducible polynomial and a
factorization pattern exhibiting a transposition. -/
theorem subgroup_eq_top_of_isPretransitive_of_prime_card_of_isSwap_mem
    {β : Type*} [DecidableEq β] {G : Subgroup (Equiv.Perm β)} (hG : IsPretransitive G β)
    (hp : Nat.Prime (Nat.card β)) (g : Equiv.Perm β) (hgSwap : g.IsSwap) (hg : g ∈ G) :
    G = ⊤ := by
  have : Finite β := Nat.finite_of_card_ne_zero hp.ne_zero
  let _ : IsPretransitive G β := hG
  exact Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (IsPreprimitive.of_prime_card hp) g hgSwap hg

/-- A subgroup of the symmetric group on `n ≥ 5` points whose index is less than `n` contains
the alternating group. -/
theorem alternatingGroup_le_of_index_lt (hα : 5 ≤ Nat.card α)
    {H : Subgroup (Equiv.Perm α)} (hH : H.index < Nat.card α) : alternatingGroup α ≤ H := by
  -- The bound on the normal core follows the proof of Mathlib's
  -- `Subgroup.normal_of_index_eq_minFac_card`.
  have hcore : H.normalCore.index ∣ Nat.factorial H.index := by
    rw [Subgroup.normalCore_eq_ker, Subgroup.index_ker, Subgroup.index_eq_card, ← Nat.card_perm]
    exact Subgroup.card_subgroup_dvd_card (toPermHom (Equiv.Perm α) (Equiv.Perm α ⧸ H)).range
  have hne : Nontrivial H.normalCore := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    rw [hbot, Subgroup.index_bot, Nat.card_perm] at hcore
    exact (Nat.factorial_lt (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)).2 hH |>.not_ge
      (Nat.le_of_dvd (Nat.factorial_pos _) hcore)
  exact (Equiv.Perm.alternatingGroup_le_of_normal hα hne).trans H.normalCore_le

/-- If a permutation has exactly one cycle of length two and every other cycle has odd length,
then raising it to the product of those other cycle lengths gives a transposition.

The exponent is itself odd. This is the cycle-theoretic step used to turn a factorization pattern
with one quadratic factor and only odd-degree remaining factors into a transposition in a Galois
group. -/
theorem _root_.Equiv.Perm.isSwap_pow_prod_erase_two_cycleType_and_odd {σ : Equiv.Perm α}
    (htwo : σ.cycleType.count 2 = 1)
    (hodd : ∀ n ∈ σ.cycleType, n ≠ 2 → Odd n) :
    (σ ^ (σ.cycleType.erase 2).prod).IsSwap ∧ Odd (σ.cycleType.erase 2).prod := by
  have hmem : 2 ∈ σ.cycleType := Multiset.count_pos.mp (by omega)
  obtain ⟨c, τ, hσ, hdisj, hc, hcard⟩ := Equiv.Perm.mem_cycleType_iff.mp hmem
  have hcSwap : c.IsSwap := Equiv.Perm.card_support_eq_two.mp hcard
  have hcycleType : σ.cycleType = {2} + τ.cycleType := by
    rw [hσ, hdisj.cycleType_mul, hc.cycleType, hcard]
  have herase : σ.cycleType.erase 2 = τ.cycleType := by
    rw [hcycleType]
    simp
  have htwoτ : 2 ∉ τ.cycleType := by
    rw [← Multiset.count_eq_zero]
    have : 1 + τ.cycleType.count 2 = 1 := by
      simpa [hcycleType] using htwo
    omega
  have hoddτ : ∀ n ∈ τ.cycleType, Odd n := by
    intro n hn
    have hnσ : n ∈ σ.cycleType := by
      rw [hcycleType, Multiset.mem_add]
      exact Or.inr hn
    exact (hodd n hnσ) (fun hn2 ↦ htwoτ (hn2 ▸ hn))
  have hkodd : Odd τ.cycleType.prod :=
    Multiset.prod_induction Odd τ.cycleType (fun _ _ ha hb ↦ ha.mul hb) (by simp) hoddτ
  have hτpow : τ ^ τ.cycleType.prod = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType]
    exact Multiset.lcm_dvd.mpr fun _ hn ↦ Multiset.dvd_prod hn
  have hcpow : c ^ τ.cycleType.prod = c := by
    have hmod : τ.cycleType.prod ≡ 1 [MOD orderOf c] := by
      rw [hcSwap.orderOf, Nat.ModEq, Nat.odd_iff.mp hkodd]
    exact ((pow_eq_pow_iff_modEq).mpr hmod).trans (pow_one c)
  rw [herase, hσ, hdisj.commute.mul_pow, hcpow, hτpow, mul_one]
  exact ⟨hcSwap, hkodd⟩

/-- A permutation with exactly one 2-cycle and all remaining cycle lengths odd has an odd power
that is a transposition. -/
theorem _root_.Equiv.Perm.exists_odd_isSwap_pow {σ : Equiv.Perm α}
    (htwo : σ.cycleType.count 2 = 1)
    (hodd : ∀ n ∈ σ.cycleType, n ≠ 2 → Odd n) :
    ∃ k, Odd k ∧ (σ ^ k).IsSwap := by
  have h := σ.isSwap_pow_prod_erase_two_cycleType_and_odd htwo hodd
  exact ⟨(σ.cycleType.erase 2).prod, h.2, h.1⟩

/-- A permutation of order `6` on five points has cycle type `(2, 3)`: it is the product of a
transposition and a three-cycle. -/
private theorem cycleType_eq_two_three_of_orderOf_eq_six {σ : Equiv.Perm α}
    (hcard : Fintype.card α = 5) (hσ : orderOf σ = 6) : σ.cycleType = {2, 3} := by
  have hsum : σ.cycleType.sum ≤ 5 := by
    have := σ.sum_cycleType_le
    rwa [hcard] at this
  have hdvd : ∀ n ∈ σ.cycleType, n = 2 ∨ n = 3 := by
    intro n hn
    have hn2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have hnd : n ∣ 6 := by
      have := Equiv.Perm.dvd_of_mem_cycleType hn
      rwa [hσ] at this
    have hn6 : n ≤ 6 := Nat.le_of_dvd (by omega) hnd
    interval_cases n
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hnd (by decide)
    · exact absurd hnd (by decide)
    · obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hn
      rw [ht, Multiset.sum_cons] at hsum
      omega
  have hex2 : (2 : ℕ) ∈ σ.cycleType := by
    by_contra h
    have hall : ∀ n ∈ σ.cycleType, n ∣ 3 := by
      intro n hn
      obtain rfl | rfl := hdvd n hn
      · exact absurd hn h
      · exact dvd_rfl
    have h3 : σ.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.mpr hall
    rw [Equiv.Perm.lcm_cycleType, hσ] at h3
    omega
  have hex3 : (3 : ℕ) ∈ σ.cycleType := by
    by_contra h
    have hall : ∀ n ∈ σ.cycleType, n ∣ 2 := by
      intro n hn
      obtain rfl | rfl := hdvd n hn
      · exact dvd_rfl
      · exact absurd hn h
    have h2 : σ.cycleType.lcm ∣ 2 := Multiset.lcm_dvd.mpr hall
    rw [Equiv.Perm.lcm_cycleType, hσ] at h2
    omega
  obtain ⟨m1, hm1⟩ := Multiset.exists_cons_of_mem hex3
  have h2mem : (2 : ℕ) ∈ m1 := by
    rw [hm1] at hex2
    simpa using hex2
  obtain ⟨m2, hm2⟩ := Multiset.exists_cons_of_mem h2mem
  have hm2' : m2 = 0 := by
    by_contra hne
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hx
    have hx2 : 2 ≤ x := Equiv.Perm.two_le_of_mem_cycleType (by rw [hm1, hm2]; simp [hx])
    rw [hm1, hm2, ht] at hsum
    simp only [Multiset.sum_cons] at hsum
    omega
  rw [hm1, hm2, hm2']
  exact Multiset.pair_comm 3 2

/-- A permutation of order `3` on five points is a three-cycle. -/
private theorem isThreeCycle_of_orderOf_eq_three {σ : Equiv.Perm α}
    (hcard : Fintype.card α = 5) (hσ : orderOf σ = 3) : Equiv.Perm.IsThreeCycle σ := by
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (hσ ▸ Nat.prime_three)
  have hn0 : n = 0 := by
    have hsum := σ.sum_cycleType_le
    rw [hn, hσ, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, hcard] at hsum
    omega
  simp [Equiv.Perm.IsThreeCycle, hn, hσ, hn0]

/-- **A transitive subgroup of `S₅` containing an element of order `3` contains the alternating
group.** On five points an element of order `3` is a three-cycle, so a primitive criterion
applies: a primitive subgroup of `Sₙ`, `n ≥ 3`, containing a three-cycle contains `Aₙ`. -/
theorem alternatingGroup_le_of_isPretransitive_of_orderOf_eq_three
    (hcard : Fintype.card α = 5) {G : Subgroup (Equiv.Perm α)} (hG : IsPretransitive G α)
    {σ : Equiv.Perm α} (hσ : orderOf σ = 3) (hg : σ ∈ G) : alternatingGroup α ≤ G := by
  let _ : IsPretransitive G α := hG
  refine Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (IsPreprimitive.of_prime_card ?_) (isThreeCycle_of_orderOf_eq_three hcard hσ) hg
  rw [Nat.card_eq_fintype_card, hcard]
  exact Nat.prime_five

omit [DecidableEq α] in
/-- **A transitive subgroup of `S₅` containing an element of order `6` is the full symmetric
group.** On five points an element of order `6` is the product of a transposition and a
three-cycle, so some odd power of it is a transposition and the transposition criterion
applies. -/
theorem subgroup_eq_top_of_isPretransitive_of_orderOf_eq_six
    (hcard : Fintype.card α = 5) {G : Subgroup (Equiv.Perm α)} (hG : IsPretransitive G α)
    {σ : Equiv.Perm α} (hσ : orderOf σ = 6) (hg : σ ∈ G) : G = ⊤ := by
  classical
  have hct : σ.cycleType = {2, 3} := cycleType_eq_two_three_of_orderOf_eq_six hcard hσ
  obtain ⟨k, -, hswap⟩ := Equiv.Perm.exists_odd_isSwap_pow (σ := σ) (by simp [hct])
    fun n hn hn2 => by
    rw [hct] at hn
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hn
    obtain rfl | rfl := hn
    · exact absurd rfl hn2
    · exact ⟨1, by omega⟩
  refine subgroup_eq_top_of_isPretransitive_of_prime_card_of_isSwap_mem hG ?_ (σ ^ k) hswap
    (pow_mem hg k)
  rw [Nat.card_eq_fintype_card, hcard]
  exact Nat.prime_five

end TauCeti
