/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.G2

/-!
# Double root chains

For a finite reduced crystallographic root pairing whose Cartan integers lie in
`{-2, -1, 0, 1, 2}`, a double chain `β, α + β, 2α + β` determines its descending
coefficients, pairings, and the non-root sums needed in the Chevalley commutator formula.

The pairing bound is explicit rather than bundled in `RootPairing.IsNotG2`, since that
Mathlib class also requires irreducibility. Thus these results apply to reducible pairings
and integral root data as well. For an `IsNotG2` pairing, supply
`RootPairing.IsNotG2.pairingIn_mem_zero_one_two`. The exclusion of `β + (2α + β)`
requires no pairing bound.

The proofs use Mathlib's root-string identities and reducedness API.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  (hbound : ∀ i j, P.pairingIn ℤ i j ∈ ({-2, -1, 0, 1, 2} : Set ℤ))

include hbound

omit [P.IsReduced] in
/-- If every Cartan integer lies between minus two and two, each root string has
ascending and descending coefficients summing to at most two.
This generalizes Mathlib's `RootPairing.chainBotCoeff_add_chainTopCoeff_le_two` in
`Mathlib.LinearAlgebra.RootSystem.Finite.G2` from `IsNotG2` to an explicit pairing bound. -/
theorem chainBotCoeff_add_chainTopCoeff_le_two_of_pairing_bound (α β : ι) :
    P.chainBotCoeff α β + P.chainTopCoeff α β ≤ 2 := by
  by_cases hli : LinearIndependent R ![P.root α, P.root β]
  · rw [← Int.ofNat_le, Nat.cast_add, Nat.cast_ofNat,
      P.chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx hli]
    have := hbound (P.chainTopIdx α β) α
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    omega
  · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, hli]

/-- In a double chain with Cartan integers bounded by two, the descending coefficient
at the initial root is zero. -/
theorem chainBotCoeff_eq_zero_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) : P.chainBotCoeff α β = 0 := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have htop : 2 ≤ P.chainTopCoeff α β := by
    apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli).1
    exact ⟨δ, by rw [hδ, hγ]; abel⟩
  have := P.chainBotCoeff_add_chainTopCoeff_le_two_of_pairing_bound hbound α β
  omega

/-- In a double chain with Cartan integers bounded by two, the descending coefficient
at the middle root is one. -/
theorem chainBotCoeff_eq_one_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) : P.chainBotCoeff α γ = 1 := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  rw [P.chainBotCoeff_of_add hli (hγ.trans (add_comm _ _)),
    P.chainBotCoeff_eq_zero_of_double_chain hbound hγ hδ]

/-- The Cartan pairings along a double chain with Cartan integers bounded by two are
`⟨β, α∨⟩ = -2` and `⟨α, β∨⟩ = -1`. -/
theorem pairing_eq_neg_two_and_pairing_eq_neg_one_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) :
    P.pairing β α = -2 ∧ P.pairing α β = -1 := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hbot := P.chainBotCoeff_eq_zero_of_double_chain hbound hγ hδ
  have htop : P.chainTopCoeff α β = 2 := by
    have hpos := P.one_le_chainTopCoeff_of_root_add_mem ⟨δ, hδ⟩
    have hstep := P.chainTopCoeff_of_add hli (hγ.trans (add_comm _ _))
    have htotal := P.chainBotCoeff_add_chainTopCoeff_le_two_of_pairing_bound hbound α β
    omega
  have hβα : P.pairingIn ℤ β α = -2 := by
    have := P.chainBotCoeff_sub_chainTopCoeff hli
    simpa [hbot, htop] using this.symm
  have hne : P.root α ≠ P.root β := hli.injective.ne (by decide : (0 : Fin 2) ≠ 1)
  have hneg : P.root α ≠ -P.root β := by
    intro heq
    apply P.zero_notMem_range_root
    exact ⟨γ, by rw [hγ, heq, neg_add_cancel]⟩
  have hp := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' α β hne hneg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk_zero_zero, Prod.mk_one_one,
    Prod.mk_eq_zero, Prod.mk_eq_one, Prod.mk.injEq] at hp
  have hαβ : P.pairingIn ℤ α β = -1 := by omega
  constructor
  · simpa using (P.algebraMap_pairingIn ℤ β α).symm.trans
      (congrArg (algebraMap ℤ R) hβα)
  · simpa using (P.algebraMap_pairingIn ℤ α β).symm.trans
      (congrArg (algebraMap ℤ R) hαβ)

omit [Finite ι] [P.IsReduced] [IsDomain R] in
/-- A vector whose coroot evaluation lies outside the possible Cartan pairings is
neither a root nor zero. -/
theorem notMem_range_root_and_ne_zero_of_coroot_notMem (α : ι)
    {x : M} (hx : P.coroot' α x ∉ ({-2, -1, 0, 1, 2} : Set R)) :
    x ∉ Set.range P.root ∧ x ≠ 0 := by
  constructor
  · rintro ⟨ε, rfl⟩
    apply hx
    have hb := hbound ε α
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb ⊢
    rw [root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ ε α]
    rcases hb with hb | hb | hb | hb | hb <;> simp [hb]
  · intro hz
    apply hx
    simp [hz]

/-- The sum `α + δ`, where `δ = 2α + β` is the last root of a double chain with
Cartan integers bounded by two, is neither a root nor zero. -/
theorem root_add_last_notMem_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) :
    P.root α + P.root δ ∉ Set.range P.root ∧ P.root α + P.root δ ≠ 0 := by
  have hp := (P.pairing_eq_neg_two_and_pairing_eq_neg_one_of_double_chain hbound hγ hδ).1
  have heval : P.coroot' α (P.root α + P.root δ) = 4 := by
    norm_num [hδ, hγ, map_add, hp]
  exact P.notMem_range_root_and_ne_zero_of_coroot_notMem hbound α (by norm_num [heval])

/-- The sum `β + γ` of the initial and middle roots of a double chain with Cartan
integers bounded by two is neither a root nor zero. -/
theorem root_initial_add_middle_notMem_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) :
    P.root β + P.root γ ∉ Set.range P.root ∧ P.root β + P.root γ ≠ 0 := by
  have hp := (P.pairing_eq_neg_two_and_pairing_eq_neg_one_of_double_chain hbound hγ hδ).2
  have heval : P.coroot' β (P.root β + P.root γ) = 3 := by
    norm_num [hγ, map_add, hp]
  exact P.notMem_range_root_and_ne_zero_of_coroot_notMem hbound β (by norm_num [heval])

omit hbound [Finite ι] [P.IsCrystallographic] in
/-- The sum of the initial and last roots of a double chain is twice its middle root,
and hence is neither a root nor zero. No bound on Cartan integers is needed. -/
theorem root_initial_add_last_notMem_of_double_chain {α β γ δ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ) :
    P.root β + P.root δ ∉ Set.range P.root ∧ P.root β + P.root δ ≠ 0 := by
  let : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  let : HasUniqueDiv M := .of_isTorsionFree R M
  have heq : P.root β + P.root δ = 2 • P.root γ := by
    rw [hδ, hγ]
    abel
  rw [heq]
  exact ⟨P.nsmul_notMem_range_root, smul_ne_zero (by decide : (2 : ℕ) ≠ 0) (P.ne_zero γ)⟩

end RootPairing
