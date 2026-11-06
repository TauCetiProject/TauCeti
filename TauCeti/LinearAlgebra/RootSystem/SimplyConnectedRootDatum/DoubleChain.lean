/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational

/-!
# Double root chains in the pinned datum

If both `α + β` and `2α + β` are roots outside type `G₂`, the `α`-string through `β`
starts at `β` and ends at `2α + β`. This determines the two structure-constant magnitudes
in the corresponding two-factor Chevalley commutator. The further sums needed in that
commutator are neither roots nor zero.

The root-string bounds are supplied by Mathlib's `RootPairing.IsNotG2` API, applied to the
rational scalar extension of the pinned datum.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace TauCeti.DynkinType

variable {t : DynkinType} {ht : t.Valid} (h : t ≠ .G2)

local notation "P" => t.simplyConnectedRootDatum ht

include h

/-- Outside `G₂`, the ascending and descending root-string coefficients sum to at most two. -/
theorem chainBotCoeff_add_chainTopCoeff_le_two (α β : Fin t.numRoots) :
    (P).chainBotCoeff α β + (P).chainTopCoeff α β ≤ 2 := by
  let := t.isNotG2_rationalRootSystem ht h
  simpa using (t.rationalRootSystem ht).chainBotCoeff_add_chainTopCoeff_le_two α β

/-- In a double chain, the descending coefficient at its initial root is zero. -/
theorem chainBotCoeff_eq_zero_of_double_chain {α β γ δ : Fin t.numRoots}
    (hγ : (P).root γ = (P).root α + (P).root β)
    (hδ : (P).root δ = (P).root α + (P).root γ) : (P).chainBotCoeff α β = 0 := by
  let := t.isReduced_simplyConnectedRootDatum ht
  have hli := (P).linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have htop : 2 ≤ (P).chainTopCoeff α β := by
    apply ((P).root_add_nsmul_mem_range_iff_le_chainTopCoeff hli).1
    exact ⟨δ, by rw [hδ, hγ]; abel⟩
  have := chainBotCoeff_add_chainTopCoeff_le_two (ht := ht) h α β
  omega

/-- In a double chain, the descending coefficient at the middle root is one. -/
theorem chainBotCoeff_eq_one_of_double_chain {α β γ δ : Fin t.numRoots}
    (hγ : (P).root γ = (P).root α + (P).root β)
    (hδ : (P).root δ = (P).root α + (P).root γ) : (P).chainBotCoeff α γ = 1 := by
  let := t.isReduced_simplyConnectedRootDatum ht
  have hli := (P).linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  rw [(P).chainBotCoeff_of_add hli (hγ.trans (add_comm _ _)),
    chainBotCoeff_eq_zero_of_double_chain h hγ hδ]

/-- The Cartan integers along a double chain are `⟨β, α∨⟩ = -2` and `⟨α, β∨⟩ = -1`. -/
theorem pairings_of_double_chain {α β γ δ : Fin t.numRoots}
    (hγ : (P).root γ = (P).root α + (P).root β)
    (hδ : (P).root δ = (P).root α + (P).root γ) :
    (P).pairing β α = -2 ∧ (P).pairing α β = -1 := by
  let := t.isReduced_simplyConnectedRootDatum ht
  have hli := (P).linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hbot := chainBotCoeff_eq_zero_of_double_chain h hγ hδ
  have htop : (P).chainTopCoeff α β = 2 := by
    have hpos := (P).one_le_chainTopCoeff_of_root_add_mem ⟨δ, hδ⟩
    have hstep := (P).chainTopCoeff_of_add hli (hγ.trans (add_comm _ _))
    have hbound := chainBotCoeff_add_chainTopCoeff_le_two (ht := ht) h α β
    omega
  have hβα : (P).pairingIn ℤ β α = -2 := by
    have := (P).chainBotCoeff_sub_chainTopCoeff hli
    simpa [hbot, htop] using this.symm
  have hne : (P).root α ≠ (P).root β := hli.injective.ne (by decide : (0 : Fin 2) ≠ 1)
  have hneg : (P).root α ≠ -(P).root β := by
    intro heq
    apply (P).zero_notMem_range_root
    exact ⟨γ, by rw [hγ, heq, neg_add_cancel]⟩
  have hp := (P).pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' α β hne hneg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk_zero_zero, Prod.mk_one_one,
    Prod.mk_eq_zero, Prod.mk_eq_one, Prod.mk.injEq] at hp
  have hαβ : (P).pairingIn ℤ α β = -1 := by omega
  constructor
  · simpa using ((P).algebraMap_pairingIn ℤ β α).symm.trans
      (congrArg (algebraMap ℤ ℤ) hβα)
  · simpa using ((P).algebraMap_pairingIn ℤ α β).symm.trans
      (congrArg (algebraMap ℤ ℤ) hαβ)

/-- The sum of the initial short root and the last root of a double chain is neither a root
nor zero. -/
theorem root_add_last_notMem_of_double_chain {α β γ δ : Fin t.numRoots}
    (hγ : (P).root γ = (P).root α + (P).root β)
    (hδ : (P).root δ = (P).root α + (P).root γ) :
    (P).root α + (P).root δ ∉ Set.range (P).root ∧ (P).root α + (P).root δ ≠ 0 := by
  have hp := (pairings_of_double_chain h hγ hδ).1
  have heval : (P).coroot' α ((P).root α + (P).root δ) = 4 := by
    simp [hδ, hγ, map_add, hp]
  constructor
  · rintro ⟨ε, hε⟩
    let := t.isNotG2_rationalRootSystem ht h
    have hb := RootPairing.IsNotG2.pairingIn_mem_zero_one_two
      («P» := t.rationalRootSystem ht) ε α
    have heq := congrArg ((P).coroot' α) hε
    simp only [RootPairing.root_coroot'_eq_pairing, heval] at heq
    simp only [pairingIn_rationalRootSystem] at hb
    have heq' := (P).algebraMap_pairingIn ℤ ε α
    norm_num [heq] at heq'
    simp_all
  · intro hz
    simp [hz] at heval

/-- The sum of the initial long root and the middle root of a double chain is neither a root
nor zero. -/
theorem root_add_middle_notMem_of_double_chain {α β γ δ : Fin t.numRoots}
    (hγ : (P).root γ = (P).root α + (P).root β)
    (hδ : (P).root δ = (P).root α + (P).root γ) :
    (P).root β + (P).root γ ∉ Set.range (P).root ∧ (P).root β + (P).root γ ≠ 0 := by
  have hp := (pairings_of_double_chain h hγ hδ).2
  have heval : (P).coroot' β ((P).root β + (P).root γ) = 3 := by
    simp [hγ, map_add, hp]
  constructor
  · rintro ⟨ε, hε⟩
    let := t.isNotG2_rationalRootSystem ht h
    have hb := RootPairing.IsNotG2.pairingIn_mem_zero_one_two
      («P» := t.rationalRootSystem ht) ε β
    have heq := congrArg ((P).coroot' β) hε
    simp only [RootPairing.root_coroot'_eq_pairing, heval] at heq
    simp only [pairingIn_rationalRootSystem] at hb
    have heq' := (P).algebraMap_pairingIn ℤ ε β
    norm_num [heq] at heq'
    simp_all
  · intro hz
    simp [hz] at heval

omit h in
/-- The sum of the initial long root and the last root of a double chain is twice its middle
root, and hence is neither a root nor zero. This also holds in type `G₂`. -/
theorem root_add_last_notMem_of_root_eq_add {α β γ δ : Fin t.numRoots}
    (hγ : (P).root γ = (P).root α + (P).root β)
    (hδ : (P).root δ = (P).root α + (P).root γ) :
    (P).root β + (P).root δ ∉ Set.range (P).root ∧ (P).root β + (P).root δ ≠ 0 := by
  let := t.isReduced_simplyConnectedRootDatum ht
  let : HasUniqueDiv (Fin t.rank → ℤ) := .of_isTorsionFree ℤ _
  have heq : (P).root β + (P).root δ = 2 • (P).root γ := by
    rw [hδ, hγ]
    abel
  rw [heq]
  exact ⟨(P).nsmul_notMem_range_root, smul_ne_zero (by decide : (2 : ℕ) ≠ 0) ((P).ne_zero γ)⟩

end TauCeti.DynkinType
