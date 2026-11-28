/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

import TauCeti.GroupTheory.SpecificGroups.Cyclic.ActionKernel

/-!
# Kernel index of an action on a prime-order group

Let a group `G` act by additive automorphisms on an additive group `A` of prime order `p`. Since
`A` is cyclic of order `p`, the kernel of `DistribMulAction.toAddAut G A` has index dividing
`φ(p) = p - 1`, which is coprime to `p`. More generally, for any homomorphism `χ : G →* H` into a
group whose order is coprime to `p` (such as `(ZMod p)ˣ` for the mod-`p` cyclotomic character), the
joint kernel of `(DistribMulAction.toAddAut G A).prod χ` has index coprime to `p`.

## Main results

* `TauCeti.index_ker_toAddAut_dvd_sub_one`: the kernel of `DistribMulAction.toAddAut G A` has index
  dividing `p - 1` when `Nat.card A = p` is prime.
* `TauCeti.coprime_index_ker_prod_toAddAut`: the kernel of `(DistribMulAction.toAddAut G A).prod χ`
  has index coprime to `p` whenever `Nat.card A = p` is prime and `p.Coprime (Nat.card H)`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/ClassField/GreenbergWiles/RelationsModL.lean`
(`New.RelationSetting.coprime_index_ker_torsionAction`), generalized from the Galois action on
`M[ℓ]` and `(ZMod ℓ)ˣ` to any group acting on an additive group of prime order `p` paired with a
homomorphism into a group of order coprime to `p`.
-/

@[expose] public section

namespace TauCeti

/-- If a group `G` acts by additive automorphisms on an additive group `A` of prime order `p`, the
kernel of `DistribMulAction.toAddAut G A` has index dividing `p - 1`. -/
theorem index_ker_toAddAut_dvd_sub_one (G A : Type*) [Group G] [AddGroup A]
    [DistribMulAction G A] {p : ℕ} (hp : p.Prime) (hA : Nat.card A = p) :
    (DistribMulAction.toAddAut G A).ker.index ∣ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hmul : Nat.card (Multiplicative A) = p := by
    simpa [Nat.card_congr Multiplicative.toAdd] using hA
  have : Finite (Multiplicative A) := Nat.finite_of_card_ne_zero (hmul ▸ hp.ne_zero)
  have hcyc : IsCyclic (Multiplicative A) := isCyclic_of_prime_card hmul
  have : IsAddCyclic A := by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    exact ⟨⟨Multiplicative.toAdd g, fun a ↦ hg (Multiplicative.ofAdd a)⟩⟩
  have hker : (DistribMulAction.toAddAut G A).ker = (MulAction.toPermHom G A).ker := by
    ext g
    simp only [MonoidHom.mem_ker, Equiv.ext_iff, MulAction.toPermHom_apply, Equiv.Perm.one_apply]
    constructor
    · intro h a
      exact DFunLike.congr_fun (congrArg Multiplicative.toAdd h) a
    · intro h
      exact Multiplicative.toAdd.injective (AddEquiv.ext h)
  rw [hker, ← Nat.totient_prime hp, ← hA]
  exact index_ker_toPermHom_dvd_totient G A

/-- If a group `G` acts by additive automorphisms on an additive group `A` of prime order `p` and
`χ : G →* H` is a homomorphism into a group whose order is coprime to `p`, then the kernel of
`(DistribMulAction.toAddAut G A).prod χ` has index coprime to `p`. -/
theorem coprime_index_ker_prod_toAddAut {G A H : Type*} [Group G] [AddGroup A]
    [DistribMulAction G A] [Group H] {p : ℕ} (hp : p.Prime) (hA : Nat.card A = p)
    (χ : G →* H) (hH : p.Coprime (Nat.card H)) :
    p.Coprime ((DistribMulAction.toAddAut G A).prod χ).ker.index := by
  have : Fact p.Prime := ⟨hp⟩
  have hmul : Nat.card (Multiplicative A) = p := by
    simpa [Nat.card_congr Multiplicative.toAdd] using hA
  have : Finite (Multiplicative A) := Nat.finite_of_card_ne_zero (hmul ▸ hp.ne_zero)
  have haut : Nat.card (Multiplicative (AddAut A)) = p - 1 := by
    rw [← Nat.card_congr (MulAutMultiplicative A).toEquiv,
      (isCyclic_of_prime_card hmul).card_mulAut, hmul, Nat.totient_prime hp]
  have hdvd : ((DistribMulAction.toAddAut G A).prod χ).ker.index ∣ (p - 1) * Nat.card H := by
    rw [Subgroup.index_ker, ← haut, ← Nat.card_prod]
    exact Subgroup.card_subgroup_dvd_card _
  have hcop : p.Coprime (p - 1) :=
    (Nat.coprime_self_sub_right hp.one_le).mpr (Nat.coprime_one_right p)
  exact (hcop.mul_right hH).of_dvd_right hdvd

end TauCeti
