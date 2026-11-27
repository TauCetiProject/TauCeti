/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Sylow

/-!
# Indices dividing a power of `q`

If every element of a group has a power `g ^ q ^ n` in a subgroup of finite index, then every
prime factor of the index divides `q`, so the index divides a power of `q`
(`Subgroup.exists_index_dvd_pow_of_forall_exists_pow_pow_mem`). For a normal subgroup this says
that a finite quotient in which every element is killed by some power of `q` (its order divides a
power of `q`) has order dividing a power of `q` (`isPGroup_iff_card_dvd_pow`); the subgroup need
not be normal here, and `q` need not be prime. This bounds the indices of stabilisers, and with
them the cover multiplicities of `Subgroup.coverMultiplicity`, when conjugates of a level have
`q`-power powers in a larger level.
-/

public section

namespace Subgroup

/-- If every element `g` of `G` has a power `g ^ q ^ n` in a subgroup `H` of finite index, then
every prime factor of the index of `H` divides `q`, so the index divides a power of `q`. Neither
primality of `q` nor a bound on `n` independent of `g` is needed. When `G` is a `p`-group for a
prime `p`, the powers `g ^ p ^ n` can be taken to be `1` and this is `IsPGroup.index`. -/
theorem exists_index_dvd_pow_of_forall_exists_pow_pow_mem {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] {q : ℕ} (h : ∀ g : G, ∃ n : ℕ, g ^ q ^ n ∈ H) :
    ∃ n : ℕ, H.index ∣ q ^ n := by
  -- For a prime `p ∤ q`, every element of a Sylow `p`-subgroup `P` of the finite quotient of `G`
  -- by the normal core of `H` is a power of its own `q ^ n`-th power, so `P` lies in the image
  -- of `H`, whose index is therefore prime to `p`.
  rcases eq_or_ne q 0 with rfl | hq
  · exact ⟨1, by simp⟩
  rw [Nat.exists_dvd_pow_iff H.index_ne_zero hq]
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  refine hpp.mem_primeFactors (by_contra fun hpq ↦ ?_) hq
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p (G ⧸ H.normalCore)) := inferInstance
  let f := QuotientGroup.mk' H.normalCore
  have hPH : (P : Subgroup (G ⧸ H.normalCore)) ≤ H.map f := by
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨n, hn⟩ := h g
    have hcop := P.isPGroup.orderOf_coprime ((hpp.coprime_iff_not_dvd.mpr hpq).pow_right n)
      ⟨f g, hx⟩
    rw [Subgroup.orderOf_mk] at hcop
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop.symm
    rw [← hm, ← map_pow, ← map_pow]
    exact mem_map_of_mem f (pow_mem hn m)
  have hker : f.ker ≤ H := by simpa [f] using H.normalCore_le
  exact P.not_dvd_index ((Nat.dvd_of_mem_primeFactors hp).trans
    (H.index_map_eq (QuotientGroup.mk'_surjective _) hker ▸ index_dvd_of_le hPH))

end Subgroup
