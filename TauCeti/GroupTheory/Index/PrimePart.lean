/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Prime parts of subgroup indices

If the order of a subgroup is prime to `p`, its index has the same `p`-part as the order of
the ambient group. This arithmetic constraint on indices gives dimension constraints on
induced representations.

The `ℓ`-adic valuation of the index is antitone along inclusions of subgroups of nonzero index
(`Subgroup.padicValNat_index_le_of_le`), and the valuation of the index of a subgroup `A` is the
sum of the valuations of its relative index in a larger subgroup `B` and of the index of `B`
(`Subgroup.padicValNat_relIndex_add_padicValNat_index`), as an identity in `ℕ∞`.

If every element of the group has a power `g ^ q ^ n` in a subgroup of finite index, then every
prime factor of the index divides `q`, so the index divides a power of `q`
(`Subgroup.exists_index_dvd_pow_of_forall_exists_pow_pow_mem`). For a normal subgroup this says
that a finite quotient in which every element has `q`-power order has order dividing a power of
`q` (`isPGroup_iff_card_dvd_pow`); the subgroup need not be normal here.
-/

public section

namespace Subgroup

/-- The index of a subgroup of order prime to `p` has the same `p`-part as the order of the
ambient group. No primality of `p` or finiteness of the group is needed. -/
theorem ordProj_index_eq_ordProj_natCard {G : Type*} [Group G]
    (S : Subgroup G) {p : ℕ} (hS : ¬ p ∣ Nat.card S) :
    ordProj[p] S.index = ordProj[p] (Nat.card G) := by
  have hS₀ : Nat.card S ≠ 0 := fun h ↦ hS (h ▸ dvd_zero p)
  rcases eq_or_ne S.index 0 with h | h
  · simp [← S.card_mul_index, h]
  rw [← S.card_mul_index, Nat.factorization_mul hS₀ h, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hS, zero_add]

/-- The `ℓ`-adic valuation of the index of a subgroup is at most that of any subgroup it contains,
provided the smaller subgroup has nonzero index. -/
theorem padicValNat_index_le_of_le {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B)
    (hA : A.index ≠ 0) (ℓ : ℕ) :
    padicValNat ℓ B.index ≤ padicValNat ℓ A.index := by
  have hdvd := Subgroup.index_dvd_of_le h
  rcases eq_or_ne ℓ 1 with rfl | hℓ
  · simp [Nat.padicValNat_def]
  rw [Nat.padicValNat_def, Nat.padicValNat_def,
    ← Nat.pow_dvd_iff_le_multiplicity hℓ hA]
  exact (pow_multiplicity_dvd ℓ B.index).trans hdvd

/-- For subgroups `A ≤ B` with `A` of nonzero index, the `ℓ`-adic valuation of the index of `A`
is the sum of the valuations of the relative index of `A` in `B` and of the index of `B`. -/
theorem padicValNat_relIndex_add_padicValNat_index {G : Type*} [Group G] {A B : Subgroup G}
    (h : A ≤ B) (hA : A.index ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] :
    (padicValNat ℓ (A.relIndex B) : ℕ∞) + padicValNat ℓ B.index = padicValNat ℓ A.index := by
  have hmul := A.relIndex_mul_index h
  rw [← hmul] at hA ⊢
  simp only [Nat.padicValNat_def]
  rw [Nat.multiplicity_mul (left_ne_zero_of_mul hA) (right_ne_zero_of_mul hA), Nat.cast_add]

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
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup ⟨f g, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    have hcop : (q ^ n).Coprime (orderOf (f g)) := hk ▸
      ((Nat.coprime_comm.mp (hpp.coprime_iff_not_dvd.mpr hpq)).pow n k)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm, ← map_pow, ← map_pow]
    exact mem_map_of_mem f (pow_mem hn m)
  have hker : f.ker ≤ H := by simpa [f] using H.normalCore_le
  exact P.not_dvd_index ((Nat.dvd_of_mem_primeFactors hp).trans
    (H.index_map_eq (QuotientGroup.mk'_surjective _) hker ▸ index_dvd_of_le hPH))

end Subgroup
