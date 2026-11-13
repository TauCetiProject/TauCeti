/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Gaschutz
public import TauCeti.GroupTheory.Complement.Containment
public import TauCeti.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Sylow

/-!
# Invariant complements under prime-power actions

Let a finite `q`-group act on a finite group `W`, preserving an abelian normal `p`-subgroup `N`,
where `p ≠ q`. If `N` has a complement in a Sylow `p`-subgroup of `W`, then it has an invariant
complement in `W`. The acting group's order need not be coprime to the order of `W`.

Gaschütz's theorem first supplies a complement in the semidirect product. A conjugate of this
complement contains the acting group, by
`Subgroup.IsComplement'.exists_isComplement'_and_le_of_not_dvd_card`. Pulling it back to `W`
then gives an invariant complement.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254, Section 1.
-/

public section

namespace Subgroup

open SemidirectProduct
open scoped IsMulCommutative

variable {W A : Type*} [Group W] [Group A] [Finite W] [Finite A]
    [MulDistribMulAction A W] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- An abelian normal `p`-subgroup complemented in a Sylow `p`-subgroup has an invariant
complement under every finite `q`-group action preserving it, provided `p ≠ q`.
No coprimality between the orders of the acting and ambient groups is required. -/
theorem exists_invariant_complement (N : Subgroup W) [N.Normal] [IsMulCommutative N]
    (hN : IsPGroup p N) (hA : IsPGroup q A) (hpq : p ≠ q)
    (hstable : ∀ a : A, ∀ n ∈ N, a • n ∈ N) (P : Sylow p W)
    (hlocal : ∃ K : Subgroup W, N.IsLocalComplement K P) :
    ∃ D : Subgroup W, N.IsComplement' D ∧ ∀ a : A, ∀ d ∈ D, a • d ∈ D := by
  let φ := MulDistribMulAction.toMulAut A W
  let i : W →* W ⋊[φ] A := inl
  let j : A →* W ⋊[φ] A := inr
  have hi : Function.Injective i := inl_injective
  have : (N.map i).Normal := N.normal_map_inl hstable
  have hcard : Nat.card (N.map i) = Nat.card N := card_map_of_injective hi
  obtain ⟨n, hncard⟩ := hN.exists_card_eq
  obtain ⟨m, hmcard⟩ := hA.exists_card_eq
  have hindex : (P.toSubgroup.map i).index = P.toSubgroup.index * Nat.card A := by
    rw [index_map_of_injective _ hi]
    congr 1
    rw [range_inl_eq_ker_rightHom, index_ker,
      MonoidHom.range_eq_top.mpr rightHom_surjective, card_top]
  have hcop : Nat.Coprime (P.toSubgroup.map i).index (Nat.card (N.map i)) := by
    rw [hindex, hcard, hncard, hmcard]
    exact ((Fact.out : p.Prime).coprime_pow_of_not_dvd P.not_dvd_index).mul_left
      (Nat.coprime_pow_primes _ _ (Fact.out : q.Prime) (Fact.out : p.Prime) hpq.symm)
  obtain ⟨K, hK⟩ := hlocal
  obtain ⟨D₀, hD₀⟩ := (hK.map hi).exists_isComplement'_of_coprime_index hcop
  have hq : ¬ q ∣ Nat.card (N.map i) := by
    rw [hcard, hncard]
    apply (Fact.out : q.Prime).coprime_iff_not_dvd.mp
    simpa only [pow_one] using Nat.coprime_pow_primes 1 n (Fact.out : q.Prime)
      (Fact.out : p.Prime) hpq.symm
  obtain ⟨D₁, hD₁, hj⟩ := hD₀.exists_isComplement'_and_le_of_not_dvd_card
    (hA.of_surjective j.rangeRestrict j.rangeRestrict_surjective) hq
  refine ⟨D₁.comap i, hD₁.of_map hi, ?_⟩
  intro a d hd
  have ha : j a ∈ D₁ := hj ⟨a, rfl⟩
  have he : i (a • d) = j a * i d * (j a)⁻¹ := by
    exact (inl_aut a d).trans (by rw [map_inv])
  apply mem_comap.mpr
  rw [he]
  exact D₁.mul_mem (D₁.mul_mem ha hd) (D₁.inv_mem ha)

end Subgroup
