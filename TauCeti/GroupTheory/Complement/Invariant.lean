/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Basic
public import TauCeti.GroupTheory.Complement.Gaschutz
public import TauCeti.GroupTheory.Complement.Containment
public import TauCeti.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Sylow

/-!
# Invariant complements under prime-power actions

Let a `q`-group act by automorphisms on a finite group `W`, preserving an abelian normal
`p`-subgroup `N`, where `p ≠ q`. If `N` has a complement in a Sylow `p`-subgroup of `W`, then
it has an invariant complement in `W`. The acting group need not be finite, and its order
need not be coprime to the order of `W`.

More generally, a complemented abelian normal subgroup whose order is not divisible by `q`
has an invariant complement under a finite `q`-group acting by automorphisms. Gaschütz's
theorem supplies a complement in the semidirect product. A conjugate of this complement
contains the acting group, by
`Subgroup.IsComplement'.exists_isComplement'_and_le_of_not_dvd_card`. Pulling it back to `W`
then gives an invariant complement. For finite `W`, passing to the finite image of the action
removes the finiteness assumption on the acting group.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254, Section 1.
-/

public section

namespace Subgroup

open SemidirectProduct
open scoped IsMulCommutative

variable {W A : Type*} [Group W] [Group A] [MulDistribMulAction A W]
    {q : ℕ} [Fact q.Prime]

/-- A complemented abelian normal subgroup whose order is not divisible by `q` has an
invariant complement under every action by automorphisms of a finite `q`-group preserving it.
No finiteness of the ambient group is required. -/
theorem IsComplement'.exists_invariant_complement_of_not_dvd_card [Finite A]
    {N K : Subgroup W} [N.Normal] [IsMulCommutative N] (hK : N.IsComplement' K)
    (hA : IsPGroup q A) (hN : ¬ q ∣ Nat.card N)
    (hstable : ∀ a : A, ∀ n ∈ N, a • n ∈ N) :
    ∃ D : Subgroup W, N.IsComplement' D ∧ ∀ a : A, ∀ d ∈ D, a • d ∈ D := by
  let φ := MulDistribMulAction.toMulAut A W
  let i : W →* W ⋊[φ] A := inl
  let j : A →* W ⋊[φ] A := inr
  have hi : Function.Injective i := inl_injective
  have : (N.map i).Normal := N.normal_map_semidirectProductInl hstable
  have hcard : Nat.card (N.map i) = Nat.card N := card_map_of_injective hi
  obtain ⟨m, hmcard⟩ := hA.exists_card_eq
  have hindex : ((⊤ : Subgroup W).map i).index = Nat.card A := by
    rw [map_top, range_inl_eq_ker_rightHom, index_ker,
      MonoidHom.range_eq_top.mpr rightHom_surjective, card_top]
  have hcop : Nat.Coprime ((⊤ : Subgroup W).map i).index (Nat.card (N.map i)) := by
    rw [hindex, hcard, hmcard]
    exact ((Fact.out : q.Prime).coprime_pow_of_not_dvd hN).symm
  obtain ⟨D₀, hD₀⟩ :=
    ((isLocalComplement_top_iff.mpr hK).map hi).exists_isComplement'_of_coprime_index hcop
  obtain ⟨D₁, hD₁, hj⟩ := hD₀.exists_isComplement'_and_le_of_not_dvd_card
    (hA.of_surjective j.rangeRestrict j.rangeRestrict_surjective) (hcard ▸ hN)
  have hker : Disjoint N i.ker := by rw [i.ker_eq_bot hi]; exact disjoint_bot_right
  refine ⟨D₁.comap i, hD₁.comap_of_disjoint_ker hker, ?_⟩
  intro a d hd
  have ha : j a ∈ D₁ := hj ⟨a, rfl⟩
  have he : i (a • d) = j a * i d * (j a)⁻¹ := by
    exact (inl_aut a d).trans (by rw [map_inv])
  apply mem_comap.mpr
  rw [he]
  exact D₁.mul_mem (D₁.mul_mem ha hd) (D₁.inv_mem ha)

/-- An abelian normal `p`-subgroup of a finite group, complemented in a Sylow `p`-subgroup,
has an invariant complement under every action by automorphisms of a `q`-group preserving it,
provided `p ≠ q`. No finiteness of the acting group or coprimality between its order and the
order of the ambient group is required. -/
theorem exists_invariant_complement [Finite W] {p : ℕ} [Fact p.Prime]
    (N : Subgroup W) [N.Normal] [IsMulCommutative N]
    (hN : IsPGroup p N) (hA : IsPGroup q A) (hpq : p ≠ q)
    (hstable : ∀ a : A, ∀ n ∈ N, a • n ∈ N) (P : Sylow p W)
    (hlocal : ∃ K : Subgroup W, N.IsLocalComplement K P) :
    ∃ D : Subgroup W, N.IsComplement' D ∧ ∀ a : A, ∀ d ∈ D, a • d ∈ D := by
  obtain ⟨n, hncard⟩ := hN.exists_card_eq
  have hcop : Nat.Coprime P.toSubgroup.index (Nat.card N) := by
    rw [hncard]
    exact (Fact.out : p.Prime).coprime_pow_of_not_dvd P.not_dvd_index
  obtain ⟨K, hK⟩ := hlocal
  obtain ⟨D₀, hD₀⟩ := hK.exists_isComplement'_of_coprime_index hcop
  have hq : ¬ q ∣ Nat.card N := by
    rw [hncard]
    apply (Fact.out : q.Prime).coprime_iff_not_dvd.mp
    simpa only [pow_one] using Nat.coprime_pow_primes 1 n (Fact.out : q.Prime)
      (Fact.out : p.Prime) hpq.symm
  let φ := MulDistribMulAction.toMulAut A W
  have hA' : IsPGroup q φ.range :=
    hA.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hstable' : ∀ a : φ.range, ∀ n ∈ N, a • n ∈ N := by
    rintro ⟨_, a, rfl⟩ n hn
    exact hstable a n hn
  obtain ⟨D, hD, hstableD⟩ :=
    hD₀.exists_invariant_complement_of_not_dvd_card hA' hq hstable'
  exact ⟨D, hD, fun a d hd => hstableD (φ.rangeRestrict a) d hd⟩

end Subgroup
