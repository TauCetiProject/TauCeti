/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Jordan
import TauCeti.Data.Nat.Factorial.Prime
import TauCeti.GroupTheory.Commutator
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Sylow

/-!
# Jordan's theorem for a cycle of prime length

A primitive permutation group of degree `n` that contains a cycle of prime length `p`, with
`p + 3 ≤ n`, contains the alternating group. This is Jordan's theorem of 1873, the analogue for
cycles of arbitrary prime length of Mathlib's
`Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem` and
`Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`, which need no bound on
the degree. The bound `p + 3 ≤ n` cannot be weakened to `p ≤ n` or `p + 1 ≤ n`: the affine group
`AGL(1, 5)` is primitive of degree `5` and contains a `5`-cycle, and `AGL(1, 8)` is primitive of
degree `8` and contains a `7`-cycle. Neither contains the alternating group.

## Main results

* `TauCeti.isMultiplyPreprimitive_of_isCycle_mem`: a primitive group containing a cycle of prime
  length whose complement of the support has `k` points is `(k + 1)`-fold primitive.
* `TauCeti.exists_eqOn_compl_support_mul_mul_inv_mem_zpowers`: the Frattini step for an element
  preserving the support of a cycle of prime length.
* `TauCeti.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem`: Jordan's theorem, a primitive
  permutation group of degree at least `p + 3` containing a `p`-cycle for a prime `p` contains the
  alternating group.

## References

* H. Wielandt, *Finite Permutation Groups*, Theorem 13.9, with the Sylow argument of
  Theorem 9.4.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, Theorem 3.3E.
* Mathlib's `Mathlib/GroupTheory/GroupAction/Jordan.lean`, by Antoine Chambert-Loir, for the
  related transposition and `3`-cycle results.
-/

public section

namespace TauCeti

open MulAction Equiv Equiv.Perm Finset Subgroup
open scoped commutatorElement

variable {α : Type*} [Fintype α] [DecidableEq α] {G : Subgroup (Perm α)}

/-- **Jordan's multiple primitivity for a cycle of prime length.** A primitive permutation group
containing a cycle `g` of prime length is `(k + 1)`-fold primitive, where `k` is the number of
fixed points of `g`. -/
theorem isMultiplyPreprimitive_of_isCycle_mem (hG : IsPreprimitive G α) {g : Perm α}
    (hgc : g.IsCycle) (hgp : (#g.support).Prime) (hg : g ∈ G) :
    IsMultiplyPreprimitive G α (#g.supportᶜ + 1) := by
  classical
  obtain hk | hk := Nat.eq_zero_or_pos #g.supportᶜ
  · rwa [hk, zero_add, is_one_preprimitive_iff]
  obtain ⟨m, hm⟩ : ∃ m, #g.supportᶜ = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hk).symm⟩
  have hcard := (card_compl_add_card g.support).trans Nat.card_eq_fintype_card.symm
  have hp2 := hgp.two_le
  rw [hm]
  refine hG.isMultiplyPreprimitive (s := (g.support : Set α)ᶜ) ?_ (by omega) ?_
  · rw [← coe_compl, Set.ncard_coe_finset, hm]
  · -- The subgroup fixing the complement of the support is transitive on a set of prime size.
    have := isPretransitive_of_isCycle_mem hgc hg
    apply IsPreprimitive.of_prime_card
    convert hgp using 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]

/-- The Frattini step: if `x ∈ G` preserves the support of a cycle `g ∈ G` of prime length, then
`x` can be corrected by an element of `G` supported on the support of `g` so that it normalizes
`⟨g⟩`. The subgroup of `G` supported on the support of `g` has `⟨g⟩` as a Sylow subgroup. -/
theorem exists_eqOn_compl_support_mul_mul_inv_mem_zpowers {g x : Perm α}
    (hgc : g.IsCycle) (hgp : (#g.support).Prime) (hg : g ∈ G) (hx : x ∈ G)
    (hxs : ∀ z, x z ∈ g.support ↔ z ∈ g.support) :
    ∃ n ∈ G, (∀ z ∉ g.support, n z = x z) ∧ n * g * n⁻¹ ∈ zpowers g := by
  have := Fact.mk hgp
  -- The elements of `G` supported on the support of `g`.
  let F : Subgroup (Perm α) := G ⊓ (ofSubtype : Perm {z // z ∈ g.support} →* Perm α).range
  have hmemF : ∀ σ ∈ G, (∀ z, σ z ≠ z → z ∈ g.support) → σ ∈ F := fun σ hσ hsupp ↦
    ⟨hσ, mem_range_ofSubtype_iff.2 fun z hz ↦ hsupp z (mem_support.1 hz)⟩
  have hgF : g ∈ F := hmemF g hg fun z hz ↦ mem_support.2 hz
  have hg'F : x * g * x⁻¹ ∈ F := by
    refine hmemF _ (mul_mem (mul_mem hx hg) (inv_mem hx)) fun z hz ↦ ?_
    have h : x⁻¹ z ∈ g.support := by
      rw [mem_support]
      intro h
      apply hz
      rw [Perm.mul_apply, Perm.mul_apply, h]
      exact x.apply_symm_apply z
    simpa using (hxs _).2 h
  -- `F` embeds into the symmetric group on the support of `g`, so `p ^ 2` does not divide `|F|`.
  have hsq : ¬ (#g.support) ^ 2 ∣ Nat.card F := by
    intro h
    have hcard : Nat.card F ∣ (#g.support).factorial := by
      refine (card_dvd_of_le inf_le_right).trans (dvd_of_eq ?_)
      rw [← Nat.card_congr (MonoidHom.ofInjective ofSubtype_injective).toEquiv, Nat.card_perm,
        Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hgp.not_sq_dvd_factorial (h.trans hcard)
  obtain ⟨y, hy⟩ := exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd hsq
    (g := ⟨g, hgF⟩) (h := ⟨x * g * x⁻¹, hg'F⟩) (by rw [orderOf_mk, hgc.orderOf])
    (by rw [orderOf_mk, hgc.conj.orderOf, card_support_conj])
  refine ⟨y * x, mul_mem y.2.1 hx, fun z hz ↦ ?_, ?_⟩
  · have hyz : (y : Perm α) (x z) = x z := by
      by_contra h
      exact hz ((hxs z).1 (by simpa using mem_range_ofSubtype_iff.1 y.2.2 (mem_support.2 h)))
    rw [Perm.mul_apply, hyz]
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    simpa only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc] using
      congrArg Subtype.val hk

/-- If `G` is `k`-fold transitive, where `k` is the number of fixed points of a cycle `g ∈ G` of
prime length, then every transposition of two fixed points of `g` is induced on the fixed points
of `g` by an element of `G` normalizing `⟨g⟩`. -/
private theorem exists_eqOn_swap_mul_mul_inv_mem_zpowers {g : Perm α} (hgc : g.IsCycle)
    (hgp : (#g.support).Prime) (hg : g ∈ G) (hG : IsMultiplyPretransitive G α #g.supportᶜ)
    {a b : α} (ha : a ∉ g.support) (hb : b ∉ g.support) :
    ∃ n ∈ G, (∀ z ∉ g.support, n z = swap a b z) ∧ n * g * n⁻¹ ∈ zpowers g := by
  have hswap : ∀ z ∉ g.support, swap a b z ∉ g.support := fun _ ↦ swap_apply_notMem ha hb
  -- Realize the transposition on the fixed points of `g` by `k`-fold transitivity.
  let e : Fin #g.supportᶜ ↪ α :=
    g.supportᶜ.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨x, hx⟩ := exists_smul_eq G e (e.trans (swap a b).toEmbedding)
  have hxΔ : ∀ z ∉ g.support, (x : Perm α) z = swap a b z := fun z hz ↦ by
    simpa only [e, Function.Embedding.smul_apply, Function.Embedding.trans_apply,
      Function.Embedding.subtype_apply, Equiv.toEmbedding_apply, Equiv.symm_apply_apply,
      Subgroup.smul_def, Perm.smul_def] using
      DFunLike.congr_fun hx (g.supportᶜ.equivFin ⟨z, mem_compl.2 hz⟩)
  have hxs : ∀ z, (x : Perm α) z ∈ g.support ↔ z ∈ g.support := fun z ↦ by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · by_contra hz
      exact hswap z hz (hxΔ z hz ▸ h)
    · by_contra hxz
      have hw := hswap _ hxz
      have : (x : Perm α) (swap a b ((x : Perm α) z)) = (x : Perm α) z := by
        rw [hxΔ _ hw, swap_apply_self]
      exact hw (by rwa [(x : Perm α).injective this])
  obtain ⟨n, hnG, hn, hng⟩ := exists_eqOn_compl_support_mul_mul_inv_mem_zpowers hgc hgp hg x.2 hxs
  exact ⟨n, hnG, fun z hz ↦ (hn z hz).trans (hxΔ z hz), hng⟩

/-- **Jordan's theorem for a cycle of prime length** (Wielandt, Theorem 13.9). A primitive
permutation group of degree at least `p + 3` that contains a cycle of prime length `p` contains
the alternating group. -/
theorem alternatingGroup_le_of_isPreprimitive_of_isCycle_mem (hG : IsPreprimitive G α) {p : ℕ}
    (hp : p.Prime) (hp' : p + 3 ≤ Nat.card α) {g : Perm α} (hgc : g.IsCycle)
    (hgp : #g.support = p) (hg : g ∈ G) : alternatingGroup α ≤ G := by
  subst hgp
  have hcard := (card_compl_add_card g.support).trans Nat.card_eq_fintype_card.symm
  have htr : IsMultiplyPretransitive G α #g.supportᶜ := by
    have := (isMultiplyPreprimitive_of_isCycle_mem hG hgc hp hg).isMultiplyPretransitive
    exact isMultiplyPretransitive_of_le (n := #g.supportᶜ + 1) (by omega)
      (by have := hp.two_le; omega)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.1 (by omega : 2 < #g.supportᶜ)
  rw [mem_compl] at ha hb hc
  obtain ⟨n₁, hn₁G, hn₁, hn₁g⟩ := exists_eqOn_swap_mul_mul_inv_mem_zpowers hgc hp hg htr ha hb
  obtain ⟨n₂, hn₂G, hn₂, hn₂g⟩ := exists_eqOn_swap_mul_mul_inv_mem_zpowers hgc hp hg htr hb hc
  have hinv : ∀ {n : Perm α} {x y : α}, (∀ z ∉ g.support, n z = swap x y z) → x ∉ g.support →
      y ∉ g.support → ∀ z ∉ g.support, n⁻¹ z = swap x y z := fun hn hx hy z hz ↦ by
    rw [Perm.inv_eq_iff_eq, hn _ (swap_apply_notMem hx hy hz), swap_apply_self]
  -- The commutator `t` of `n₁⁻¹` and `n₂⁻¹` centralizes `g`, so it is a power of `g` on the
  -- support of `g`; on the fixed points of `g` it is the `3`-cycle `(a b)(b c)(a b)(b c)`.
  have htg : Commute ⁅n₁⁻¹, n₂⁻¹⁆ g :=
    commute_commutatorElement_of_inv_mul_mul_mem_zpowers (x := n₁⁻¹) (y := n₂⁻¹)
      (by rwa [inv_inv]) (by rwa [inv_inv])
  obtain ⟨j, hfix, hout⟩ := hgc.exists_mul_zpow_inv_apply_eq_of_commute htg
  have hτ : ⁅n₁⁻¹, n₂⁻¹⁆ * (g ^ j)⁻¹ = swap c a * swap c b := by
    ext z
    by_cases hz : z ∈ g.support
    · rw [hfix z hz, Perm.mul_apply]
      have hne : ∀ d ∉ g.support, z ≠ d := fun d hd h ↦ hd (h ▸ hz)
      rw [swap_apply_of_ne_of_ne (hne c hc) (hne b hb),
        swap_apply_of_ne_of_ne (hne c hc) (hne a ha)]
    · have hperm : swap a b * swap b c * swap a b * swap b c = swap c a * swap c b := by
        rw [swap_comm a b, swap_comm b c, swap_mul_swap_mul_swap hbc.symm hac.symm, swap_comm a c]
      rw [← hperm, hout z hz, commutatorElement_def, inv_inv, inv_inv]
      simp only [Perm.mul_apply]
      have h₁ := swap_apply_notMem hb hc hz
      have h₂ := swap_apply_notMem ha hb h₁
      rw [hn₂ z hz, hn₁ _ h₁, hinv hn₂ hb hc _ h₂, hinv hn₁ ha hb _ (swap_apply_notMem hb hc h₂)]
  refine alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG
    (isThreeCycle_swap_mul_swap_same hac.symm hbc.symm hab) (hτ ▸ ?_)
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hn₁G) (inv_mem hn₂G)) (inv_mem (inv_mem hn₁G)))
    (inv_mem (inv_mem hn₂G))) (inv_mem (zpow_mem hg j))

end TauCeti
