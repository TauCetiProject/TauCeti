/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Additive groups in which every element has `p`-power order

Mathlib's `IsPGroup` is stated for multiplicative groups. This file records the facts about a
`p`-primary *additive* group `A`, one in which every element `a` satisfies `p ^ k • a = 0` for
some `k`, that the theory of pro-`p` actions on finite discrete coefficient modules needs, in
additive notation: the order of a finite such group is a power of `p`, namely
`p ^ padicValNat p (Nat.card A)`, and is divisible by `p` when the group is nontrivial; a nonzero
element of `p`-power order has a nonzero multiple annihilated by `p`, a statement about natural
multiples that holds in any additive monoid; a monoid additively equivalent to `ZMod p` is
`p`-primary; a subgroup of a `p`-primary group is `p`-primary; and adjoining to a subgroup `N` an
element `x ∉ N` with `p • x ∈ N` multiplies the order of `N` by `p`.

## Main results

* `TauCeti.prime_dvd_natCard_of_forall_exists_nsmul_eq_zero`: `p ∣ Nat.card A` for a nontrivial
  finite `p`-primary additive group `A`.
* `TauCeti.natCard_eq_pow_padicValNat_of_forall_exists_nsmul_eq_zero`:
  `Nat.card A = p ^ padicValNat p (Nat.card A)` for a finite `p`-primary additive group `A`.
* `TauCeti.exists_nsmul_pow_ne_zero_nsmul_nsmul_pow_eq_zero`: a nonzero `a` with `p ^ k • a = 0`
  has a nonzero multiple `p ^ n • a` with `p • p ^ n • a = 0`.
* `TauCeti.forall_exists_nsmul_eq_zero_of_addEquiv_zmod`: an additive monoid additively
  equivalent to `ZMod p` is `p`-primary.
* `AddSubgroup.forall_exists_nsmul_eq_zero`: an additive subgroup of a `p`-primary additive group
  is `p`-primary.
* `TauCeti.subquotientEquivZModOfEqSupZmultiples`: adjoining `x ∉ N` with `p • x ∈ N`
  gives a quotient additively equivalent to `ZMod p`, sending the class of `x` to `1`.
* `TauCeti.natCard_sup_zmultiples_of_nsmul_mem`: `|N ⊔ zmultiples x| = p * |N|` when `x ∉ N` and
  `p • x ∈ N`.
-/

public section

namespace TauCeti

variable {p : ℕ}

section AddMonoid

variable {A : Type*} [AddMonoid A]

/-- A nonzero element `a` with `p ^ k • a = 0` has a nonzero multiple `p ^ n • a` annihilated by
`p`, that is, with `p • p ^ n • a = 0`. -/
theorem exists_nsmul_pow_ne_zero_nsmul_nsmul_pow_eq_zero {a : A} (ha : a ≠ 0) {k : ℕ}
    (hk : p ^ k • a = 0) : ∃ n : ℕ, p ^ n • a ≠ 0 ∧ p • p ^ n • a = 0 := by
  classical
  have h : ∃ k, p ^ k • a = 0 := ⟨k, hk⟩
  have hfind : p ^ Nat.find h • a = 0 := Nat.find_spec h
  have hpos : 0 < Nat.find h := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [h0, pow_zero, one_smul] at hfind
    exact ha hfind
  refine ⟨Nat.find h - 1, Nat.find_min h (Nat.sub_lt hpos one_pos), ?_⟩
  have hk' : Nat.find h - 1 + 1 = Nat.find h := by omega
  rwa [smul_smul, ← pow_succ', hk']

/-- An additive monoid additively equivalent to `ZMod p` is `p`-primary: `p` itself annihilates
every element. -/
theorem forall_exists_nsmul_eq_zero_of_addEquiv_zmod (e : A ≃+ ZMod p) :
    ∀ a : A, ∃ k : ℕ, p ^ k • a = 0 :=
  fun _ ↦ ⟨1, e.injective (by simp)⟩

end AddMonoid

section AddSubgroup

variable {A : Type*} [AddGroup A]

/-- An additive subgroup of a `p`-primary additive group is `p`-primary: every element of `N` has
`p`-power order when every element of the ambient group `A` does. -/
theorem _root_.AddSubgroup.forall_exists_nsmul_eq_zero (N : AddSubgroup A)
    (h : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) : ∀ x : N, ∃ k : ℕ, p ^ k • x = 0 := fun x ↦
  let ⟨k, hk⟩ := h x
  ⟨k, Subtype.ext hk⟩

end AddSubgroup

section AddGroup

variable [hp : Fact p.Prime] {A : Type*} [AddGroup A]

/-- A nontrivial finite additive group in which every element has `p`-power order has order
divisible by `p`. -/
theorem prime_dvd_natCard_of_forall_exists_nsmul_eq_zero [Finite A] [Nontrivial A]
    (htors : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) : p ∣ Nat.card A := by
  have hA : IsPGroup p (Multiplicative A) := fun a ↦ by
    obtain ⟨k, hk⟩ := htors a.toAdd
    exact ⟨k, by rw [← ofAdd_toAdd a, ← ofAdd_nsmul, hk, ofAdd_zero]⟩
  obtain ⟨n, hn, hcard⟩ := hA.nontrivial_iff_card.mp inferInstance
  rw [← Nat.card_congr (Multiplicative.toAdd (α := A)), hcard]
  exact dvd_pow_self p hn.ne'

/-- A finite additive group in which every element has `p`-power order has order the power of
`p` given by the `p`-adic valuation of its order. -/
theorem natCard_eq_pow_padicValNat_of_forall_exists_nsmul_eq_zero [Finite A]
    (htors : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) :
    Nat.card A = p ^ padicValNat p (Nat.card A) := by
  have hA : IsPGroup p (Multiplicative A) := fun a ↦ by
    obtain ⟨k, hk⟩ := htors a.toAdd
    exact ⟨k, by rw [← ofAdd_toAdd a, ← ofAdd_nsmul, hk, ofAdd_zero]⟩
  obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp hA
  rw [← Nat.card_congr (Multiplicative.toAdd (α := A)), hcard, padicValNat.prime_pow]

end AddGroup

section AddCommGroup

variable [Fact p.Prime] {M : Type*} [AddCommGroup M]

/-- If `K` is obtained from `N` by adjoining `x ∉ N` with `p • x ∈ N`, then `K ⧸ N`
is additively equivalent to `ZMod p`. The equivalence sends the class of `x` to `1`
(see `zmodAddEquivOfGenerator_symm_apply_generator`). -/
noncomputable def subquotientEquivZModOfEqSupZmultiples {N K : AddSubgroup M} {x : M}
    (hgen : K = N ⊔ AddSubgroup.zmultiples x) (hx : x ∉ N) (hpx : p • x ∈ N) :
    (K ⧸ N.addSubgroupOf K) ≃+ ZMod p := by
  have hxK : x ∈ K := hgen ▸ AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples x)
  set y : K ⧸ N.addSubgroupOf K := ((⟨x, hxK⟩ : K) : K ⧸ N.addSubgroupOf K) with hy
  have hy0 : y ≠ 0 := fun h ↦
    hx (AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h))
  have hpy : p • y = 0 := by
    rw [hy, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_addSubgroupOf.mpr hpx
  have htop : AddSubgroup.zmultiples y = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hgen] at hz
    obtain ⟨n, hn, m, hm, rfl⟩ := AddSubgroup.mem_sup.mp hz
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k, ?_⟩
    rw [hy, ← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_iff_sub_mem,
      AddSubgroup.mem_addSubgroupOf]
    simpa using hn
  have hcard : Nat.card (K ⧸ N.addSubgroupOf K) = p := by
    rw [← AddSubgroup.card_top, ← htop, Nat.card_zmultiples, addOrderOf_eq_prime hpy hy0]
  exact (zmodAddEquivOfGenerator (fun z ↦ htop ▸ AddSubgroup.mem_top z) hcard).symm

/-- Adjoining to a subgroup `N` an element `x ∉ N` with `p • x ∈ N` multiplies its order by
`p`: the quotient `(N ⊔ zmultiples x) ⧸ N` is cyclic of order `p`, generated by the class of
`x`. -/
theorem natCard_sup_zmultiples_of_nsmul_mem {N : AddSubgroup M} {x : M} (hx : x ∉ N)
    (hpx : p • x ∈ N) :
    Nat.card (N ⊔ AddSubgroup.zmultiples x : AddSubgroup M) = p * Nat.card N := by
  let K := N ⊔ AddSubgroup.zmultiples x
  have hNK : N ≤ K := le_sup_left
  have hcard : Nat.card (K ⧸ N.addSubgroupOf K) = p := by
    rw [Nat.card_congr (subquotientEquivZModOfEqSupZmultiples rfl hx hpx).toEquiv,
      Nat.card_zmod]
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (N.addSubgroupOf K), hcard,
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hNK).toEquiv]

end AddCommGroup

end TauCeti
