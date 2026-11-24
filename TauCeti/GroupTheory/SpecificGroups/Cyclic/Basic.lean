/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic groups

For `n ≠ 0`, this file gives the standard computable enumeration of
`Multiplicative (ZMod n)`, transported from the additive group `ZMod n`.
It also records that `Multiplicative.ofAdd 1` generates `Multiplicative ℤ` and has infinite order,
that the `n`-th powers of `Multiplicative ℤ` are the multiples of `n`, that an element corresponding
to `1` under an equivalence with `Multiplicative ℤ` generates its group, and reindexes finite sums
by the powers of a generator.

## Main definitions

* `TauCeti.cyclicElements`: a computable enumeration of `Multiplicative (ZMod n)`.

## Main results

* `TauCeti.mem_cyclicElements`: the enumeration exhausts the group when `n ≠ 0`.
* `Int.mem_zpowers_ofAdd_one`: `Multiplicative.ofAdd 1` generates `Multiplicative ℤ`.
* `Int.not_isOfFinOrder_ofAdd_one`: `Multiplicative.ofAdd 1` has infinite order.
* `Int.mem_range_zpowGroupHom_iff`: `x` is an `n`-th power in `Multiplicative ℤ` iff `n ∣ x.toAdd`.
* `MulEquiv.zpowers_eq_top_of_apply_eq_ofAdd_one`: an element sent to `1` by an equivalence with
  `Multiplicative ℤ` generates its group.
* `TauCeti.sum_range_orderOf_eq_sum`: summing over powers of a generator enumerates a finite group.

## References

The construction follows the enumeration pattern of `TauCeti.dihedralElements`.
-/

public section

namespace TauCeti

/-- Summing a function over the powers `1, g, …, gⁿ⁻¹` of a generator of a finite cyclic group
is the sum over the whole group, where `n = orderOf g`. -/
theorem sum_range_orderOf_eq_sum {G M : Type*} [Group G] [Fintype G] [AddCommMonoid M]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (f : G → M) :
    ∑ i ∈ Finset.range (orderOf g), f (g ^ i) = ∑ x : G, f x := by
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply, finEquivZPowers_apply] using
    (((finEquivZPowers (isOfFinOrder_of_finite g)).trans
      (Equiv.subtypeUnivEquiv hg)).sum_comp f)

/-- For `n ≠ 0`, the standard computable enumeration of the finite cyclic group
`Multiplicative (ZMod n)`. For `n = 0`, this list is empty. -/
@[expose] def cyclicElements (n : ℕ) : List (Multiplicative (ZMod n)) :=
  List.ofFn fun i : Fin n => Multiplicative.ofAdd (i : ZMod n)

/-- Every element of `Multiplicative (ZMod n)` occurs in `TauCeti.cyclicElements n` when `n` is
nonzero. -/
theorem mem_cyclicElements (n : ℕ) [NeZero n] (g : Multiplicative (ZMod n)) :
    g ∈ cyclicElements n := by
  rw [cyclicElements, List.mem_ofFn']
  exact ⟨⟨g.toAdd.val, ZMod.val_lt g.toAdd⟩,
    congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val g.toAdd)⟩

/-- `Multiplicative.ofAdd 1` generates `Multiplicative ℤ`, the multiplicative form of
`Int.zmultiples_one`. -/
theorem _root_.Int.mem_zpowers_ofAdd_one (x : Multiplicative ℤ) :
    x ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ)) :=
  Subgroup.mem_zpowers_iff.2 ⟨x.toAdd, by rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]⟩

/-- `Multiplicative.ofAdd 1` has infinite order in `Multiplicative ℤ`. -/
theorem _root_.Int.not_isOfFinOrder_ofAdd_one : ¬IsOfFinOrder (Multiplicative.ofAdd (1 : ℤ)) :=
  isOfFinOrder_ofAdd_iff.not.2 (not_isOfFinAddOrder_of_isAddTorsionFree one_ne_zero)

/-- An element `x` of `Multiplicative ℤ` is an `n`-th power exactly when `n` divides the integer
`x.toAdd`: the multiplicative form of `Int.mem_zmultiples_iff`. -/
theorem _root_.Int.mem_range_zpowGroupHom_iff {n : ℤ} {x : Multiplicative ℤ} :
    x ∈ (zpowGroupHom n : Multiplicative ℤ →* Multiplicative ℤ).range ↔ n ∣ x.toAdd :=
  ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, by rw [← hc, zpowGroupHom_apply, toAdd_zpow, smul_eq_mul]⟩,
    fun ⟨c, hc⟩ => ⟨.ofAdd c, by
      rw [zpowGroupHom_apply, ← ofAdd_toAdd x, hc, ← ofAdd_zsmul, smul_eq_mul]⟩⟩

/-- An element sent to `1` by a group equivalence with `Multiplicative ℤ` generates its
group. -/
theorem _root_.MulEquiv.zpowers_eq_top_of_apply_eq_ofAdd_one {G : Type*} [Group G] {g : G}
    (e : G ≃* Multiplicative ℤ) (hg : e g = Multiplicative.ofAdd 1) :
    Subgroup.zpowers g = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun y => ⟨(e y).toAdd,
    e.injective (by simp [hg, ← ofAdd_zsmul])⟩

end TauCeti
