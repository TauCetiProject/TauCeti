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
to `1` under an equivalence with `Multiplicative ℤ` generates its group (and, more precisely, which
elements generate it or have finite order), and reindexes finite sums
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
* `MulEquiv.zpowers_eq_top_iff_isUnit_toAdd`: under such an equivalence, an element generates its
  group iff it is sent to `±1`.
* `MulEquiv.isOfFinOrder_iff_toAdd_eq_zero`: under such an equivalence, an element has finite order
  iff it is sent to `0`.
* `TauCeti.prod_range_orderOf_eq_prod`, `TauCeti.sum_range_orderOf_eq_sum`: multiplying or summing
  over powers of a generator enumerates a finite group.

## References

The construction follows the enumeration pattern of `TauCeti.dihedralElements`.
-/

public section

namespace TauCeti

/-- Multiplying a function over the powers `1, g, …, gⁿ⁻¹` of a generator of a finite cyclic
group is the product over the whole group, where `n = orderOf g`. -/
@[to_additive (dont_translate := G) sum_range_orderOf_eq_sum
  /-- Summing a function over the powers `1, g, …, gⁿ⁻¹` of a generator of a finite cyclic group
  is the sum over the whole group, where `n = orderOf g`. -/]
theorem prod_range_orderOf_eq_prod {G M : Type*} [Group G] [Fintype G] [CommMonoid M]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (f : G → M) :
    ∏ i ∈ Finset.range (orderOf g), f (g ^ i) = ∏ x : G, f x := by
  rw [← Fin.prod_univ_eq_prod_range]
  simpa only [Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply, finEquivZPowers_apply] using
    (((finEquivZPowers (isOfFinOrder_of_finite g)).trans
      (Equiv.subtypeUnivEquiv hg)).prod_comp f)

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

/-- Under a group equivalence `e` with `Multiplicative ℤ`, an element generates its group
exactly when `e` sends it to a unit `±1` of `ℤ`. -/
theorem _root_.MulEquiv.zpowers_eq_top_iff_isUnit_toAdd {G : Type*} [Group G]
    (e : G ≃* Multiplicative ℤ) (g : G) :
    Subgroup.zpowers g = ⊤ ↔ IsUnit (e g).toAdd := by
  refine ⟨fun h ↦ ?_, fun hu ↦ ?_⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (h ▸ Subgroup.mem_top (e.symm (Multiplicative.ofAdd 1)))
    rw [e.eq_symm_apply, map_zpow, ← ofAdd_toAdd (e g), ← ofAdd_zsmul,
      EmbeddingLike.apply_eq_iff_eq, smul_eq_mul] at hk
    exact .of_mul_eq_one_right _ hk
  rcases Int.isUnit_iff.mp hu with hu | hu
  · exact e.zpowers_eq_top_of_apply_eq_ofAdd_one (by rw [← hu, ofAdd_toAdd])
  · rw [← Subgroup.zpowers_inv]
    exact e.zpowers_eq_top_of_apply_eq_ofAdd_one
      (by rw [map_inv, ← ofAdd_toAdd (e g), hu, ofAdd_neg, inv_inv])

/-- Under a group equivalence `e` with `Multiplicative ℤ`, an element has finite order exactly
when `e` sends it to `0 : ℤ`. -/
theorem _root_.MulEquiv.isOfFinOrder_iff_toAdd_eq_zero {G : Type*} [Group G]
    (e : G ≃* Multiplicative ℤ) {g : G} : IsOfFinOrder g ↔ (e g).toAdd = 0 := by
  rw [← e.injective.isOfFinOrder_iff (f := e.toMonoidHom), isOfFinOrder_iff_eq_one,
    MulEquiv.coe_toMonoidHom, toAdd_eq_zero]

end TauCeti
