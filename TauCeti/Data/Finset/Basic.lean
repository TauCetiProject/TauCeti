/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NoncommRing
import TauCeti.Data.Set.PowersetCard

/-!
# Finite-set infrastructure

* `Finset.exists_nat_prod_lt` bounds both coordinates of a finite set of pairs of
  natural numbers.
* `Finset.exists_perm_eqOn_le_apply` gives a permutation of `ℕ` fixing one finite set pointwise
  and carrying a disjoint one past any bound.
* `TauCeti.product_union_eq_union_product` rearranges a union of products of finsets.
* `TauCeti.card_nonempty_finset` counts the nonempty finsets of a finite type.
* `TauCeti.card_even_card_finset` and `TauCeti.card_odd_card_finset` count the finsets of a
  nonempty finite type by the parity of their cardinality: each parity accounts for exactly half
  of them.
* `Finset.sum_powerset_neg_one_pow_card_of_ring` evaluates the alternating sum over the subsets of
  a finset in an arbitrary ring.
* `Finset.sum_powerset_neg_one_pow_mul_eq_zero` pairs subsets that differ by one element
  to cancel a signed sum.
* `Finset.sum_Icc_neg_one_pow_card_sub_card_left` and
  `Finset.sum_Icc_neg_one_pow_card_sub_card_right` compute the Möbius function of the Boolean
  lattice of finsets: the signed sum over an interval `[s, t]` is `1` if `s = t` and `0`
  otherwise.
* `Finset.neg_one_pow_card_filter_lt_mul_insert`, `Finset.neg_one_pow_card_filter_lt_mul_erase`
  and `Finset.neg_one_pow_card_filter_lt_mul_insert_insert` show that inserting a new element and
  deleting an existing element of an ordered finset in either order, deleting two distinct
  elements in either order, or inserting two distinct new elements in either order, gives
  opposite Koszul signs.
* `Finset.card_filter_lt_add_card_filter_gt_add_one` splits a finset of a linear order at one of its
  elements, and `Finset.filter_lt_subset_Ioo` and `Finset.filter_gt_subset_Ioo` place the two
  halves of a finset inside an open interval between the split point and an endpoint;
  `Finset.add_one_add_card_erase_eq_zero` and `Finset.neg_card_filter_lt_add_neg_card_filter_gt`
  are the corresponding identities for an integer cancelling the cardinality of the finset.
* `Finset.exists_adjacent_eq_of_not_card_image_and_image_subset_Ioo` finds two consecutive points
  identified by a monotone map that is not injective on a finset `T` inside `Ioo a b`, or does not
  map it strictly between the images of `a` and `b`, and
  `Finset.card_image_comp_eq_and_image_comp_subset_Ioo_iff` splits that condition for a composite
  of maps.
* `Finset.card_symmDiff_add_two_mul_card_inter` and `Finset.even_card_symmDiff_iff` compare the
  cardinality of a symmetric difference with the cardinalities of its two arguments: exactly, and
  modulo two.
* `Finset.map_swap_pair`, `Finset.map_swap_pair_right` and `Finset.map_swap_eq_self_iff`
  describe how a transposition moves a finset around, and
  `Finset.mem_map_swap_symmDiff_pair_iff`, `Finset.involutive_map_swap_symmDiff_pair` and
  `Finset.map_swap_symmDiff_pair_eq_self_iff` do the same for a transposition composed with the
  toggle of the two transposed points.
* `Finset.mem_map_swap_prodCongr_refl_iff_of_ne` and
  `Finset.mk_mem_map_swap_prodCongr_refl_iff` describe membership in a finset of pairs whose
  first coordinates are transposed.
* `Finset.sum_filter_le_sum_filter_le` reindexes a double sum over chains in a finite type with a
  `≤` relation.
* `Finset.sum_eq_two` and `Finset.sum_eq_four` reduce a sum over a finite type, and a double sum
  over a pair of finite types, to the values of its summand at the two points where it is
  supported, and at the four cells of a rectangle.
* `Finset.filter_ne_product_of_disjoint` says that every pair in the product of disjoint finsets
  has distinct coordinates.
* `TauCeti.sum_piecewise_eq_sum_update_of_card_eq_succ` reindexes a sum of `Finset.piecewise` terms
  over the subsets of size one less than `card ι` as a sum of `Function.update` terms over `ι`. It
  is what turns a formula indexed by "all but one point" into one indexed by the omitted point, as
  in the change-origin and derivative computations for multilinear series.
-/

public section

namespace TauCeti

/-- A union of two products of finsets can be rearranged by distributing each product over its
union coordinate. -/
theorem product_union_eq_union_product {s s' : Finset α} {t t' : Finset β}
    [DecidableEq α] [DecidableEq β] :
    s ×ˢ t ∪ (s ∪ s') ×ˢ t' = s' ×ˢ t' ∪ s ×ˢ (t ∪ t') := by
  rw [Finset.union_product, Finset.product_union]
  ac_rfl

/-- **The number of nonempty subsets of a finite type is `2ⁿ - 1`.** The `2ⁿ` subsets of an
`n`-element type are the nonempty ones together with the empty set, so the nonempty ones number
`2ⁿ - 1`. -/
theorem card_nonempty_finset {ι : Type*} [Finite ι] :
    Nat.card {S : Finset ι // S.Nonempty} = 2 ^ Nat.card ι - 1 := by
  classical
  let := Fintype.ofFinite ι
  have h : Fintype.card {S : Finset ι // S.Nonempty} = 2 ^ Fintype.card ι - 1 := by
    rw [Fintype.card_subtype]
    simp_rw [Finset.nonempty_iff_ne_empty]
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_finset]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h]

/-- Deleting a fixed point `i` from a subset that contains it, and adjoining it to one that does
not. This is the parity-reversing involution of the subsets of `ι` behind
`TauCeti.card_even_card_finset`. -/
private def parityFlip {ι : Type*} [DecidableEq ι] (i : ι) (s : Finset ι) : Finset ι :=
  if i ∈ s then s.erase i else insert i s

private theorem parityFlip_parityFlip {ι : Type*} [DecidableEq ι] (i : ι) (s : Finset ι) :
    parityFlip i (parityFlip i s) = s := by
  by_cases h : i ∈ s
  · simp [parityFlip, h, Finset.insert_erase h]
  · simp [parityFlip, h, Finset.erase_insert h]

private theorem even_card_parityFlip {ι : Type*} [DecidableEq ι] (i : ι) (s : Finset ι) :
    Even (parityFlip i s).card ↔ ¬ Even s.card := by
  by_cases h : i ∈ s
  · have h1 : 1 ≤ s.card := Finset.card_pos.mpr ⟨i, h⟩
    simp [parityFlip, h, Finset.card_erase_of_mem h, Nat.even_sub h1]
  · simp [parityFlip, h, Finset.card_insert_of_notMem h, Nat.even_add_one]

/-- **The subsets of even cardinality of a finite type number `2 ^ (n - 1)`.** On a nonempty type
that is half of all `2 ^ n` subsets: deleting a fixed point from the subsets that contain it, and
adjoining it to those that do not, is an involution of the subsets of `ι` reversing the parity of
the cardinality, so the two parities are equinumerous and together exhaust the `2 ^ n` subsets. The
empty type is the exception to that halving, and is covered separately: it has no fixed point to
flip, and its lone subset `∅` is even with no odd subset to pair it with, so the two parities are
not equinumerous there — but `2 ^ (0 - 1) = 1` counts that one even subset all the same, which is
why the statement needs no nonemptiness hypothesis. (Its odd counterpart
`TauCeti.card_odd_card_finset` does need one: the empty type has no subset of odd cardinality.) -/
theorem card_even_card_finset {ι : Type*} [Finite ι] :
    Nat.card {S : Finset ι // Even S.card} = 2 ^ (Nat.card ι - 1) := by
  classical
  let _ := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hne
  · rw [Nat.card_eq_zero.mpr (Or.inl hι), Nat.zero_sub, pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun _ _ => Subtype.ext (Finset.ext fun x => (hι.false x).elim)⟩, ⟨⟨∅, by simp⟩⟩⟩
  obtain ⟨i⟩ := hne
  have hbij : (Finset.univ.filter fun s : Finset ι => Even s.card).card
      = (Finset.univ.filter fun s : Finset ι => ¬ Even s.card).card := by
    refine Finset.card_bij' (fun s _ => parityFlip i s) (fun s _ => parityFlip i s) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      exact fun hcon => (even_card_parityFlip i s).mp hcon hs
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      exact (even_card_parityFlip i s).mpr hs
    · exact fun s _ => parityFlip_parityFlip i s
    · exact fun s _ => parityFlip_parityFlip i s
  have htot : (Finset.univ.filter fun s : Finset ι => Even s.card).card
      + (Finset.univ.filter fun s : Finset ι => ¬ Even s.card).card = 2 ^ Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_finset]
  have hpow : 2 ^ Fintype.card ι = 2 * 2 ^ (Fintype.card ι - 1) := by
    have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  omega

/-- **Exactly half the subsets of a nonempty finite type have odd cardinality**, the other half of
`TauCeti.card_even_card_finset`. -/
theorem card_odd_card_finset {ι : Type*} [Finite ι] [Nonempty ι] :
    Nat.card {S : Finset ι // Odd S.card} = 2 ^ (Nat.card ι - 1) := by
  classical
  let _ := Fintype.ofFinite ι
  have heven := card_even_card_finset (ι := ι)
  have htot : (Finset.univ.filter fun s : Finset ι => Even s.card).card
      + (Finset.univ.filter fun s : Finset ι => ¬ Even s.card).card = 2 ^ Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_finset]
  have hodd : (Finset.univ.filter fun s : Finset ι => ¬ Even s.card).card
      = (Finset.univ.filter fun s : Finset ι => Odd s.card).card := by
    simp only [Nat.not_even_iff_odd]
  have hpow : 2 ^ Fintype.card ι = 2 * 2 ^ (Fintype.card ι - 1) := by
    have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card] at heven
  omega

end TauCeti

namespace Finset

open scoped symmDiff

/-- Every pair in the product of disjoint finsets has distinct coordinates. -/
theorem filter_ne_product_of_disjoint {s t : Finset α} [DecidableEq α] (hst : Disjoint s t) :
    (s ×ˢ t).filter (fun p => p.1 ≠ p.2) = s ×ˢ t :=
  filter_true_of_mem fun _ hp =>
    hst.forall_ne_finset (mem_product.mp hp).1 (mem_product.mp hp).2

/-- **The symmetric difference and the intersection account for both cardinalities.** The
symmetric difference is the union minus the intersection, and the union and the intersection
together have the two cardinalities as their total. -/
theorem card_symmDiff_add_two_mul_card_inter {α : Type*} [DecidableEq α] (s t : Finset α) :
    (s ∆ t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have hsub : s ∩ t ⊆ s ∪ t := inter_subset_left.trans subset_union_left
  have hcard : (s ∆ t).card = (s ∪ t).card - (s ∩ t).card := by
    rw [symmDiff_eq_sup_sdiff_inf, sup_eq_union, inf_eq_inter, card_sdiff,
      inter_eq_left.2 hsub]
  have hunion := card_union_add_card_inter s t
  have hle : (s ∩ t).card ≤ (s ∪ t).card := card_le_card hsub
  omega

/-- **A symmetric difference has even cardinality exactly when its two arguments have the same
cardinality parity.** -/
@[simp]
theorem even_card_symmDiff_iff {α : Type*} [DecidableEq α] (s t : Finset α) :
    Even (s ∆ t).card ↔ (Even s.card ↔ Even t.card) := by
  have h := card_symmDiff_add_two_mul_card_inter s t
  simp only [Nat.even_iff]
  omega

/-- A transposition fixes the pair it transposes. -/
theorem map_swap_pair {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).map (Equiv.swap a b).toEmbedding = {a, b} := by
  simp [Finset.pair_comm]

/-- A transposition moves a pair along its first index, provided the second index is fixed. -/
theorem map_swap_pair_right {α : Type*} [DecidableEq α] {a b c : α} (hca : c ≠ a) (hcb : c ≠ b) :
    ({b, c} : Finset α).map (Equiv.swap a b).toEmbedding = {a, c} := by
  simp [Equiv.swap_apply_of_ne_of_ne hca hcb]

/-- **A transposition fixes a finset exactly when the two transposed points have the same
membership.** -/
theorem map_swap_eq_self_iff {α : Type*} [DecidableEq α] (a b : α) (s : Finset α) :
    s.map (Equiv.swap a b).toEmbedding = s ↔ (a ∈ s ↔ b ∈ s) := by
  constructor
  · intro h
    have ha := Finset.ext_iff.1 h a
    rw [mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_left] at ha
    exact ha.symm
  · intro h
    ext x
    rw [mem_map_equiv, Equiv.symm_swap]
    rcases eq_or_ne x a with rfl | hx
    · rw [Equiv.swap_apply_left]
      exact h.symm
    · rcases eq_or_ne x b with rfl | hx'
      · rw [Equiv.swap_apply_right]
        exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hx hx']

/-- A pair whose first coordinate is neither transposed point lies in a finset of pairs with
the first coordinates transposed exactly when it lies in the finset. -/
theorem mem_map_swap_prodCongr_refl_iff_of_ne {α β : Type*} [DecidableEq α] {a b : α}
    (s : Finset (α × β)) {p : α × β} (ha : p.1 ≠ a) (hb : p.1 ≠ b) :
    p ∈ s.map ((Equiv.swap a b).prodCongr (Equiv.refl β)).toEmbedding ↔ p ∈ s := by
  rcases p with ⟨x, y⟩
  simp only [mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- A pair lies in a finset of pairs with the first coordinates transposed exactly when the pair
with its first coordinate transposed lies in the finset. -/
theorem mk_mem_map_swap_prodCongr_refl_iff {α β : Type*} [DecidableEq α] (a b : α)
    (s : Finset (α × β)) (x : α) (y : β) :
    (x, y) ∈ s.map ((Equiv.swap a b).prodCongr (Equiv.refl β)).toEmbedding ↔
      (Equiv.swap a b x, y) ∈ s := by
  simp only [mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]

/-- Membership in a transposed finset with the two transposed points toggled. -/
theorem mem_map_swap_symmDiff_pair_iff {α : Type*} [DecidableEq α] (a b : α) (s : Finset α)
    (x : α) :
    x ∈ s.map (Equiv.swap a b).toEmbedding ∆ ({a, b} : Finset α) ↔
      (Equiv.swap a b x ∈ s ↔ x ≠ a ∧ x ≠ b) := by
  simp only [mem_symmDiff, mem_map_equiv, Equiv.symm_swap, mem_insert, mem_singleton]
  grind

/-- **Transposing two points of a finset and toggling both is an involution.** -/
theorem involutive_map_swap_symmDiff_pair {α : Type*} [DecidableEq α] (a b : α) :
    Function.Involutive fun s : Finset α => s.map (Equiv.swap a b).toEmbedding ∆ {a, b} := by
  intro s
  ext x
  simp only [mem_map_swap_symmDiff_pair_iff, Equiv.swap_apply_self]
  grind

/-- **Transposing two points of a finset and toggling both fixes it exactly when the two points
have opposite membership.** -/
theorem map_swap_symmDiff_pair_eq_self_iff {α : Type*} [DecidableEq α] (a b : α) (s : Finset α) :
    s.map (Equiv.swap a b).toEmbedding ∆ ({a, b} : Finset α) = s ↔ (a ∈ s ↔ b ∉ s) := by
  constructor
  · intro h
    have hb := (mem_map_swap_symmDiff_pair_iff a b s b).symm.trans (Finset.ext_iff.1 h b)
    rw [Equiv.swap_apply_right] at hb
    have hbb : ¬(b ≠ a ∧ b ≠ b) := fun hc => hc.2 rfl
    tauto
  · intro h
    ext x
    rw [mem_map_swap_symmDiff_pair_iff]
    rcases eq_or_ne x a with rfl | hx
    · rw [Equiv.swap_apply_left]
      have hxx : ¬(x ≠ x ∧ x ≠ b) := fun hc => hc.1 rfl
      tauto
    · rcases eq_or_ne x b with rfl | hx'
      · rw [Equiv.swap_apply_right]
        have hxx : ¬(x ≠ a ∧ x ≠ x) := fun hc => hc.2 rfl
        tauto
      · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
        tauto

/-- The two coordinates of every element of a finite set of natural-number pairs lie below a
common bound. -/
theorem exists_nat_prod_lt (I : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∀ p ∈ I, p.1 < n ∧ p.2 < n := by
  refine ⟨(I.sup fun p ↦ max p.1 p.2) + 1, fun p hp ↦ ?_⟩
  have hle := le_sup (f := fun p : ℕ × ℕ ↦ max p.1 p.2) hp
  omega

/-- A permutation of `ℕ` that fixes a finite set `I` pointwise and carries a finite set `J`,
disjoint from `I`, past `n`. -/
theorem exists_perm_eqOn_le_apply (I J : Finset ℕ) (hIJ : Disjoint I J) (n : ℕ) :
    ∃ ρ : Equiv.Perm ℕ, (∀ i ∈ I, ρ i = i) ∧ ∀ j ∈ J, n ≤ ρ j := by
  classical
  -- shift `J` by `N`, large enough to clear both `n` and everything in `I`
  set N : ℕ := n + (I ∪ J).sup id + 1
  let g : ↥(I ∪ J) → ℕ := fun x => if (x : ℕ) ∈ I then x else x + N
  -- every element of `J` is sent past `N`, hence past everything in `I ∪ J`
  have hbig : ∀ x : ↥(I ∪ J), (x : ℕ) < N := fun x => by
    have := Finset.le_sup (f := id) x.property
    simp only [id] at this; omega
  have hg : Function.Injective g := by
    intro x y hxy
    simp only [g] at hxy
    apply Subtype.ext
    have hx := hbig x
    have hy := hbig y
    split_ifs at hxy <;> omega
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair (fun x : ↥(I ∪ J) => (x : ℕ)) g
    Subtype.val_injective hg
  refine ⟨ρ, fun i hi => ?_, fun j hj => ?_⟩
  · have := hρ ⟨i, Finset.mem_union_left _ hi⟩
    simpa [g, hi] using this
  · have hjI : j ∉ I := Finset.disjoint_right.mp hIJ hj
    have := hρ ⟨j, Finset.mem_union_right _ hj⟩
    simp only [g, hjI, ite_false] at this
    rw [this]; omega

open Classical in
/-- A double sum over a chain `a ≤ b ≤ c`, summed first over `b` and then over `c`, can instead
be summed first over `c` and then over the interval of possible `b`. -/
theorem sum_filter_le_sum_filter_le {α M : Type*} [Fintype α] [LE α] [AddCommMonoid M]
    (a : α) (f : α → α → M) :
    ∑ b ∈ univ.filter (a ≤ ·), ∑ c ∈ univ.filter (b ≤ ·), f b c =
      ∑ c, ∑ b ∈ univ.filter (fun b => a ≤ b ∧ b ≤ c), f b c := by
  calc _ = ∑ b, ∑ c, if a ≤ b ∧ b ≤ c then f b c else 0 := by
        rw [sum_filter]
        refine sum_congr rfl fun b _ => ?_
        by_cases h : a ≤ b <;> simp [h, sum_filter]
    _ = _ := by
        rw [sum_comm]
        exact sum_congr rfl fun c _ => (sum_filter _ _).symm

/-- **The alternating sum over the subsets of a finset** is `1` for the empty finset and `0`
otherwise, in an arbitrary ring. Mathlib's `Finset.sum_powerset_neg_one_pow_card` is the case of
the integers. -/
@[simp]
theorem sum_powerset_neg_one_pow_card_of_ring {α R : Type*} [DecidableEq α] [Ring R]
    (s : Finset α) :
    ∑ t ∈ s.powerset, (-1 : R) ^ t.card = if s = ∅ then 1 else 0 := by
  have := congrArg (Int.cast : ℤ → R) (sum_powerset_neg_one_pow_card (x := s))
  push_cast at this
  exact this

/-- **A telescoping signed sum over the subsets of `P` vanishes.** If, for each `i ∈ P`, the
summand `g i` changes by `h i` when `i` is adjoined to a set not containing it, then
`∑_{T ⊆ P} (-1)^{|T|} (∑_{i ∈ P} g i T + ∑_{i ∈ T} h i T) = 0`: for fixed `i`, the sets `T ∌ i`
and `T ∪ {i}` cancel in pairs. -/
theorem sum_powerset_neg_one_pow_mul_eq_zero {ι R : Type*} [DecidableEq ι] [Ring R]
    (P : Finset ι) (g h : ι → Finset ι → R)
    (hstep : ∀ i ∈ P, ∀ t ∈ (P.erase i).powerset, g i t = g i (insert i t) + h i (insert i t)) :
    ∑ T ∈ P.powerset, (-1 : R) ^ T.card * (∑ i ∈ P, g i T + ∑ i ∈ T, h i T) = 0 := by
  have hT : ∀ T ∈ P.powerset, (-1 : R) ^ T.card * (∑ i ∈ P, g i T + ∑ i ∈ T, h i T) =
      ∑ i ∈ P, (-1 : R) ^ T.card * (g i T + if i ∈ T then h i T else 0) := fun T hT ↦ by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hT)]
  rw [Finset.sum_congr rfl hT, Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [← Finset.insert_erase hi, Finset.sum_powerset_insert (Finset.notMem_erase i P),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun t ht ↦ ?_
  have hit : i ∉ t := fun h ↦ Finset.notMem_erase i P (Finset.mem_powerset.mp ht h)
  simp only [hit, Finset.mem_insert_self, ↓reduceIte, Finset.card_insert_of_notMem hit,
    hstep i hi t ht]
  noncomm_ring

/-- **The Möbius function of the Boolean lattice, measured from the bottom.** The sets between `s`
and `t` are `s ∪ u` for `u ⊆ t \ s`, so the signed sum `∑_{s ⊆ u ⊆ t} (-1)^{|u| - |s|}` is the
alternating sum over the subsets of `t \ s`: it is `1` if `s = t` and `0` otherwise. -/
@[simp]
theorem sum_Icc_neg_one_pow_card_sub_card_left {α R : Type*} [DecidableEq α] [Ring R]
    (s t : Finset α) :
    ∑ u ∈ Icc s t, (-1 : R) ^ (u.card - s.card) = if s = t then 1 else 0 := by
  by_cases hst : s ⊆ t
  · have hdisj : ∀ u ∈ (t \ s).powerset, Disjoint s u := fun u hu =>
      disjoint_sdiff.mono_right (mem_powerset.1 hu)
    rw [Icc_eq_image_powerset hst, sum_image fun u hu v hv huv => by
      rw [← union_sdiff_cancel_left (hdisj u hu), huv, union_sdiff_cancel_left (hdisj v hv)]]
    have hcond : t \ s = ∅ ↔ s = t := by
      rw [sdiff_eq_empty_iff_subset]
      exact ⟨fun h => subset_antisymm hst h, fun h => h ▸ subset_rfl⟩
    rw [sum_congr rfl fun u hu => by
      rw [card_union_of_disjoint (hdisj u hu), Nat.add_sub_cancel_left],
      sum_powerset_neg_one_pow_card_of_ring]
    exact if_congr hcond rfl rfl
  · rw [Icc_eq_empty hst, sum_empty, ite_eq_right_iff.2 fun h => absurd h.le hst]

/-- **The Möbius function of the Boolean lattice, measured from the top.** The signed sum
`∑_{s ⊆ u ⊆ t} (-1)^{|t| - |u|}` is `1` if `s = t` and `0` otherwise: its terms differ from those
of `Finset.sum_Icc_neg_one_pow_card_sub_card_left` by the common sign `(-1)^{|t| - |s|}`. -/
@[simp]
theorem sum_Icc_neg_one_pow_card_sub_card_right {α R : Type*} [DecidableEq α] [Ring R]
    (s t : Finset α) :
    ∑ u ∈ Icc s t, (-1 : R) ^ (t.card - u.card) = if s = t then 1 else 0 := by
  have hsign (a b : ℕ) :
      (-1 : R) ^ a = (-1) ^ (a + b) * (-1) ^ b := by
    rw [← pow_add]
    apply neg_one_pow_congr
    grind
  have hterm : ∀ u ∈ Icc s t, (-1 : R) ^ (t.card - u.card) =
      (-1) ^ (t.card - s.card) * (-1) ^ (u.card - s.card) := fun u hu => by
    obtain ⟨hsu, hut⟩ := mem_Icc.1 hu
    have hs := card_le_card hsu
    have ht := card_le_card hut
    rw [← (tsub_add_tsub_cancel ht hs)]
    exact hsign _ _
  rw [sum_congr rfl hterm, ← mul_sum, sum_Icc_neg_one_pow_card_sub_card_left]
  split_ifs with h <;> simp [h]

/-- **Inserting a new element and deleting an existing element of an ordered finset in either order
gives opposite Koszul signs.** For `c ∉ s` and `k ∈ s` in a linear order, the sign of inserting `c`
into `s` and then deleting `k` is the opposite of the sign of deleting `k` from `s` and then
inserting `c`. -/
theorem neg_one_pow_card_filter_lt_mul_insert {α R : Type*} [LinearOrder α] [Monoid R]
    [HasDistribNeg R]
    {s : Finset α} {c k : α} (hc : c ∉ s) (hk : k ∈ s) :
    (-1 : R) ^ ({j ∈ s | j < c}).card * (-1) ^ ({j ∈ insert c s | j < k}).card =
      -((-1) ^ ({j ∈ s | j < k}).card * (-1) ^ ({j ∈ s.erase k | j < c}).card) := by
  have hck : c ≠ k := fun h ↦ hc (h ▸ hk)
  rcases hck.lt_or_gt with h | h
  · have hcs : c ∉ {j ∈ s | j < k} := by simp [hc]
    have hkc : k ∉ {j ∈ s | j < c} := by simp [h.not_gt]
    simp only [filter_insert, h, ↓reduceIte, card_insert_of_notMem hcs, filter_erase,
      erase_eq_of_notMem hkc, pow_succ]
    simp [← pow_add, add_comm]
  · have hkc : k ∈ {j ∈ s | j < c} := mem_filter.2 ⟨hk, h⟩
    simp only [filter_insert, h.not_gt, ↓reduceIte, filter_erase, ← card_erase_add_one hkc,
      pow_succ]
    simp [← pow_add, add_comm]

/-- **Deleting two distinct elements of an ordered finset in either order gives opposite Koszul
signs.** -/
theorem neg_one_pow_card_filter_lt_mul_erase {α R : Type*} [LinearOrder α] [Monoid R]
    [HasDistribNeg R]
    {s : Finset α} {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    (-1 : R) ^ ({k ∈ s | k < i}).card * (-1) ^ ({k ∈ s.erase i | k < j}).card =
      -((-1) ^ ({k ∈ s | k < j}).card * (-1) ^ ({k ∈ s.erase j | k < i}).card) := by
  rcases hij.lt_or_gt with hij | hji
  · have hi' : i ∈ {k ∈ s | k < j} := mem_filter.2 ⟨hi, hij⟩
    have hj' : j ∉ {k ∈ s | k < i} := by simp [hij.not_gt]
    simp only [filter_erase, erase_eq_of_notMem hj', ← card_erase_add_one hi', pow_succ]
    simp [← pow_add, add_comm]
  · have hi' : i ∉ {k ∈ s | k < j} := by simp [hji.not_gt]
    have hj' : j ∈ {k ∈ s | k < i} := mem_filter.2 ⟨hj, hji⟩
    simp only [filter_erase, erase_eq_of_notMem hi', ← card_erase_add_one hj', pow_succ]
    simp [← pow_add, add_comm]

/-- **Inserting two distinct new elements into an ordered finset in either order gives opposite
Koszul signs.** -/
theorem neg_one_pow_card_filter_lt_mul_insert_insert {α R : Type*} [LinearOrder α] [Monoid R]
    [HasDistribNeg R] {s : Finset α} {i j : α} (hi : i ∉ s) (hj : j ∉ s) (hij : i ≠ j) :
    (-1 : R) ^ ({k ∈ s | k < i}).card * (-1) ^ ({k ∈ insert i s | k < j}).card =
      -((-1) ^ ({k ∈ s | k < j}).card * (-1) ^ ({k ∈ insert j s | k < i}).card) := by
  rcases hij.lt_or_gt with hij | hji
  · have hi' : i ∉ {k ∈ s | k < j} := by simp [hi]
    simp only [filter_insert, hij, hij.not_gt, ↓reduceIte, card_insert_of_notMem hi', pow_succ]
    simp [← pow_add, add_comm]
  · have hj' : j ∉ {k ∈ s | k < i} := by simp [hj]
    simp only [filter_insert, hji, hji.not_gt, ↓reduceIte, card_insert_of_notMem hj', pow_succ]
    simp [← pow_add, add_comm]

/-- Splitting a finset of a linear order at one of its elements: the elements below it and the
elements above it account for all the others. -/
theorem card_filter_lt_add_card_filter_gt_add_one {α : Type*} [LinearOrder α] {s : Finset α} {t : α}
    (ht : t ∈ s) : #{x ∈ s | x < t} + #{x ∈ s | t < x} + 1 = #s := by
  rw [← card_erase_add_one ht,
    ← card_filter_add_card_filter_not (s := s.erase t) (p := fun x ↦ x < t)]
  have h₁ : {x ∈ s | x < t} = {x ∈ s.erase t | x < t} := by
    ext x; simp only [mem_filter, mem_erase]; grind
  have h₂ : {x ∈ s | t < x} = {x ∈ s.erase t | ¬ x < t} := by
    ext x; simp only [mem_filter, mem_erase]; grind
  rw [h₁, h₂]

/-- If an integer `d` cancels the cardinality of a finset `s`, then `d + 1` cancels the cardinality
of `s` with one of its elements removed. -/
theorem add_one_add_card_erase_eq_zero {α : Type*} [DecidableEq α] {s : Finset α} {t : α}
    (ht : t ∈ s) {d : ℤ} (hd : d + #s = 0) : d + 1 + #(s.erase t) = 0 := by
  have := card_erase_add_one ht
  omega

/-- If an integer `d` cancels the cardinality of a finset `s` of a linear order, then splitting `s`
at one of its elements `t`, the negated cardinalities of the elements below and above `t` add up to
`d + 1`. -/
theorem neg_card_filter_lt_add_neg_card_filter_gt {α : Type*} [LinearOrder α] {s : Finset α}
    {t : α} (ht : t ∈ s) {d : ℤ} (hd : d + #s = 0) :
    -(#{x ∈ s | x < t} : ℤ) + -(#{x ∈ s | t < x} : ℤ) = d + 1 := by
  have := card_filter_lt_add_card_filter_gt_add_one ht
  omega

/-- The elements of a finset inside `Ioo a b` that lie below `t` lie in `Ioo a t`. -/
theorem filter_lt_subset_Ioo {α : Type*} [Preorder α] [LocallyFiniteOrder α] {a b t : α}
    {s : Finset α} [DecidablePred (· < t)] (hs : s ⊆ Ioo a b) : {x ∈ s | x < t} ⊆ Ioo a t :=
  fun _ hx ↦ by
    rw [mem_filter] at hx
    exact mem_Ioo.2 ⟨(mem_Ioo.1 (hs hx.1)).1, hx.2⟩

/-- The elements of a finset inside `Ioo a b` that lie above `t` lie in `Ioo t b`. -/
theorem filter_gt_subset_Ioo {α : Type*} [Preorder α] [LocallyFiniteOrder α] {a b t : α}
    {s : Finset α} [DecidablePred (t < ·)] (hs : s ⊆ Ioo a b) : {x ∈ s | t < x} ⊆ Ioo t b :=
  fun _ hx ↦ by
    rw [mem_filter] at hx
    exact mem_Ioo.2 ⟨hx.2, (mem_Ioo.1 (hs hx.1)).2⟩

/-- If a monotone map `f` is not injective on a finset `T` inside `Ioo a b`, or does not map `T`
strictly between `f a` and `f b`, then it identifies two consecutive points `u < v` of
`a < T < b`, at least one of which lies in `T`. -/
theorem exists_adjacent_eq_of_not_card_image_and_image_subset_Ioo {α β : Type*} [LinearOrder α]
    [LocallyFiniteOrder α] [LinearOrder β] [LocallyFiniteOrder β] {f : α → β} (hf : Monotone f)
    {a b : α} {T : Finset α} (hT : T ⊆ Ioo a b)
    (h : ¬ (#(T.image f) = #T ∧ T.image f ⊆ Ioo (f a) (f b))) :
    ∃ u v, u < v ∧ (u = a ∨ u ∈ T) ∧ (v = b ∨ v ∈ T) ∧ (u ∈ T ∨ v ∈ T) ∧ f u = f v ∧
      ∀ s ∈ T, ¬ (u < s ∧ s < v) := by
  obtain ⟨u, v', huv', hu, hv', huv'T, hf'⟩ : ∃ u v', u < v' ∧ (u = a ∨ u ∈ T) ∧
      (v' = b ∨ v' ∈ T) ∧ (u ∈ T ∨ v' ∈ T) ∧ f u = f v' := by
    rw [not_and_or] at h
    rcases h with h | h
    · rw [card_image_iff, Set.InjOn] at h
      push Not at h
      obtain ⟨s, hs, s', hs', hfs, hne⟩ := h
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact ⟨s, s', hlt, Or.inr hs, Or.inr hs', Or.inl hs, hfs⟩
      · exact ⟨s', s, hlt, Or.inr hs', Or.inr hs, Or.inl hs', hfs.symm⟩
    · obtain ⟨y, hy, hy'⟩ := not_subset.1 h
      obtain ⟨s, hs, rfl⟩ := mem_image.1 hy
      have hs' := mem_Ioo.1 (hT hs)
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at hy'
      rcases hy' with hy' | hy'
      · exact ⟨a, s, hs'.1, Or.inl rfl, Or.inr hs, Or.inr hs, le_antisymm (hf hs'.1.le) hy'⟩
      · exact ⟨s, b, hs'.2, Or.inr hs, Or.inl rfl, Or.inl hs, le_antisymm (hf hs'.2.le) hy'⟩
  -- Replace `v'` by the successor of `u` among `T ∪ {b}`.
  set V := {y ∈ insert b T | u < y}
  have hV : v' ∈ V := mem_filter.2 ⟨by rcases hv' with rfl | hv' <;> simp [*], huv'⟩
  have hvV := V.min'_mem ⟨v', hV⟩
  have hvv' : V.min' ⟨v', hV⟩ ≤ v' := V.min'_le v' hV
  rw [mem_filter, mem_insert] at hvV
  refine ⟨u, V.min' ⟨v', hV⟩, hvV.2, hu, hvV.1, ?_,
    le_antisymm (hf hvV.2.le) ((hf hvv').trans hf'.symm.le), ?_⟩
  · rcases hu with rfl | hu
    · rcases hvV.1 with hvb | hvT
      · exfalso
        rcases huv'T with h | h
        · exact lt_irrefl _ (mem_Ioo.1 (hT h)).1
        · exact not_le.2 (mem_Ioo.1 (hT h)).2 (hvb ▸ hvv')
      · exact Or.inr hvT
    · exact Or.inl hu
  · rintro s hs ⟨hus, hsv⟩
    exact not_le.2 hsv (V.min'_le s (mem_filter.2 ⟨mem_insert_of_mem hs, hus⟩))

/-- For a finset `S` inside `Ioo i j` and a monotone map `g`, the composite `f ∘ g` is injective
on `S` with image strictly between `f (g i)` and `f (g j)` exactly when `g` is injective on `S`
with image strictly between `g i` and `g j`, and `f` is injective on the image of `S` under `g`
with image strictly between `f (g i)` and `f (g j)`. -/
theorem card_image_comp_eq_and_image_comp_subset_Ioo_iff {α β γ : Type*} [PartialOrder α]
    [LocallyFiniteOrder α] [Preorder β] [LocallyFiniteOrder β] [Preorder γ]
    [LocallyFiniteOrder γ] [DecidableEq α] [DecidableEq β] (f : α → β) {g : γ → α}
    (hg : Monotone g) {i j : γ} {S : Finset γ} (hS : S ⊆ Ioo i j) :
    (#(S.image (f ∘ g)) = #S ∧ S.image (f ∘ g) ⊆ Ioo (f (g i)) (f (g j))) ↔
      (#(S.image g) = #S ∧ S.image g ⊆ Ioo (g i) (g j)) ∧
        (#((S.image g).image f) = #(S.image g) ∧
          (S.image g).image f ⊆ Ioo (f (g i)) (f (g j))) := by
  rw [← image_image]
  constructor
  · rintro ⟨hc, hsub⟩
    have h₁ := card_image_le (s := S.image g) (f := f)
    have h₂ := card_image_le (s := S) (f := g)
    refine ⟨⟨by omega, fun y hy ↦ ?_⟩, by omega, hsub⟩
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hy
    have hs' := mem_Ioo.1 (hS hs)
    have hf := mem_Ioo.1 (hsub (mem_image_of_mem f hy))
    refine mem_Ioo.2 ⟨lt_of_le_of_ne (hg hs'.1.le) fun he ↦ ?_,
      lt_of_le_of_ne (hg hs'.2.le) fun he ↦ ?_⟩
    · rw [← he] at hf
      exact lt_irrefl _ hf.1
    · rw [he] at hf
      exact lt_irrefl _ hf.2
  · rintro ⟨⟨hcg, -⟩, hcf, hsub⟩
    exact ⟨hcf.trans hcg, hsub⟩

/-- The sum over a finite type of a function that vanishes away from two distinct points is the sum
of its values at those two points. -/
theorem sum_eq_two {α M : Type*} [Fintype α] [AddCommMonoid M] (f : α → M) (a b : α)
    (hab : a ≠ b) (h : ∀ x, x ≠ a → x ≠ b → f x = 0) : ∑ x, f x = f a + f b := by
  classical
  -- The summand vanishes away from the pair `a`, `b`, so the sum over the whole type is the sum
  -- over the two-point finset, which `Finset.sum_pair` evaluates.
  calc (∑ x, f x) = ∑ x ∈ ({a, b} : Finset α), f x := by
        refine (Finset.sum_subset (s₁ := ({a, b} : Finset α)) (s₂ := (Finset.univ : Finset α))
          (fun x _ => Finset.mem_univ x) ?_).symm
        intro x _ hx
        have hx' : x ≠ a ∧ x ≠ b := by simpa using hx
        exact h x hx'.1 hx'.2
    _ = f a + f b := Finset.sum_pair hab

/-- The double sum over a pair of finite types of a function that vanishes outside the four cells
of the rectangle `i`, `i'` by `j`, `j'` is the sum of its four values there. -/
theorem sum_eq_four {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M] (g : ι → κ → M)
    (i i' : ι) (j j' : κ) (hi'ne : i ≠ i') (hj'ne : j ≠ j')
    (h0 : ∀ x y, ¬(x = i ∧ y = j) → ¬(x = i ∧ y = j') → ¬(x = i' ∧ y = j)
      → ¬(x = i' ∧ y = j') → g x y = 0) :
    (∑ x, ∑ y, g x y) = g i j + g i j' + g i' j + g i' j' := by
  classical
  have hzero (x : ι) (hx : x ≠ i) (hx' : x ≠ i') : (∑ y, g x y) = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    exact h0 x y (fun h => hx h.1) (fun h => hx h.1) (fun h => hx' h.1) (fun h => hx' h.1)
  calc (∑ x, ∑ y, g x y) = (∑ y, g i y) + (∑ y, g i' y) :=
        sum_eq_two (fun x => ∑ y, g x y) i i' hi'ne (fun x hx hx' => hzero x hx hx')
    _ = (g i j + g i j') + (g i' j + g i' j') := by
        rw [sum_eq_two (g i) j j' hj'ne (fun y hyj hyj' => h0 i y (fun h => hyj h.2)
              (fun h => hyj' h.2) (fun h => hi'ne h.1) (fun h => hi'ne h.1)),
            sum_eq_two (g i') j j' hj'ne (fun y hyj hyj' => h0 i' y (fun h => hi'ne h.1.symm)
              (fun h => hi'ne h.1.symm) (fun h => hyj h.2) (fun h => hyj' h.2))]
    _ = g i j + g i j' + g i' j + g i' j' := by simp only [add_assoc]

end Finset

namespace TauCeti

-- The bijection below is Mathlib's, taken from the inline argument in
-- `ContinuousMultilinearMap.changeOrigin_toFormalMultilinearSeries`.
/-- **Summing over the subsets of size one less than `card ι` is summing over the points.** Such a
subset is the complement of a singleton, and `Finset.piecewise` against such a complement is
`Function.update` at the missing point, so a sum of `F` over those subsets is a sum over `ι`.

Use it to turn a formula indexed by the subsets that omit a single point into one indexed by the
omitted point. -/
theorem sum_piecewise_eq_sum_update_of_card_eq_succ {ι : Type*} {α : ι → Type*} {M : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid M] {m : ℕ} (hm : Fintype.card ι = m + 1)
    (F : ((i : ι) → α i) → M) (f g : (i : ι) → α i) :
    (∑ s : {s : Finset ι // s.card = m}, F (s.1.piecewise f g)) =
      ∑ i : ι, F (Function.update f i (g i)) := by
  refine (Fintype.sum_equiv (e := (Set.powersetCard.ofSingleton.trans
    (Set.powersetCard.compl hm.symm)).trans
      (Equiv.subtypeEquivRight fun _ ↦ Set.powersetCard.mem_iff)) _ _ fun i ↦ ?_).symm
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.subtypeEquivRight_apply,
    Set.powersetCard.coe_compl, Set.powersetCard.coe_ofSingleton, Finset.compl_singleton,
    Finset.piecewise_erase_univ]

end TauCeti
