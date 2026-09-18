/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Set.PowersetCard
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NoncommRing

/-!
# Finite-set infrastructure

* `TauCeti.product_union_eq_union_product` rearranges a union of products of finsets.
* `TauCeti.card_nonempty_finset` counts the nonempty finsets of a finite type.
* `Finset.sum_powerset_neg_one_pow_mul_eq_zero` pairs subsets that differ by one element
  to cancel a signed sum.
* `Finset.sum_Icc_neg_one_pow_card_sub_card_left` and
  `Finset.sum_Icc_neg_one_pow_card_sub_card_right` compute the Möbius function of the Boolean
  lattice of finsets: the signed sum over an interval `[s, t]` is `1` if `s = t` and `0`
  otherwise.
* `Finset.sum_filter_le_sum_filter_le` reindexes a double sum over chains in a finite type with a
  `≤` relation.
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

end TauCeti

namespace Finset

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
theorem sum_Icc_neg_one_pow_card_sub_card_left {α R : Type*} [DecidableEq α] [Ring R]
    (s t : Finset α) :
    ∑ u ∈ Icc s t, (-1 : R) ^ (u.card - s.card) = if s = t then 1 else 0 := by
  by_cases hst : s ⊆ t
  · have hdisj : ∀ u ∈ (t \ s).powerset, Disjoint s u := fun u hu =>
      disjoint_sdiff.mono_right (mem_powerset.1 hu)
    rw [Icc_eq_image_powerset hst, sum_image fun u hu v hv huv => by
      rw [← union_sdiff_cancel_left (hdisj u hu), huv, union_sdiff_cancel_left (hdisj v hv)]]
    have hsum : ∑ u ∈ (t \ s).powerset, (-1 : R) ^ u.card = if t \ s = ∅ then 1 else 0 := by
      have := congrArg (Int.cast : ℤ → R) (sum_powerset_neg_one_pow_card (x := t \ s))
      push_cast at this
      exact this
    have hcond : t \ s = ∅ ↔ s = t := by
      rw [sdiff_eq_empty_iff_subset]
      exact ⟨fun h => subset_antisymm hst h, fun h => h ▸ subset_rfl⟩
    rw [sum_congr rfl fun u hu => by
      rw [card_union_of_disjoint (hdisj u hu), Nat.add_sub_cancel_left], hsum]
    exact if_congr hcond rfl rfl
  · rw [Icc_eq_empty hst, sum_empty, ite_eq_right_iff.2 fun h => absurd h.le hst]

/-- **The Möbius function of the Boolean lattice, measured from the top.** The signed sum
`∑_{s ⊆ u ⊆ t} (-1)^{|t| - |u|}` is `1` if `s = t` and `0` otherwise: its terms differ from those
of `Finset.sum_Icc_neg_one_pow_card_sub_card_left` by the common sign `(-1)^{|t| - |s|}`. -/
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

end Finset

namespace TauCeti

/-- The underlying `Finset` of `Set.powersetCard.ofSingleton a` is `{a}`. Mathlib states
`ofSingleton` by its defining data rather than through a coercion lemma, so name the one step of
definitional unfolding here instead of reducing a whole composite equivalence in place. -/
private lemma coe_ofSingleton {ι : Type*} (a : ι) :
    ((Set.powersetCard.ofSingleton a : Set.powersetCard ι 1) : Finset ι) = {a} := rfl

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
    Set.powersetCard.coe_compl, coe_ofSingleton, Finset.compl_singleton,
    Finset.piecewise_erase_univ]

end TauCeti
