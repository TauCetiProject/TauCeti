/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.PowersetCard
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-!
# Finite-set infrastructure

* `TauCeti.product_union_eq_union_product` rearranges a union of products of finsets.
* `TauCeti.card_nonempty_finset` counts the nonempty finsets of a finite type.
* `Finset.sum_powerset_neg_one_pow_mul_eq_zero` pairs subsets that differ by one element
  to cancel a signed sum.
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

/-- **A telescoping signed sum over the subsets of `P` vanishes.** If, for each `i ∈ P`, the
summand `g i` changes by `h i` when `i` is adjoined to a set not containing it, then
`∑_{T ⊆ P} (-1)^{|T|} (∑_{i ∈ P} g i T + ∑_{i ∈ T} h i T) = 0`: for fixed `i`, the sets `T ∌ i`
and `T ∪ {i}` cancel in pairs. -/
theorem sum_powerset_neg_one_pow_mul_eq_zero {ι R : Type*} [DecidableEq ι] [CommRing R]
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
  ring

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
