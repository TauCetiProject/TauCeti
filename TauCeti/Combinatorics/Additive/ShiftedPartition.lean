/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# Recovering a partition from a shifted partition

Let `t` be an element of infinite additive order in an additive cancellative monoid (for instance
`t = 1` in `ℤ`). If a finite set is split into two blocks `A ∪ B` in two ways, `A ∪ B = C ∪ D`,
and translating the first block by `t` again gives the same set in both ways,
`(t +ᵥ A) ∪ B = (t +ᵥ C) ∪ D`, with all unions disjoint, then the two splittings coincide:
`A = C` and `B = D` (`Finset.eq_and_eq_of_union_eq_of_vadd_finset_union_eq`).

The proof compares multiplicities. Subtracting the two partitions shows that the difference of
the multiplicity functions of `A` and `C` is invariant under translation by `t`; a finitely
supported function invariant under translation by an element of infinite order vanishes. In this
form the statement holds for multisets, with sums in place of disjoint unions
(`Multiset.eq_of_add_eq_of_map_add_add_eq`).

For `t = 1` in `ℤ` this is the shifted-partition lemma used to identify Hodge–Tate weights from two
character twists differing by one (Allen–Calegari–Caraiani–Gee–Helm–Le Hung–Newton–Scholze–Taylor–
Thorne, *Potential automorphy over CM fields*, Lemma 4.5.2). That lemma also assumes that `A`, `B`,
`C`, `D` have the same cardinality and that every element of `C` exceeds every element of `D`; the
multiplicity argument uses neither, and of the four disjointness conditions only two are needed.

## Main results

* `Multiset.eq_of_add_eq_of_map_add_add_eq`: if `A + B = C + D` and
  `A.map (t + ·) + B = C.map (t + ·) + D` with `t` of infinite order, then `A = C`.
* `Finset.eq_and_eq_of_union_eq_of_vadd_finset_union_eq`: the finite-set version, concluding
  `A = C` and `B = D`.
-/

public section

open scoped Pointwise

variable {G : Type*} [AddCancelMonoid G] {t : G}

namespace Multiset

/-- **Shifted partition recovery** for multisets. If `A + B = C + D` and translating the first
summand by an element `t` of infinite order preserves the equality,
`A.map (t + ·) + B = C.map (t + ·) + D`, then `A = C` (and hence `B = D`). -/
theorem eq_of_add_eq_of_map_add_add_eq (ht : ¬IsOfFinAddOrder t) {A B C D : Multiset G}
    (h : A + B = C + D) (h' : A.map (t + ·) + B = C.map (t + ·) + D) : A = C := by
  classical
  -- The difference of the multiplicities of `A` and `C` is invariant under `x ↦ t + x` ...
  have hstep (x : G) :
      (count (t + x) A : ℤ) - count (t + x) C = count x A - count x C := by
    have h₁ := congrArg (count (t + x)) h
    have h₂ := congrArg (count (t + x)) h'
    simp only [count_add, count_map_eq_count' _ _ (add_right_injective t)] at h₁ h₂
    omega
  have hiter (n : ℕ) (x : G) :
      (count (n • t + x) A : ℤ) - count (n • t + x) C = count x A - count x C := by
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul', add_assoc, hstep, ih]
  -- ... so a point where they differ has an infinite orbit inside the finite support of `A + C`.
  ext x
  by_contra hx
  have hmem (n : ℕ) : n • t + x ∈ (A + C).toFinset := by
    have := hiter n x
    rw [mem_toFinset, mem_add]
    by_contra hc
    rw [not_or, ← count_eq_zero, ← count_eq_zero] at hc
    omega
  have hinj : Function.Injective fun n : ℕ ↦ n • t + x := fun _ _ hmn ↦
    injective_nsmul_iff_not_isOfFinAddOrder.mpr ht (add_right_cancel hmn)
  exact Set.infinite_range_of_injective hinj <|
    (A + C).toFinset.finite_toSet.subset <| Set.range_subset_iff.mpr hmem

end Multiset

namespace Finset

variable [DecidableEq G]

/-- **Shifted partition recovery**. Let `t` have infinite order. If `A ∪ B = C ∪ D` and
`(t +ᵥ A) ∪ B = (t +ᵥ C) ∪ D`, where `C ∪ D` and `(t +ᵥ A) ∪ B` are disjoint unions, then
`A = C` and `B = D`. The remaining unions `A ∪ B` and `(t +ᵥ C) ∪ D` are then disjoint as well,
by counting. -/
theorem eq_and_eq_of_union_eq_of_vadd_finset_union_eq (ht : ¬IsOfFinAddOrder t)
    {A B C D : Finset G} (hCD : Disjoint C D) (hAB : Disjoint (t +ᵥ A) B) (h : A ∪ B = C ∪ D)
    (h' : (t +ᵥ A) ∪ B = (t +ᵥ C) ∪ D) : A = C ∧ B = D := by
  -- Counting shows that the other two unions are disjoint too.
  have hcard : #(A ∪ B) = #A + #B ∧ #((t +ᵥ C) ∪ D) = #(t +ᵥ C) + #D := by
    have h₁ := congrArg card h
    have h₂ := congrArg card h'
    have := card_union_le A B
    have := card_union_le (t +ᵥ C) D
    rw [card_union_of_disjoint hCD] at h₁
    rw [card_union_of_disjoint hAB] at h₂
    simp only [card_vadd_finset] at h₂ this ⊢
    omega
  have hval {s u : Finset G} (hsu : Disjoint s u) : (s ∪ u).val = s.val + u.val := by
    rw [union_val, Multiset.add_eq_union_iff_disjoint.mpr (disjoint_val.mpr hsu)]
  have hmap (s : Finset G) : (t +ᵥ s).val = s.val.map (t + ·) := by
    rw [vadd_finset_def]
    simp only [vadd_eq_add]
    exact image_val_of_injOn (add_right_injective t).injOn
  have hsum : A.val + B.val = C.val + D.val := by
    rw [← hval (card_union_eq_card_add_card.mp hcard.1), ← hval hCD, h]
  have hsum' : A.val.map (t + ·) + B.val = C.val.map (t + ·) + D.val := by
    rw [← hmap, ← hmap, ← hval hAB, ← hval (card_union_eq_card_add_card.mp hcard.2), h']
  obtain rfl := val_injective (Multiset.eq_of_add_eq_of_map_add_add_eq ht hsum hsum')
  exact ⟨rfl, val_injective (add_left_cancel hsum)⟩

end Finset
