/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Fork
import TauCeti.LinearAlgebra.RootSystem.FiniteType.AffineD

/-!
# Double-ended forks of `(-2)`-indices

A chain of `(-2)`-indices cannot have an additional leaf at both its second and its penultimate
component while remaining a proper subgraph of a numerical type. The two fork classifications
make every displayed edge simply laced and all component weights equal. The affine-`D` marks give
zero row sums on the chain and nonnegative row sums on the two leaves; a possible extra intersection
between the leaves only increases their row sums. This contradicts negative definiteness.

This is [Stacks, Lemma 55.5.11](https://stacks.math.columbia.edu/tag/0C8H). It is part of the
classification of proper connected subgraphs of `(-2)`-indices used to bound the multiplicities of
a minimal numerical type.

## Main result

* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.not_oppositeFork`: a proper chain of
  length at least four cannot carry distinct fork leaves at both ends.
-/

public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable {T : NumericalType.{u}} {t : ℕ} {c : ℕ → T.Component}
  {left right : T.Component}

namespace IsSelfIntersectionMinusTwoFork

/-- The leaf of a fork on the reversed chain is distinct from every original chain component. -/
lemma branch_ne_reverse
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left)
    {i : ℕ} (hi : i < t) : left ≠ c i := by
  have hreverse : t - 1 - (t - 1 - i) = i := by omega
  simpa only [hreverse] using hl.branch_ne (t - 1 - i) (by omega)

/-- The extra leaves of forks at opposite ends of a chain of length at least four are distinct. -/
lemma opposite_branch_ne (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left)
    (ht : 3 < t) : left ≠ right := by
  intro h
  have hrightZero : T.intersection (c 1) right = 0 :=
    hr.branch_intersection_eq_zero (by omega) (by omega)
  have hleftPos : 0 < T.intersection (c 1) left := by
    have hreverse : t - 1 - (t - 2) = 1 := by omega
    simpa only [hreverse] using hl.branch_intersection_pos
  rw [h, hrightZero] at hleftPos
  exact lt_irrefl 0 hleftPos

private def doubleForkEmbedding (t : ℕ) (c : ℕ → T.Component) (left right : T.Component) :
    DoubleForkIndex (t - 4) → T.Component
  | .inl i => if i = 0 then c 0 else left
  | .inr (.inl i) => c (i + 1)
  | .inr (.inr i) => if i = 0 then c (t - 1) else right

private def doubleForkExtra (T : NumericalType) (left right : T.Component) (n : ℕ) :
    DoubleForkIndex n → DoubleForkIndex n → ℤ
  | .inl i, .inr (.inr j) => if i = 1 ∧ j = 1 then T.intersection left right else 0
  | .inr (.inr i), .inl j => if i = 1 ∧ j = 1 then T.intersection right left else 0
  | _, _ => 0

private lemma doubleForkEmbedding_injective
    (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (ht : 3 < t) (hleftRight : left ≠ right)
    (hleft_ne_chain : ∀ i < t, left ≠ c i) :
    Function.Injective (doubleForkEmbedding t c left right) := by
  intro i j hij
  -- In each case `hij` equates two of `c 0`, `c (k + 1)`, `c (t - 1)`, `left` and `right`.
  rcases i with i | i | i <;> rcases j with j | j | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;>
    simp only [doubleForkEmbedding, Fin.zero_eta, Fin.isValue, Fin.mk_one, one_ne_zero,
      zero_ne_one, ↓reduceIte, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hij ⊢
  all_goals first
    | exact absurd hij (hleft_ne_chain _ (by omega))
    | exact absurd hij.symm (hleft_ne_chain _ (by omega))
    | exact absurd hij (hr.branch_ne _ (by omega))
    | exact absurd hij.symm (hr.branch_ne _ (by omega))
    | exact absurd hij hleftRight
    | exact absurd hij.symm hleftRight
    -- two chain components: `injOn` equates their positions, which settles the case
    | (have := hr.injOn _ (by omega) _ (by omega) hij; omega)

/-- The extra intersection block of the double-fork matrix is symmetric. -/
private lemma doubleForkExtra_comm (left right : T.Component) (n : ℕ)
    (k l : DoubleForkIndex n) :
    doubleForkExtra T left right n k l = doubleForkExtra T left right n l k := by
  rcases k with k | k | k <;> rcases l with l | l | l
  all_goals simp only [doubleForkExtra]
  case inl.inr.inr =>
    by_cases hk : k = 1
    · by_cases hl : l = 1
      · simpa [hk, hl] using T.intersection_comm left right
      · simp [hk, hl]
    · simp [hk]
  case inr.inr.inl =>
    by_cases hk : k = 1
    · by_cases hl : l = 1
      · simpa [hk, hl] using T.intersection_comm right left
      · simp [hk, hl]
    · simp [hk]

/-- The intersection matrix of the double fork on the two left leaves. -/
private lemma intersection_doubleForkEmbedding_inl_inl
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left)
    {w : ℤ} (hwleft : (T.weight left : ℤ) = w)
    (hchainEntry : ∀ i j, i < t → j < t →
      T.intersection (c i) (c j) =
        if i = j then -(2 * w) else if i + 1 = j ∨ j + 1 = i then w else 0)
    (hleftEntry : ∀ i, i < t → T.intersection (c i) left = if i = 1 then w else 0)
    (k l : Fin 2) :
    T.intersection (doubleForkEmbedding t c left right (.inl k))
        (doubleForkEmbedding t c left right (.inl l)) =
      -w * doubleForkCartanMatrix (t - 4) (.inl k) (.inl l) +
        doubleForkExtra T left right (t - 4) (.inl k) (.inl l) := by
  have ht := hl.two_lt
  simp only [doubleForkEmbedding]
  fin_cases k <;> fin_cases l
  all_goals dsimp
  · rw [hchainEntry 0 0 (by omega) (by omega)]
    simp [doubleForkExtra]
    ring_nf
  · rw [hleftEntry 0 (by omega)]
    simp [doubleForkExtra]
  · rw [T.intersection_comm, hleftEntry 0 (by omega)]
    simp [doubleForkExtra]
  · rw [hl.branch_intersection_self, hwleft]
    simp [doubleForkExtra]
    ring_nf

/-- The intersection matrix of the double fork between a left leaf and a middle vertex. -/
private lemma intersection_doubleForkEmbedding_inl_inr_inl (ht : 3 < t) {w : ℤ}
    (hchainEntry : ∀ i j, i < t → j < t →
      T.intersection (c i) (c j) =
        if i = j then -(2 * w) else if i + 1 = j ∨ j + 1 = i then w else 0)
    (hleftEntry : ∀ i, i < t → T.intersection (c i) left = if i = 1 then w else 0)
    (k : Fin 2) (l : Fin (t - 4 + 2)) :
    T.intersection (doubleForkEmbedding t c left right (.inl k))
        (doubleForkEmbedding t c left right (.inr (.inl l))) =
      -w * doubleForkCartanMatrix (t - 4) (.inl k) (.inr (.inl l)) +
        doubleForkExtra T left right (t - 4) (.inl k) (.inr (.inl l)) := by
  have hlt : (l : ℕ) + 1 < t := by have := l.isLt; omega
  simp only [doubleForkEmbedding]
  fin_cases k
  all_goals dsimp
  · rw [hchainEntry 0 (l + 1) (by omega) hlt]
    simp only [doubleForkExtra, doubleForkCartanMatrix_inl_inr_inl]
    by_cases hl0 : (l : ℕ) = 0
    · have : l = 0 := Fin.ext hl0
      subst l
      norm_num
    · simp [hl0]
  · rw [T.intersection_comm, hleftEntry (l + 1) hlt]
    simp only [doubleForkExtra, doubleForkCartanMatrix_inl_inr_inl]
    by_cases hl0 : (l : ℕ) = 0
    · have : l = 0 := Fin.ext hl0
      subst l
      norm_num
    · simp [hl0]

/-- The intersection matrix of the double fork between a left leaf and a right leaf. -/
private lemma intersection_doubleForkEmbedding_inl_inr_inr (ht : 3 < t) {w : ℤ}
    (hchainEntry : ∀ i j, i < t → j < t →
      T.intersection (c i) (c j) =
        if i = j then -(2 * w) else if i + 1 = j ∨ j + 1 = i then w else 0)
    (hrightEntry : ∀ i, i < t → T.intersection (c i) right = if i = t - 2 then w else 0)
    (hleftEntry : ∀ i, i < t → T.intersection (c i) left = if i = 1 then w else 0)
    (k l : Fin 2) :
    T.intersection (doubleForkEmbedding t c left right (.inl k))
        (doubleForkEmbedding t c left right (.inr (.inr l))) =
      -w * doubleForkCartanMatrix (t - 4) (.inl k) (.inr (.inr l)) +
        doubleForkExtra T left right (t - 4) (.inl k) (.inr (.inr l)) := by
  have hzero_ne_last : 0 ≠ t - 1 := by omega
  have hone_ne_last : 1 ≠ t - 1 := by omega
  have hlast_ne_one : t - 1 ≠ 1 := by omega
  have hzero_ne_penultimate : 0 ≠ t - 2 := by omega
  simp only [doubleForkEmbedding]
  fin_cases k <;> fin_cases l
  all_goals dsimp
  · rw [hchainEntry 0 (t - 1) (by omega) (by omega)]
    simp only [doubleForkCartanMatrix_inl_inr_inr, doubleForkExtra]
    simp [hzero_ne_last, hone_ne_last]
  · rw [hrightEntry 0 (by omega)]
    simp only [doubleForkCartanMatrix_inl_inr_inr, doubleForkExtra]
    simp only [hzero_ne_penultimate, ↓reduceIte]
    norm_num
  · rw [T.intersection_comm, hleftEntry (t - 1) (by omega)]
    simp only [doubleForkCartanMatrix_inl_inr_inr, doubleForkExtra]
    simp only [hlast_ne_one, ↓reduceIte]
    norm_num
  · norm_num [doubleForkExtra]

/-- The intersection matrix of the double fork on the middle vertices. -/
private lemma intersection_doubleForkEmbedding_inr_inl_inr_inl (ht : 3 < t) {w : ℤ}
    (hchainEntry : ∀ i j, i < t → j < t →
      T.intersection (c i) (c j) =
        if i = j then -(2 * w) else if i + 1 = j ∨ j + 1 = i then w else 0)
    (k l : Fin (t - 4 + 2)) :
    T.intersection (doubleForkEmbedding t c left right (.inr (.inl k)))
        (doubleForkEmbedding t c left right (.inr (.inl l))) =
      -w * doubleForkCartanMatrix (t - 4) (.inr (.inl k)) (.inr (.inl l)) +
        doubleForkExtra T left right (t - 4) (.inr (.inl k)) (.inr (.inl l)) := by
  simp only [doubleForkEmbedding, doubleForkExtra, doubleForkCartanMatrix_inr_inl_inr_inl]
  rw [hchainEntry (k + 1) (l + 1) (by have := k.isLt; omega) (by have := l.isLt; omega)]
  split_ifs <;> omega

/-- The intersection matrix of the double fork between a middle vertex and a right leaf. -/
private lemma intersection_doubleForkEmbedding_inr_inl_inr_inr (ht : 3 < t) {w : ℤ}
    (hchainEntry : ∀ i j, i < t → j < t →
      T.intersection (c i) (c j) =
        if i = j then -(2 * w) else if i + 1 = j ∨ j + 1 = i then w else 0)
    (hrightEntry : ∀ i, i < t → T.intersection (c i) right = if i = t - 2 then w else 0)
    (k : Fin (t - 4 + 2)) (l : Fin 2) :
    T.intersection (doubleForkEmbedding t c left right (.inr (.inl k)))
        (doubleForkEmbedding t c left right (.inr (.inr l))) =
      -w * doubleForkCartanMatrix (t - 4) (.inr (.inl k)) (.inr (.inr l)) +
        doubleForkExtra T left right (t - 4) (.inr (.inl k)) (.inr (.inr l)) := by
  have hlt : (k : ℕ) + 1 < t := by have := k.isLt; omega
  simp only [doubleForkEmbedding]
  fin_cases l
  all_goals dsimp
  · rw [hchainEntry (k + 1) (t - 1) hlt (by omega)]
    simp only [doubleForkExtra, doubleForkCartanMatrix_inr_inl_inr_inr]
    split_ifs <;> omega
  · rw [hrightEntry (k + 1) hlt]
    simp only [doubleForkExtra, doubleForkCartanMatrix_inr_inl_inr_inr]
    split_ifs <;> omega

/-- The intersection matrix of the double fork on the two right leaves. -/
private lemma intersection_doubleForkEmbedding_inr_inr_inr_inr
    (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    {w : ℤ} (hwright : (T.weight right : ℤ) = w)
    (hchainEntry : ∀ i j, i < t → j < t →
      T.intersection (c i) (c j) =
        if i = j then -(2 * w) else if i + 1 = j ∨ j + 1 = i then w else 0)
    (hrightEntry : ∀ i, i < t → T.intersection (c i) right = if i = t - 2 then w else 0)
    (k l : Fin 2) :
    T.intersection (doubleForkEmbedding t c left right (.inr (.inr k)))
        (doubleForkEmbedding t c left right (.inr (.inr l))) =
      -w * doubleForkCartanMatrix (t - 4) (.inr (.inr k)) (.inr (.inr l)) +
        doubleForkExtra T left right (t - 4) (.inr (.inr k)) (.inr (.inr l)) := by
  have ht := hr.two_lt
  have hlast_ne_penultimate : t - 1 ≠ t - 2 := by omega
  simp only [doubleForkEmbedding]
  fin_cases k <;> fin_cases l
  all_goals dsimp
  · rw [hchainEntry (t - 1) (t - 1) (by omega) (by omega)]
    simp [doubleForkExtra]
    ring_nf
  · rw [hrightEntry (t - 1) (by omega)]
    simp only [hlast_ne_penultimate, ↓reduceIte]
    norm_num [doubleForkExtra]
  · rw [T.intersection_comm, hrightEntry (t - 1) (by omega)]
    simp only [hlast_ne_penultimate, ↓reduceIte]
    norm_num [doubleForkExtra]
  · rw [hr.branch_intersection_self, hwright]
    simp [doubleForkExtra]
    ring_nf

private lemma intersection_doubleForkEmbedding_eq
    (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left)
    (ht : 3 < t) (w : ℕ+) (hwright : (T.weight right : ℤ) = w)
    (hwleft : (T.weight left : ℤ) = w)
    (hchainEntry : ∀ i j, i < t → j < t →
      T.intersection (c i) (c j) =
        if i = j then -(2 * (w : ℤ)) else if i + 1 = j ∨ j + 1 = i then w else 0)
    (hrightEntry : ∀ i, i < t →
      T.intersection (c i) right = if i = t - 2 then (w : ℤ) else 0)
    (hleftEntry : ∀ i, i < t →
      T.intersection (c i) left = if i = 1 then (w : ℤ) else 0)
    (i j : DoubleForkIndex (t - 4)) :
    T.intersection (doubleForkEmbedding t c left right i)
        (doubleForkEmbedding t c left right j) =
      -(w : ℤ) * doubleForkCartanMatrix (t - 4) i j +
        doubleForkExtra T left right (t - 4) i j := by
  have hswap (k l : DoubleForkIndex (t - 4))
      (h : T.intersection (doubleForkEmbedding t c left right l)
          (doubleForkEmbedding t c left right k) =
        -(w : ℤ) * doubleForkCartanMatrix (t - 4) l k +
          doubleForkExtra T left right (t - 4) l k) :
      T.intersection (doubleForkEmbedding t c left right k)
          (doubleForkEmbedding t c left right l) =
        -(w : ℤ) * doubleForkCartanMatrix (t - 4) k l +
          doubleForkExtra T left right (t - 4) k l := by
    rw [T.intersection_comm, h, ← (doubleForkCartanMatrix_isSymm (t - 4)).apply,
      doubleForkExtra_comm]
  have hll := intersection_doubleForkEmbedding_inl_inl (right := right) hl hwleft hchainEntry
    hleftEntry
  have hlm := intersection_doubleForkEmbedding_inl_inr_inl (right := right) ht hchainEntry
    hleftEntry
  have hlr := intersection_doubleForkEmbedding_inl_inr_inr (T := T) (c := c) ht hchainEntry
    hrightEntry hleftEntry
  have hmm := intersection_doubleForkEmbedding_inr_inl_inr_inl (left := left) (right := right)
    ht hchainEntry
  have hmr := intersection_doubleForkEmbedding_inr_inl_inr_inr (left := left) ht hchainEntry
    hrightEntry
  have hrr := intersection_doubleForkEmbedding_inr_inr_inr_inr (left := left) hr hwright
    hchainEntry hrightEntry
  rcases i with k | k | k <;> rcases j with l | l | l
  · exact hll k l
  · exact hlm k l
  · exact hlr k l
  · exact hswap _ _ (hlm l k)
  · exact hmm k l
  · exact hmr k l
  · exact hswap _ _ (hlr l k)
  · exact hswap _ _ (hmr l k)
  · exact hrr k l

/-- For a double fork of `(-2)`-indices in a numerical type with at least `t + 2` components, all
the weights are one common `w` and the intersection numbers of the chain components with each
other and with the two leaves are the simply laced ones. -/
private lemma exists_weight_intersection_entries
    (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left)
    (hcard : t + 1 < Fintype.card T.Component) :
    ∃ w : ℕ+, (T.weight right : ℤ) = w ∧ (T.weight left : ℤ) = w ∧
      (∀ i j, i < t → j < t →
        T.intersection (c i) (c j) =
          if i = j then -(2 * (w : ℤ)) else if i + 1 = j ∨ j + 1 = i then w else 0) ∧
      (∀ i, i < t → T.intersection (c i) right = if i = t - 2 then (w : ℤ) else 0) ∧
      (∀ i, i < t → T.intersection (c i) left = if i = 1 then (w : ℤ) else 0) := by
  have ht := hr.two_lt
  have hchainCard : t < Fintype.card T.Component := by omega
  have hreversePenultimate : t - 1 - (t - 2) = 1 := by omega
  -- Classifying the two forks fixes one common weight, every chain edge, and the two leaf edges.
  obtain ⟨w, hw, hwright, hedge, hrightEdge⟩ := hr.exists_weight_intersection_eq hcard
  obtain ⟨w', hw', hwleft', -, hleftEdge'⟩ := hl.exists_weight_intersection_eq hcard
  have hreverseLast : t - 1 - 0 = t - 1 := by omega
  have hww : (w' : ℤ) = w := by
    have hw'last : (T.weight (c (t - 1)) : ℤ) = w' := by
      simpa only [hreverseLast] using hw' 0 (by omega)
    exact hw'last.symm.trans (hw (t - 1) (by omega))
  have hleftEdge : T.intersection (c 1) left = w := by
    simpa only [hreversePenultimate, hww] using hleftEdge'
  have hleftZero : ∀ {i}, i < t → i ≠ 1 → T.intersection (c i) left = 0 := by
    intro i hi hi1
    have hreverse : t - 1 - (t - 1 - i) = i := by omega
    have hreverse_ne : t - 1 - i ≠ t - 2 := by omega
    simpa only [hreverse] using
      hl.branch_intersection_eq_zero (i := t - 1 - i) (by omega) hreverse_ne
  refine ⟨w, hwright, hwleft'.trans hww,
    fun i j hi hj ↦ hr.intersection_eq_ite hchainCard hw hedge hi hj, fun i hi ↦ ?_,
    fun i hi ↦ ?_⟩
  · split_ifs with hit
    · subst i
      exact hrightEdge
    · exact hr.branch_intersection_eq_zero hi hit
  · split_ifs with hi1
    · subst i
      exact hleftEdge
    · exact hleftZero hi hi1

/-- The intersection numbers of an injective family `doubleForkEmbedding` of the vertices of the
affine-`D` diagram are `-w` times its Cartan matrix plus a nonnegative off-diagonal block between
the two leaves; this contradicts negative definiteness when the family is a proper subset. -/
private lemma false_of_intersection_doubleForkEmbedding_eq
    (ht : 3 < t) (hleftRight : left ≠ right)
    (he : Function.Injective (doubleForkEmbedding t c left right))
    (hcard : t + 2 < Fintype.card T.Component) {w : ℤ}
    (hmatrix : ∀ i j : DoubleForkIndex (t - 4),
      T.intersection (doubleForkEmbedding t c left right i)
          (doubleForkEmbedding t c left right j) =
        -w * doubleForkCartanMatrix (t - 4) i j + doubleForkExtra T left right (t - 4) i j) :
    False := by
  let n := t - 4
  let e : DoubleForkIndex n → T.Component := doubleForkEmbedding t c left right
  let mark : DoubleForkIndex n → ℤ
    | .inl _ => 1
    | .inr (.inl _) => 2
    | .inr (.inr _) => 1
  let extra : DoubleForkIndex n → DoubleForkIndex n → ℤ :=
    doubleForkExtra T left right n
  have hmark (i : DoubleForkIndex n) : (mark i : ℚ) = doubleForkMark n i := by
    rcases i with i | i | i <;> simp [mark]
  have hcartan (i : DoubleForkIndex n) :
      ∑ j, doubleForkCartanMatrix n i j * mark j = 0 := by
    have hcast : ((↑(∑ j, doubleForkCartanMatrix n i j * mark j) : ℚ)) = 0 := by
      rw [Int.cast_sum]
      simp_rw [Int.cast_mul, hmark]
      exact sum_doubleForkCartanMatrix_mul_doubleForkMark_eq_zero n i
    exact Int.cast_injective hcast
  have hextra (i : DoubleForkIndex n) : 0 ≤ ∑ j, extra i j * mark j := by
    have hnonneg := T.offDiagonal_nonneg left right hleftRight
    rcases i with i | i | i
    · fin_cases i <;>
        simp [extra, doubleForkExtra, mark, Fintype.sum_sum_type, hnonneg]
    · simp [extra, doubleForkExtra]
    · fin_cases i <;>
        simp [extra, doubleForkExtra, mark, Fintype.sum_sum_type,
          T.intersection_comm right left, hnonneg]
  have hrow (i : DoubleForkIndex n) :
      0 ≤ ∑ j, T.intersection (e i) (e j) * mark j := by
    have hsum : ∑ j, T.intersection (e i) (e j) * mark j = ∑ j, extra i j * mark j := by
      calc
        ∑ j, T.intersection (e i) (e j) * mark j =
            ∑ j, (-w * doubleForkCartanMatrix n i j + extra i j) * mark j := by
          exact sum_congr rfl fun j _ ↦ by rw [hmatrix]
        _ = -w * (∑ j, doubleForkCartanMatrix n i j * mark j) +
            ∑ j, extra i j * mark j := by
          simp_rw [add_mul]
          rw [sum_add_distrib, mul_sum]
          ring_nf
        _ = ∑ j, extra i j * mark j := by rw [hcartan]; ring_nf
    calc
      0 ≤ ∑ j, extra i j * mark j := hextra i
      _ = ∑ j, T.intersection (e i) (e j) * mark j := hsum.symm
  have hindexCard : Fintype.card (DoubleForkIndex n) = t + 2 := by
    simp [n]
    omega
  exact (T.not_forall_fintype_sum_intersection_mul_nonneg_of_pos (y := mark) he
    (by rw [hindexCard]; exact hcard) (fun i ↦ by
      rcases i with _ | _ | _ <;> simp [mark]) ⟨Sum.inl 0, by simp [mark]⟩) hrow

/-- A chain of at least four `(-2)`-indices cannot have additional leaves meeting its second and
penultimate components when the displayed components form a proper subset of the numerical type.
The leaves are necessarily distinct, but they may intersect each other; the affine-`D` marks still
give nonnegative row sums ([Stacks, Lemma 55.5.11](https://stacks.math.columbia.edu/tag/0C8H)). -/
theorem not_oppositeFork (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left)
    (ht : 3 < t) (hcard : t + 2 < Fintype.card T.Component) : False := by
  have hleftRight := hr.opposite_branch_ne hl ht
  have hleft_ne_chain : ∀ i < t, left ≠ c i := fun _ hi ↦ hl.branch_ne_reverse hi
  obtain ⟨w, hwright, hwleft, hchainEntry, hrightEntry, hleftEntry⟩ :=
    exists_weight_intersection_entries hr hl (by omega)
  exact false_of_intersection_doubleForkEmbedding_eq ht hleftRight
    (doubleForkEmbedding_injective hr ht hleftRight hleft_ne_chain) hcard
    (intersection_doubleForkEmbedding_eq hr hl ht w hwright hwleft hchainEntry hrightEntry
      hleftEntry)

end IsSelfIntersectionMinusTwoFork

/-- Every component of a numerical type exhausted by a double fork `(c, left, right)` of chain
length `t ≥ 4` is `left`, `right`, or `c i` for some `i < t`. -/
lemma IsSelfIntersectionMinusTwoFork.eq_or_eq_or_exists_lt_eq_of_card_eq {t : ℕ}
    {c : ℕ → T.Component} {left right : T.Component}
    (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left) (ht : 4 ≤ t)
    (hcard : Fintype.card T.Component = t + 2) (v : T.Component) :
    v = left ∨ v = right ∨ ∃ i < t, c i = v := by
  classical
  have hleft_ne : ∀ i < t, left ≠ c i := fun _ hi ↦ hl.branch_ne_reverse hi
  have hlr := hr.opposite_branch_ne hl (by omega)
  have hr_notMem : right ∉ (range t).image c := by
    simp only [mem_image, mem_range, not_exists, not_and]
    exact fun i hi h ↦ hr.branch_ne i hi h.symm
  have hl_notMem : left ∉ insert right ((range t).image c) := by
    simp only [mem_insert, mem_image, mem_range, not_or, not_exists, not_and]
    exact ⟨hlr, fun i hi h ↦ hleft_ne i hi h.symm⟩
  have hu : insert left (insert right ((range t).image c)) = univ :=
    eq_univ_of_card _ (by
      rw [card_insert_of_notMem hl_notMem, card_insert_of_notMem hr_notMem,
        hr.card_image_range, hcard])
  simpa [← hu] using mem_univ v

end NumericalType

end TauCeti
