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
  have hmiddle_lt (i : Fin (t - 4 + 2)) : (i : ℕ) + 1 < t := by
    have hi := i.isLt
    omega
  intro i j hij
  rcases i with i | i | i <;> rcases j with j | j | j
  · fin_cases i <;> fin_cases j
    · rfl
    · exact (hleft_ne_chain 0 (by omega)
        (by simpa [doubleForkEmbedding] using hij.symm)).elim
    · exact (hleft_ne_chain 0 (by omega)
        (by simpa [doubleForkEmbedding] using hij)).elim
    · rfl
  · exfalso
    fin_cases i
    · exact (hr.ne (i := 0) (j := j + 1) (by omega) (hmiddle_lt j) (by omega)
        (by simpa [doubleForkEmbedding] using hij)).elim
    · exact (hleft_ne_chain (j + 1) (hmiddle_lt j)
        (by simpa [doubleForkEmbedding] using hij)).elim
  · exfalso
    fin_cases i <;> fin_cases j
    · exact (hr.ne (i := 0) (j := t - 1) (by omega) (by omega) (by omega)
        (by simpa [doubleForkEmbedding] using hij)).elim
    · exact (hr.branch_ne 0 (by omega)
        (by simpa [doubleForkEmbedding] using hij.symm)).elim
    · exact (hleft_ne_chain (t - 1) (by omega)
        (by simpa [doubleForkEmbedding] using hij)).elim
    · exact (hleftRight (by simpa [doubleForkEmbedding] using hij)).elim
  · exfalso
    fin_cases j
    · exact (hr.ne (i := i + 1) (j := 0) (hmiddle_lt i) (by omega) (by omega)
        (by simpa [doubleForkEmbedding] using hij)).elim
    · exact (hleft_ne_chain (i + 1) (hmiddle_lt i)
        (by simpa [doubleForkEmbedding] using hij.symm)).elim
  · apply congrArg (Sum.inr ∘ Sum.inl)
    apply Fin.ext
    have := hr.injOn (i + 1) (hmiddle_lt i) (j + 1) (hmiddle_lt j)
      (by simpa [doubleForkEmbedding] using hij)
    omega
  · exfalso
    fin_cases j
    · exact (hr.ne (i := i + 1) (j := t - 1) (hmiddle_lt i) (by omega) (by omega)
        (by simpa [doubleForkEmbedding] using hij)).elim
    · exact (hr.branch_ne (i + 1) (hmiddle_lt i)
        (by simpa [doubleForkEmbedding] using hij.symm)).elim
  · exfalso
    fin_cases i <;> fin_cases j
    · exact (hr.ne (i := t - 1) (j := 0) (by omega) (by omega) (by omega)
        (by simpa [doubleForkEmbedding] using hij)).elim
    · exact (hleft_ne_chain (t - 1) (by omega)
        (by simpa [doubleForkEmbedding] using hij.symm)).elim
    · exact (hr.branch_ne 0 (by omega)
        (by simpa [doubleForkEmbedding] using hij)).elim
    · exact (hleftRight (by simpa [doubleForkEmbedding] using hij.symm)).elim
  · exfalso
    fin_cases i
    · exact (hr.ne (i := t - 1) (j := j + 1) (by omega) (hmiddle_lt j) (by omega)
        (by simpa [doubleForkEmbedding] using hij)).elim
    · exact (hr.branch_ne (j + 1) (hmiddle_lt j)
        (by simpa [doubleForkEmbedding] using hij)).elim
  · fin_cases i <;> fin_cases j
    · rfl
    · exact (hr.branch_ne (t - 1) (by omega)
        (by simpa [doubleForkEmbedding] using hij.symm)).elim
    · exact (hr.branch_ne (t - 1) (by omega)
        (by simpa [doubleForkEmbedding] using hij)).elim
    · rfl

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
  let n := t - 4
  let e : DoubleForkIndex n → T.Component := doubleForkEmbedding t c left right
  let extra : DoubleForkIndex n → DoubleForkIndex n → ℤ :=
    doubleForkExtra T left right n
  have hmiddle_lt (k : Fin (n + 2)) : (k : ℕ) + 1 < t := by
    have hk := k.isLt
    simp only [n] at hk
    omega
  have hzero_ne_last : 0 ≠ t - 1 := by omega
  have hone_ne_last : 1 ≠ t - 1 := by omega
  have hlast_ne_one : t - 1 ≠ 1 := by omega
  have hzero_ne_penultimate : 0 ≠ t - 2 := by omega
  have hlast_ne_penultimate : t - 1 ≠ t - 2 := by omega
  have hextra_comm (k l : DoubleForkIndex n) : extra k l = extra l k := by
    rcases k with k | k | k <;> rcases l with l | l | l
    all_goals simp only [extra, doubleForkExtra]
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
  -- The six blocks on and above the diagonal determine the whole symmetric matrix.
  have hmatrix_left_left (k l : Fin 2) :
      T.intersection (e (.inl k)) (e (.inl l)) =
        -(w : ℤ) * doubleForkCartanMatrix n (.inl k) (.inl l) +
          extra (.inl k) (.inl l) := by
    simp only [e, doubleForkEmbedding]
    fin_cases k <;> fin_cases l
    all_goals dsimp
    · rw [hchainEntry 0 0 (by omega) (by omega)]
      simp [extra, doubleForkExtra]
      ring_nf
    · rw [hleftEntry 0 (by omega)]
      simp [extra, doubleForkExtra]
    · rw [T.intersection_comm, hleftEntry 0 (by omega)]
      simp [extra, doubleForkExtra]
    · rw [hl.branch_intersection_self, hwleft]
      simp [extra, doubleForkExtra]
      ring_nf
  have hmatrix_left_middle (k : Fin 2) (l : Fin (n + 2)) :
      T.intersection (e (.inl k)) (e (.inr (.inl l))) =
        -(w : ℤ) * doubleForkCartanMatrix n (.inl k) (.inr (.inl l)) +
          extra (.inl k) (.inr (.inl l)) := by
    simp only [e, doubleForkEmbedding]
    fin_cases k
    all_goals dsimp
    · rw [hchainEntry 0 (l + 1) (by omega) (hmiddle_lt l)]
      simp only [extra, doubleForkExtra, doubleForkCartanMatrix_inl_inr_inl]
      by_cases hl0 : (l : ℕ) = 0
      · have : l = 0 := Fin.ext hl0
        subst l
        norm_num
      · simp [hl0]
    · rw [T.intersection_comm, hleftEntry (l + 1) (hmiddle_lt l)]
      simp only [extra, doubleForkExtra, doubleForkCartanMatrix_inl_inr_inl]
      by_cases hl0 : (l : ℕ) = 0
      · have : l = 0 := Fin.ext hl0
        subst l
        norm_num
      · simp [hl0]
  have hmatrix_left_right (k l : Fin 2) :
      T.intersection (e (.inl k)) (e (.inr (.inr l))) =
        -(w : ℤ) * doubleForkCartanMatrix n (.inl k) (.inr (.inr l)) +
          extra (.inl k) (.inr (.inr l)) := by
    simp only [e, doubleForkEmbedding]
    fin_cases k <;> fin_cases l
    all_goals dsimp
    · rw [hchainEntry 0 (t - 1) (by omega) (by omega)]
      simp only [doubleForkCartanMatrix_inl_inr_inr, extra, doubleForkExtra]
      simp [hzero_ne_last, hone_ne_last]
    · rw [hrightEntry 0 (by omega)]
      simp only [doubleForkCartanMatrix_inl_inr_inr, extra, doubleForkExtra]
      simp only [hzero_ne_penultimate, ↓reduceIte]
      norm_num
    · rw [T.intersection_comm, hleftEntry (t - 1) (by omega)]
      simp only [doubleForkCartanMatrix_inl_inr_inr, extra, doubleForkExtra]
      simp only [hlast_ne_one, ↓reduceIte]
      norm_num
    · norm_num [extra, doubleForkExtra]
  have hmatrix_middle_middle (k l : Fin (n + 2)) :
      T.intersection (e (.inr (.inl k))) (e (.inr (.inl l))) =
        -(w : ℤ) * doubleForkCartanMatrix n (.inr (.inl k)) (.inr (.inl l)) +
          extra (.inr (.inl k)) (.inr (.inl l)) := by
    simp only [e, doubleForkEmbedding, extra, doubleForkExtra,
      doubleForkCartanMatrix_inr_inl_inr_inl]
    rw [hchainEntry (k + 1) (l + 1) (hmiddle_lt k) (hmiddle_lt l)]
    split_ifs <;> omega
  have hmatrix_middle_right (k : Fin (n + 2)) (l : Fin 2) :
      T.intersection (e (.inr (.inl k))) (e (.inr (.inr l))) =
        -(w : ℤ) * doubleForkCartanMatrix n (.inr (.inl k)) (.inr (.inr l)) +
          extra (.inr (.inl k)) (.inr (.inr l)) := by
    simp only [e, doubleForkEmbedding]
    fin_cases l
    all_goals dsimp
    · rw [hchainEntry (k + 1) (t - 1) (hmiddle_lt k) (by omega)]
      simp only [extra, doubleForkExtra, doubleForkCartanMatrix_inr_inl_inr_inr]
      split_ifs <;> omega
    · rw [hrightEntry (k + 1) (hmiddle_lt k)]
      simp only [extra, doubleForkExtra, doubleForkCartanMatrix_inr_inl_inr_inr]
      split_ifs <;> omega
  have hmatrix_right_right (k l : Fin 2) :
      T.intersection (e (.inr (.inr k))) (e (.inr (.inr l))) =
        -(w : ℤ) * doubleForkCartanMatrix n (.inr (.inr k)) (.inr (.inr l)) +
          extra (.inr (.inr k)) (.inr (.inr l)) := by
    simp only [e, doubleForkEmbedding]
    fin_cases k <;> fin_cases l
    all_goals dsimp
    · rw [hchainEntry (t - 1) (t - 1) (by omega) (by omega)]
      simp [extra, doubleForkExtra]
      ring_nf
    · rw [hrightEntry (t - 1) (by omega)]
      simp only [hlast_ne_penultimate, ↓reduceIte]
      norm_num [extra, doubleForkExtra]
    · rw [T.intersection_comm, hrightEntry (t - 1) (by omega)]
      simp only [hlast_ne_penultimate, ↓reduceIte]
      norm_num [extra, doubleForkExtra]
    · rw [hr.branch_intersection_self, hwright]
      simp [extra, doubleForkExtra]
      ring_nf
  have hmatrix_swap (k l : DoubleForkIndex n)
      (h : T.intersection (e l) (e k) =
        -(w : ℤ) * doubleForkCartanMatrix n l k + extra l k) :
      T.intersection (e k) (e l) =
        -(w : ℤ) * doubleForkCartanMatrix n k l + extra k l := by
    calc
      T.intersection (e k) (e l) = T.intersection (e l) (e k) :=
        T.intersection_comm _ _
      _ = -(w : ℤ) * doubleForkCartanMatrix n l k + extra l k := h
      _ = -(w : ℤ) * doubleForkCartanMatrix n k l + extra k l := by
        rw [← (doubleForkCartanMatrix_isSymm n).apply, hextra_comm]
  have hmatrix (k l : DoubleForkIndex n) :
      T.intersection (e k) (e l) =
        -(w : ℤ) * doubleForkCartanMatrix n k l + extra k l := by
    rcases k with k | k | k <;> rcases l with l | l | l
    · exact hmatrix_left_left k l
    · exact hmatrix_left_middle k l
    · exact hmatrix_left_right k l
    · exact hmatrix_swap (.inr (.inl k)) (.inl l) (hmatrix_left_middle l k)
    · exact hmatrix_middle_middle k l
    · exact hmatrix_middle_right k l
    · exact hmatrix_swap (.inr (.inr k)) (.inl l) (hmatrix_left_right l k)
    · exact hmatrix_swap (.inr (.inr k)) (.inr (.inl l)) (hmatrix_middle_right l k)
    · exact hmatrix_right_right k l
  exact hmatrix i j

/-- A chain of at least four `(-2)`-indices cannot have additional leaves meeting its second and
penultimate components when the displayed components form a proper subset of the numerical type.
The leaves are necessarily distinct, but they may intersect each other; the affine-`D` marks still
give nonnegative row sums ([Stacks, Lemma 55.5.11](https://stacks.math.columbia.edu/tag/0C8H)). -/
theorem not_oppositeFork (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left)
    (ht : 3 < t) (hcard : t + 2 < Fintype.card T.Component) : False := by
  have hchainCard : t < Fintype.card T.Component := by omega
  have hrightCard : t + 1 < Fintype.card T.Component := by omega
  have hreversePenultimate : t - 1 - (t - 2) = 1 := by omega
  have hleftRight : left ≠ right := by
    intro h
    have hrightZero : T.intersection (c 1) right = 0 :=
      hr.branch_intersection_eq_zero (by omega) (by omega)
    have hleftPos : 0 < T.intersection (c 1) left := by
      simpa only [hreversePenultimate] using hl.branch_intersection_pos
    rw [h] at hleftPos
    omega
  have hleft_ne_chain : ∀ i < t, left ≠ c i := by
    intro i hi
    have hreverse : t - 1 - (t - 1 - i) = i := by omega
    simpa only [hreverse] using hl.branch_ne (t - 1 - i) (by omega)
  -- Classifying the two forks fixes one common weight, every chain edge, and the two leaf edges.
  obtain ⟨w, hw, hwright, hedge, hrightEdge⟩ := hr.exists_weight_intersection_eq hrightCard
  obtain ⟨w', hw', hwleft', -, hleftEdge'⟩ := hl.exists_weight_intersection_eq hrightCard
  have hreverseLast : t - 1 - 0 = t - 1 := by omega
  have hww : (w' : ℤ) = w := by
    have hw'last : (T.weight (c (t - 1)) : ℤ) = w' := by
      simpa only [hreverseLast] using hw' 0 (by omega)
    exact hw'last.symm.trans (hw (t - 1) (by omega))
  have hwleft : (T.weight left : ℤ) = w := hwleft'.trans hww
  have hleftEdge : T.intersection (c 1) left = w := by
    simpa only [hreversePenultimate, hww] using hleftEdge'
  have hleftZero : ∀ {i}, i < t → i ≠ 1 → T.intersection (c i) left = 0 := by
    intro i hi hi1
    have hreverse : t - 1 - (t - 1 - i) = i := by omega
    have hreverse_ne : t - 1 - i ≠ t - 2 := by omega
    simpa only [hreverse] using
      hl.branch_intersection_eq_zero (i := t - 1 - i) (by omega) hreverse_ne
  have hchainEntry (i j : ℕ) (hi : i < t) (hj : j < t) :
      T.intersection (c i) (c j) =
        if i = j then -(2 * (w : ℤ)) else if i + 1 = j ∨ j + 1 = i then w else 0 := by
    split_ifs with hij hadj
    · subst j
      rw [hr.intersection_self i hi, hw i hi]
    · rcases hadj with hadj | hadj
      · subst j
        exact hedge i hj
      · subst i
        rw [T.intersection_comm]
        exact hedge j hi
    · exact hr.intersection_eq_zero hchainCard hi hj hij (by omega) (by omega)
  have hrightEntry (i : ℕ) (hi : i < t) :
      T.intersection (c i) right = if i = t - 2 then (w : ℤ) else 0 := by
    split_ifs with hit
    · subst i
      exact hrightEdge
    · exact hr.branch_intersection_eq_zero hi hit
  have hleftEntry (i : ℕ) (hi : i < t) :
      T.intersection (c i) left = if i = 1 then (w : ℤ) else 0 := by
    split_ifs with hi1
    · subst i
      exact hleftEdge
    · exact hleftZero hi hi1
  let n := t - 4
  let e : DoubleForkIndex n → T.Component := doubleForkEmbedding t c left right
  have he : Function.Injective e :=
    doubleForkEmbedding_injective hr ht hleftRight hleft_ne_chain
  let mark : DoubleForkIndex n → ℤ
    | .inl _ => 1
    | .inr (.inl _) => 2
    | .inr (.inr _) => 1
  let extra : DoubleForkIndex n → DoubleForkIndex n → ℤ :=
    doubleForkExtra T left right n
  have hmatrix (i j : DoubleForkIndex n) :
      T.intersection (e i) (e j) =
        -(w : ℤ) * doubleForkCartanMatrix n i j + extra i j := by
    exact intersection_doubleForkEmbedding_eq hr hl ht w hwright hwleft hchainEntry
      hrightEntry hleftEntry i j
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
            ∑ j, (-(w : ℤ) * doubleForkCartanMatrix n i j + extra i j) * mark j := by
          exact sum_congr rfl fun j _ ↦ by rw [hmatrix]
        _ = -(w : ℤ) * (∑ j, doubleForkCartanMatrix n i j * mark j) +
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
      rcases i with i | i | i <;> simp [mark]) ⟨Sum.inl 0, by simp [mark]⟩) hrow

end IsSelfIntersectionMinusTwoFork

end NumericalType

end TauCeti
