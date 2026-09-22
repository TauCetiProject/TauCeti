/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Chain
import TauCeti.Algebra.BigOperators.Finset.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Forks of `(-2)`-indices of arbitrary length

A fork consists of a chain of components of self-intersection `-2w` together with a second leaf
at the component indexed by `t - 2`.  The raw predicate allows every chain length, so this index
uses truncated subtraction for short chains.  When the chain has at least five components and
the numerical type has components outside the fork, every component in the fork has the same
weight, the displayed intersections equal that weight, and all other intersections between the
branch and the chain vanish.  Together with the chain's no-chord theorem, this identifies the
induced intersection graph with a simply-laced fork.

This is [Stacks, Lemma 55.5.9](https://stacks.math.columbia.edu/tag/0C8A).  It is one of the
families in the classification of proper connected subgraphs of `(-2)`-indices used to bound the
multiplicities of a minimal numerical type.

## Main results

* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork`: a chain with a second leaf at its
  component indexed by `t - 2`, with no lower bound on the chain length.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.exists_weight_intersection_eq`: the
  weights and intersections of a proper fork whose chain has length at least five are all the
  simply-laced ones.
-/

public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable (T : NumericalType.{u})

/-- A chain `c 0 - ... - c (t - 1)` of components of self-intersection `-2w`, together with a
second leaf `branch` meeting `c (t - 2)`.  This structure imposes no lower bound on `t`, so the
index `t - 2` is truncated when `t < 2`; the classification theorem assumes `4 < t`. -/
structure IsSelfIntersectionMinusTwoFork (t : ℕ) (c : ℕ → T.Component)
    (branch : T.Component) : Prop extends T.IsSelfIntersectionMinusTwoChain t c where
  /-- The extra leaf is not one of the chain components. -/
  branch_ne : ∀ i < t, branch ≠ c i
  /-- The extra leaf has self-intersection `-2w`. -/
  branch_intersection_self :
    T.intersection branch branch = -(2 * (T.weight branch : ℤ))
  /-- The extra leaf meets the penultimate chain component. -/
  branch_intersection_pos : 0 < T.intersection (c (t - 2)) branch

variable {T : NumericalType.{u}} {t : ℕ} {c : ℕ → T.Component} {branch : T.Component}

namespace IsSelfIntersectionMinusTwoFork

/-- The extra leaf of a fork whose chain has length at least five meets no chain component other
than the one indexed by `t - 2`. -/
lemma branch_intersection_eq_zero (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (ht : 4 < t) {i : ℕ} (hi : i < t) (hne : i ≠ t - 2) :
    T.intersection (c i) branch = 0 := by
  let e : Fin (t + 1) → T.Component := fun j ↦ if (j : ℕ) = t then branch else c j
  have he : Function.Injective e := by
    intro p q hpq
    apply Fin.ext
    dsimp only [e] at hpq
    by_cases hpt : (p : ℕ) = t
    · by_cases hqt : (q : ℕ) = t
      · exact hpt.trans hqt.symm
      · simp only [hpt, hqt, ↓reduceIte] at hpq
        exact (hf.branch_ne q (by omega) hpq).elim
    · by_cases hqt : (q : ℕ) = t
      · simp only [hpt, hqt, ↓reduceIte] at hpq
        exact (hf.branch_ne p (by omega) hpq.symm).elim
      · simp only [hpt, hqt, ↓reduceIte] at hpq
        exact hf.injOn p (by omega) q (by omega) hpq
  have hforkCard : t + 1 ≤ Fintype.card T.Component := by
    simpa using Fintype.card_le_of_injective e he
  let d : ℕ → T.Component := fun j ↦ if j = t - 1 then branch else c j
  have hd_lt {j : ℕ} (hj : j < t - 1) : d j = c j := by simp [d, ne_of_lt hj]
  have hd_last : d (t - 1) = branch := by simp [d]
  have hd : T.IsSelfIntersectionMinusTwoChain t d := {
    injOn := by
      intro p hp q hq hpq
      by_cases hpl : p = t - 1
      · subst p
        by_contra hqne
        have hq' : q < t - 1 := by omega
        rw [hd_last, hd_lt hq'] at hpq
        exact hf.branch_ne q hq hpq
      · have hp' : p < t - 1 := by omega
        by_cases hql : q = t - 1
        · subst q
          rw [hd_lt hp', hd_last] at hpq
          exact absurd hpq (hf.branch_ne p hp).symm
        · have hq' : q < t - 1 := by omega
          rw [hd_lt hp', hd_lt hq'] at hpq
          exact hf.toIsSelfIntersectionMinusTwoChain.injOn p hp q hq hpq
    intersection_self := by
      intro j hj
      by_cases hjl : j = t - 1
      · subst j
        rw [hd_last]
        exact hf.branch_intersection_self
      · have hj' : j < t - 1 := by omega
        rw [hd_lt hj']
        exact hf.toIsSelfIntersectionMinusTwoChain.intersection_self j hj
    intersection_succ_pos := by
      intro j hj
      by_cases hlast : j + 1 = t - 1
      · have hjc : j = t - 2 := by omega
        subst j
        rw [hd_lt (by omega), hlast, hd_last]
        exact hf.branch_intersection_pos
      · have hj' : j + 1 < t - 1 := by omega
        rw [hd_lt (by omega), hd_lt hj']
        exact hf.toIsSelfIntersectionMinusTwoChain.intersection_succ_pos j hj }
  by_cases hil : i = t - 1
  · subst i
    obtain ⟨w, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzero⟩ :=
      T.exists_weight_intersection_fork_five_eq (by omega)
        (hf.intersection_self (t - 4) (by omega))
        (hf.intersection_self (t - 3) (by omega))
        (hf.intersection_self (t - 2) (by omega))
        (hf.intersection_self (t - 1) (by omega)) hf.branch_intersection_self
        (hf.ne (by omega) (by omega) (by omega))
        (hf.ne (by omega) (by omega) (by omega)) (hf.branch_ne (t - 4) (by omega)).symm
        (hf.ne (by omega) (by omega) (by omega)) (hf.branch_ne (t - 3) (by omega)).symm
        (hf.branch_ne (t - 1) (by omega)).symm
        (hf.intersection_pos (by omega) (by omega))
        (hf.intersection_pos (by omega) (by omega))
        (hf.intersection_pos (by omega) (by omega)) hf.branch_intersection_pos
    exact hzero
  · have hi' : i < t - 1 := by omega
    have h := hd.intersection_eq_zero (by omega) (p := i) (q := t - 1) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [hd_lt hi', hd_last] at h
    exact h

/-- The exceptional left-end weights allowed for a chain cannot occur after attaching the
second leaf.  The proof extends the fork weights to the positive kernel vector of the affine
fork and checks its rows at the two left endpoints, the branch point, the right endpoint, and
the remaining interior points, contradicting negative definiteness on a proper subset. -/
private lemma left_weight_eq (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : t + 1 < Fintype.card T.Component) (ht : 4 < t) {w : ℕ+}
    (hinterior : ∀ i, 0 < i → i + 1 < t → (T.weight (c i) : ℤ) = w)
    (hbranchZero : ∀ i < t, i ≠ t - 2 → T.intersection (c i) branch = 0)
    (hedge : ∀ i, 0 < i → i + 1 < t → T.intersection (c i) (c (i + 1)) = w)
    (hWleft : (T.weight (c 0) : ℤ) = w ∨ (T.weight (c 0) : ℤ) = 2 * w ∨
      2 * (T.weight (c 0) : ℤ) = w)
    (hwb : (T.weight branch : ℤ) = w) (hw₂ : (T.weight (c (t - 2)) : ℤ) = w)
    (hw₁ : (T.weight (c (t - 1)) : ℤ) = w)
    (ha₃₂ : T.intersection (c (t - 3)) (c (t - 2)) = w)
    (ha₂₁ : T.intersection (c (t - 2)) (c (t - 1)) = w)
    (ha₂b : T.intersection (c (t - 2)) branch = w) :
    (T.weight (c 0) : ℤ) = w := by
  rcases hWleft with h | hexceptional
  · exact h
  · exfalso
    -- Both exceptional weights give the same two vanishing left-end rows, with coefficient
    -- one or two at the first component respectively.
    obtain ⟨α, hαpos, hrow0, hrow1⟩ :
        ∃ α : ℤ, 0 < α ∧
          T.intersection (c 0) (c 0) * α + T.intersection (c 0) (c 1) * 2 = 0 ∧
          T.intersection (c 1) (c 0) * α + T.intersection (c 1) (c 1) * 2 +
            T.intersection (c 1) (c 2) * 2 = 0 := by
      rcases hexceptional with h | h
      · have h01 : T.intersection (c 0) (c 1) = 2 * w := by
          rw [T.intersection_eq_max_weight (by omega)
            (hf.intersection_self 0 (by omega)) (hf.intersection_self 1 (by omega))
            (hf.intersection_succ_pos 0 (by omega)), h,
            hinterior 1 (by omega) (by omega)]
          exact max_eq_left (by omega)
        refine ⟨1, one_pos, ?_, ?_⟩
        · rw [hf.intersection_self 0 (by omega), h, h01]
          ring
        · rw [T.intersection_comm (c 1) (c 0), h01,
            hf.intersection_self 1 (by omega), hinterior 1 (by omega) (by omega),
            hedge 1 (by omega) (by omega)]
          ring
      · have h01 : T.intersection (c 0) (c 1) = w := by
          rw [T.intersection_eq_max_weight (by omega)
            (hf.intersection_self 0 (by omega)) (hf.intersection_self 1 (by omega))
            (hf.intersection_succ_pos 0 (by omega)), hinterior 1 (by omega) (by omega)]
          exact max_eq_right (by omega)
        refine ⟨2, two_pos, ?_, ?_⟩
        · rw [hf.intersection_self 0 (by omega), h01]
          linarith
        · rw [T.intersection_comm (c 1) (c 0), h01,
            hf.intersection_self 1 (by omega), hinterior 1 (by omega) (by omega),
            hedge 1 (by omega) (by omega)]
          ring
    let d : ℕ → T.Component := fun i ↦ if i = t then branch else c i
    let y : ℕ → ℤ := fun i ↦ if i = 0 then α else if i + 1 < t then 2 else 1
    have hd_lt {i : ℕ} (hi : i < t) : d i = c i := by simp [d, ne_of_lt hi]
    have hd_t : d t = branch := by simp [d]
    have hy0 : y 0 = α := by simp [y]
    have hyInterior {i : ℕ} (hi : 0 < i) (hit : i + 1 < t) : y i = 2 := by
      simp [y, ne_of_gt hi, hit]
    have htPredNeZero : t - 1 ≠ 0 := by omega
    have htPredSuccNotLt : ¬t - 1 + 1 < t := by omega
    have htNeZero : t ≠ 0 := by omega
    have hyLast : y (t - 1) = 1 := by simp [y, htPredNeZero, htPredSuccNotLt]
    have hyt : y t = 1 := by simp [y, htNeZero]
    have hinj : ∀ i < t + 1, ∀ j < t + 1, d i = d j → i = j := by
      intro i hi j hj hij
      by_cases hit : i = t
      · subst i
        by_cases hjt : j = t
        · exact hjt.symm
        · have hj' : j < t := by omega
          rw [hd_t, hd_lt hj'] at hij
          exact (hf.branch_ne j hj' hij).elim
      · have hi' : i < t := by omega
        by_cases hjt : j = t
        · subst j
          rw [hd_lt hi', hd_t] at hij
          exact (hf.branch_ne i hi' hij.symm).elim
        · have hj' : j < t := by omega
          rw [hd_lt hi', hd_lt hj'] at hij
          exact hf.injOn i hi' j hj' hij
    have hchainCard : t < Fintype.card T.Component := by omega
    have hrow : ∀ i < t + 1,
        0 ≤ ∑ j ∈ range (t + 1), T.intersection (d i) (d j) * y j := by
      intro i hi
      rw [sum_range_succ]
      by_cases hit : i = t
      · subst i
        rw [hd_t, hyt]
        have hsum : (∑ j ∈ range t, T.intersection branch (d j) * y j) =
            T.intersection branch (d (t - 2)) * y (t - 2) := by
          refine Finset.sum_eq_single (s := range t)
            (f := fun j ↦ T.intersection branch (d j) * y j) (t - 2)
            (fun j hj hji ↦ ?_) (fun hj ↦ ?_)
          · rw [hd_lt (mem_range.mp hj), T.intersection_comm,
              hbranchZero j (mem_range.mp hj) (by omega), zero_mul]
          · exact absurd (mem_range.mpr (by omega)) hj
        rw [hsum, hd_lt (by omega), T.intersection_comm branch, ha₂b,
          hyInterior (i := t - 2) (by omega) (by omega), hf.branch_intersection_self, hwb]
        ring_nf
        positivity
      · have hit' : i < t := by omega
        rw [hd_lt hit', hd_t]
        have hchainZero {p q : ℕ} (hp : p < t) (hq : q < t) (hpq : p ≠ q)
            (hpq₁ : p + 1 ≠ q) (hqp₁ : q + 1 ≠ p) : T.intersection (c p) (c q) = 0 :=
          hf.intersection_eq_zero hchainCard hp hq hpq hpq₁ hqp₁
        have hsumd : (∑ j ∈ range t, T.intersection (c i) (d j) * y j) =
            ∑ j ∈ range t, T.intersection (c i) (c j) * y j :=
          Finset.sum_congr rfl fun j hj ↦ by rw [hd_lt (mem_range.mp hj)]
        rw [hsumd]
        -- The first two rows are the certificate above.  The remaining rows split into the
        -- branch point, the right endpoint, and ordinary interior rows.
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [sum_range_eq_of_eq_zero_off_pair (a := 0) (b := 1) (by omega)
              (by omega) (by omega) (fun j hj hj0 hj1 ↦ by
                rw [hchainZero (by omega) hj (by omega) (by omega) (by omega), zero_mul])
              rfl, hy0, hyInterior (i := 1) (by omega) (by omega)]
          rw [hbranchZero 0 (by omega) (by omega), zero_mul, add_zero]
          exact hrow0.ge
        · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hi0) with rfl | hi1
          · rw [sum_range_eq_of_eq_zero_off_triple (a := 0) (b := 1) (d := 2)
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                (fun j hj hj0 hj1 hj2 ↦ by
                  rw [hchainZero (by omega) hj (by omega) (by omega) (by omega), zero_mul])
                rfl, hy0, hyInterior (i := 1) (by omega) (by omega),
              hyInterior (i := 2) (by omega) (by omega)]
            rw [hbranchZero 1 (by omega) (by omega), zero_mul, add_zero]
            exact hrow1.ge
          · by_cases hic : i = t - 2
            · subst i
              rw [sum_range_eq_of_eq_zero_off_triple (a := t - 3) (b := t - 2)
                  (d := t - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
                  (by omega) (fun j hj hja hjb hjd ↦ by
                    rw [hchainZero (by omega) hj (by omega) (by omega) (by omega), zero_mul])
                  rfl, hyInterior (i := t - 3) (by omega) (by omega),
                  hyInterior (i := t - 2) (by omega) (by omega), hyLast,
                  T.intersection_comm (c (t - 2)) (c (t - 3)),
                  ha₃₂, hf.intersection_self (t - 2) (by omega),
                  hw₂, ha₂₁, ha₂b, hyt]
              ring_nf
              positivity
            · by_cases hilast : i = t - 1
              · subst i
                rw [sum_range_eq_of_eq_zero_off_pair (a := t - 2) (b := t - 1)
                    (by omega) (by omega) (by omega) (fun j hj hja hjb ↦ by
                      rw [T.intersection_comm,
                        hchainZero hj (by omega) (by omega) (by omega) (by omega), zero_mul])
                    rfl, hyInterior (i := t - 2) (by omega) (by omega), hyLast,
                    T.intersection_comm, ha₂₁, hf.intersection_self (t - 1) (by omega), hw₁]
                rw [hbranchZero (t - 1) (by omega) (by omega), zero_mul, add_zero]
                ring_nf
                positivity
              · have hprev : T.intersection (c (i - 1)) (c i) = w := by
                  have hprev' := hedge (i - 1) (by omega) (by omega)
                  have hidx : i - 1 + 1 = i := by omega
                  rwa [hidx] at hprev'
                rw [sum_range_eq_of_eq_zero_off_triple (a := i - 1) (b := i)
                  (d := i + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
                  (by omega) (fun j hj hja hjb hjd ↦ by
                    rcases lt_or_gt_of_ne hjb with hji | hji
                    · rw [T.intersection_comm,
                        hchainZero hj hit' (by omega) (by omega) (by omega), zero_mul]
                    · rw [hchainZero hit' hj (by omega) (by omega) (by omega), zero_mul])
                  rfl, hyInterior (i := i - 1) (by omega) (by omega),
                    hyInterior (i := i) hi0 (by omega),
                    hyInterior (i := i + 1) (by omega) (by omega),
                    T.intersection_comm, hprev,
                    hf.intersection_self i hit', hinterior i hi0 (by omega),
                    hedge i hi0 (by omega)]
                rw [hbranchZero i hit' hic, zero_mul, add_zero]
                ring_nf
                positivity
    exact (T.not_forall_sum_intersection_mul_nonneg_of_pos hinj hcard
      (y := y) (fun i hi ↦ by simp only [y]; split_ifs <;> omega)
      ⟨0, by omega, by rw [hy0]; exact hαpos⟩) hrow

/-- A proper fork whose chain has length at least five (and hence has at least six fork
components) is simply laced: all its component weights agree, each displayed intersection is
that common weight, and the extra leaf has no other intersection with the chain.  Together with
`TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.intersection_eq_zero`, this is the full
classification of [Stacks, Lemma 55.5.9](https://stacks.math.columbia.edu/tag/0C8A). -/
theorem exists_weight_intersection_eq (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : t + 1 < Fintype.card T.Component) (ht : 4 < t) :
    ∃ w : ℕ+, (∀ i < t, (T.weight (c i) : ℤ) = w) ∧ (T.weight branch : ℤ) = w ∧
      (∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) = w) ∧
      T.intersection (c (t - 2)) branch = w ∧
      ∀ i < t, i ≠ t - 2 → T.intersection (c i) branch = 0 := by
  have hchainCard : t < Fintype.card T.Component := by omega
  obtain ⟨w, hw₄, -, hw₂, hw₁, hwb, -, ha₃₂, ha₂₁, ha₂b,
      -, -, -, -, -, -⟩ := T.exists_weight_intersection_fork_five_eq (by omega)
    (hf.intersection_self (t - 4) (by omega))
    (hf.intersection_self (t - 3) (by omega))
    (hf.intersection_self (t - 2) (by omega))
    (hf.intersection_self (t - 1) (by omega)) hf.branch_intersection_self
    (hf.ne (by omega) (by omega) (by omega)) (hf.ne (by omega) (by omega) (by omega))
    (hf.branch_ne (t - 4) (by omega)).symm (hf.ne (by omega) (by omega) (by omega))
    (hf.branch_ne (t - 3) (by omega)).symm (hf.branch_ne (t - 1) (by omega)).symm
    (hf.intersection_pos (by omega) (by omega)) (hf.intersection_pos (by omega) (by omega))
    (hf.intersection_pos (by omega) (by omega)) hf.branch_intersection_pos
  obtain ⟨W, -, hWinterior, hWleft, -, -⟩ :=
    hf.toIsSelfIntersectionMinusTwoChain.exists_weight_eq_except_one_end hchainCard ht
  have hWw : W = (w : ℤ) := by
    rw [← hWinterior (t - 4) (by omega) (by omega), hw₄]
  subst W
  have hinterior : ∀ i, 0 < i → i + 1 < t → (T.weight (c i) : ℤ) = w := hWinterior
  have hbranchZero : ∀ i < t, i ≠ t - 2 → T.intersection (c i) branch = 0 :=
    fun i hi hne ↦ hf.branch_intersection_eq_zero ht hi hne
  have hedge : ∀ i, 0 < i → i + 1 < t → T.intersection (c i) (c (i + 1)) = w := by
    intro i hi hit
    have hmax := T.intersection_eq_max_weight (by omega)
      (hf.intersection_self i (by omega)) (hf.intersection_self (i + 1) hit)
      (hf.intersection_succ_pos i hit)
    have hnext : (T.weight (c (i + 1)) : ℤ) = w := by
      by_cases hlast : i + 1 = t - 1
      · simpa [hlast] using hw₁
      · exact hinterior (i + 1) (by omega) (by omega)
    rw [hinterior i hi (by omega), hnext] at hmax
    simpa only [max_self] using hmax
  have hleft := left_weight_eq hf hcard ht hinterior hbranchZero hedge hWleft hwb hw₂ hw₁
    ha₃₂ ha₂₁ ha₂b
  refine ⟨w, ?_, hwb, ?_, ha₂b, hbranchZero⟩
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact hleft
    by_cases hlast : i = t - 1
    · simpa [hlast] using hw₁
    · exact hinterior i hi0 (by omega)
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [T.intersection_eq_max_weight (by omega)
        (hf.intersection_self 0 (by omega)) (hf.intersection_self 1 (by omega))
        (hf.intersection_succ_pos 0 hi), hleft, hinterior 1 (by omega) (by omega)]
      simp only [max_self]
    exact hedge i hi0 hi

end IsSelfIntersectionMinusTwoFork

end NumericalType

end TauCeti
