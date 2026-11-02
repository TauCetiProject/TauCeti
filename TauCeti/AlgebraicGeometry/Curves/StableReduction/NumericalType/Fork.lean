/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Chain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Forks of `(-2)`-indices of arbitrary length

A fork consists of a chain of at least three components of self-intersection `-2w`, together with
a distinct extra component of self-intersection `-2w` meeting the component indexed by `t - 2`.
The extra component meets no other component of the chain.  When the numerical type has components
outside the fork, every component in the fork has the same weight and the displayed intersections
equal that weight.  Together with the chain's no-chord theorem, this identifies the induced
intersection graph with a simply-laced fork.

This is [Stacks, Lemma 55.5.9](https://stacks.math.columbia.edu/tag/0C8D).  It is one of the
families in the classification of proper connected subgraphs of `(-2)`-indices used to bound the
multiplicities of a minimal numerical type.  The chain-length-three and chain-length-four cases
subsumed here are respectively [Stacks, Lemma 55.5.4](https://stacks.math.columbia.edu/tag/0C80)
and [Stacks, Lemma 55.5.7](https://stacks.math.columbia.edu/tag/0C87).

## Main results

* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork`: a chain of length at least three with a
  distinct extra component of self-intersection `-2w` meeting the component indexed by `t - 2`.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.branch_intersection_eq_zero`: the extra
  component meets no other component of the chain, without a properness assumption.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.exists_weight_intersection_eq`: the
  weights and intersections of a proper fork whose chain has length at least three are all the
  simply-laced ones.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.fiber_relation` and its row versions
  `left_fiber_relation`, `interior_fiber_relation`, `fork_fiber_relation`,
  `right_fiber_relation` and `branch_fiber_relation`: the fibre relations of a fork exhausting a
  numerical type.
-/

public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable (T : NumericalType.{u})

/-- A chain `c 0 - ... - c (t - 1)` of at least three components of self-intersection `-2w`,
together with a distinct extra component `branch`, also of self-intersection `-2w`, meeting
`c (t - 2)`.  The no-extra-intersection theorem shows that `branch` is a leaf. -/
structure IsSelfIntersectionMinusTwoFork (t : ℕ) (c : ℕ → T.Component)
    (branch : T.Component) : Prop extends T.IsSelfIntersectionMinusTwoChain t c where
  /-- The chain contains at least three components. -/
  two_lt : 2 < t
  /-- The extra component is not one of the chain components. -/
  branch_ne : ∀ i < t, branch ≠ c i
  /-- The extra component has self-intersection `-2w`. -/
  branch_intersection_self :
    T.intersection branch branch = -(2 * (T.weight branch : ℤ))
  /-- The extra component meets the penultimate chain component. -/
  branch_intersection_pos : 0 < T.intersection (c (t - 2)) branch

variable {T : NumericalType.{u}} {t : ℕ} {c : ℕ → T.Component} {branch : T.Component}

namespace IsSelfIntersectionMinusTwoFork

private lemma chain_branch_last (hf : T.IsSelfIntersectionMinusTwoFork t c branch) :
    T.IsSelfIntersectionMinusTwoChain t fun j ↦ if j = t - 1 then branch else c j where
  injOn p hp q hq hpq := by
    by_cases hpl : p = t - 1
    · by_cases hql : q = t - 1
      · exact hpl.trans hql.symm
      · simp only [hpl, hql, ↓reduceIte] at hpq
        exact (hf.branch_ne q hq hpq).elim
    · by_cases hql : q = t - 1
      · simp only [hpl, hql, ↓reduceIte] at hpq
        exact absurd hpq (hf.branch_ne p hp).symm
      · simp only [hpl, hql, ↓reduceIte] at hpq
        exact hf.toIsSelfIntersectionMinusTwoChain.injOn p hp q hq hpq
  intersection_self j hj := by
    by_cases hjl : j = t - 1
    · simpa only [hjl, ↓reduceIte] using hf.branch_intersection_self
    · have hj' : j < t - 1 := by omega
      simp only [ne_of_lt hj', ↓reduceIte]
      exact hf.toIsSelfIntersectionMinusTwoChain.intersection_self j hj
  intersection_succ_pos j hj := by
    by_cases hlast : j + 1 = t - 1
    · have hjc : j = t - 2 := by omega
      subst j
      have hpenultimate_ne_last : t - 2 ≠ t - 1 := by omega
      have hpenultimate_succ : t - 2 + 1 = t - 1 := by omega
      simp only [hpenultimate_ne_last, hpenultimate_succ, ↓reduceIte]
      exact hf.branch_intersection_pos
    · have hj' : j + 1 < t - 1 := by omega
      have hj_ne_last : j ≠ t - 1 := by omega
      simp only [hj_ne_last, ne_of_lt hj', ↓reduceIte]
      exact hf.toIsSelfIntersectionMinusTwoChain.intersection_succ_pos j hj

/-- The extra leaf of a fork whose chain has length at least three meets no chain component other
than the one indexed by `t - 2`. -/
lemma branch_intersection_eq_zero (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    {i : ℕ} (hi : i < t) (hne : i ≠ t - 2) :
    T.intersection (c i) branch = 0 := by
  have ht := hf.two_lt
  have hforkCard := hf.toIsSelfIntersectionMinusTwoChain.le_card_snoc hf.branch_ne
  let d : ℕ → T.Component := fun j ↦ if j = t - 1 then branch else c j
  have hd_lt {j : ℕ} (hj : j < t - 1) : d j = c j := by simp [d, ne_of_lt hj]
  have hd_last : d (t - 1) = branch := by simp [d]
  have hd : T.IsSelfIntersectionMinusTwoChain t d := by
    simpa only [d] using hf.chain_branch_last
  by_cases hil : i = t - 1
  · subst i
    exact T.intersection_eq_zero_of_intersection_pos_of_intersection_pos (by omega)
      (hf.intersection_self (t - 1) (by omega))
      (hf.intersection_self (t - 2) (by omega)) hf.branch_intersection_self
      (hf.branch_ne (t - 1) (by omega)).symm
      (T.intersection_comm (c (t - 2)) (c (t - 1)) ▸
        hf.intersection_pos (by omega) (by omega)) hf.branch_intersection_pos
  · have hi' : i < t - 1 := by omega
    have h := hd.intersection_eq_zero (by omega) (p := i) (q := t - 1) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [hd_lt hi', hd_last] at h
    exact h

private lemma affine_interior_sum_eq_zero (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    {w : ℕ+} (d : ℕ → T.Component) (y : ℕ → ℤ)
    (hd_lt : ∀ {j}, j < t → d j = c j) (hd_t : d t = branch)
    (hyInterior : ∀ {j}, 0 < j → j + 1 < t → y j = 2)
    (hinterior : ∀ i, 0 < i → i + 1 < t → (T.weight (c i) : ℤ) = w)
    (hedge : ∀ i, 0 < i → i + 1 < t → T.intersection (c i) (c (i + 1)) = w)
    {i : ℕ} (hi : 1 < i) (hit : i < t) (hic : i ≠ t - 2) (hilast : i ≠ t - 1) :
    ∑ j ∈ range (t + 1), T.intersection (d i) (d j) * y j = 0 := by
  have hforkCard := hf.toIsSelfIntersectionMinusTwoChain.le_card_snoc hf.branch_ne
  have hchainCard : t < Fintype.card T.Component := by omega
  have hprefix : (∑ j ∈ range t, T.intersection (c i) (d j) * y j) =
      ∑ j ∈ range t, T.intersection (c i) (c j) * y j :=
    Finset.sum_congr rfl fun j hj ↦ by rw [hd_lt (mem_range.mp hj)]
  have hprev : T.intersection (c (i - 1)) (c i) = w := by
    have hprev_succ : i - 1 + 1 = i := by omega
    simpa only [hprev_succ] using hedge (i - 1) (by omega) (by omega)
  rw [sum_range_succ, hd_lt hit, hd_t, hprefix,
    hf.toIsSelfIntersectionMinusTwoChain.interior_sum_eq hchainCard y (by omega) (by omega),
    hyInterior (j := i - 1) (by omega) (by omega), hyInterior (j := i) (by omega) (by omega),
    hyInterior (j := i + 1) (by omega) (by omega), T.intersection_comm, hprev,
    hf.intersection_self i hit, hinterior i (by omega) (by omega), hedge i (by omega) (by omega),
    hf.branch_intersection_eq_zero hit hic, zero_mul, add_zero]
  ring

private lemma affine_sum_nonneg (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (ht : 4 < t) {w : ℕ+} (α : ℤ) (d : ℕ → T.Component) (y : ℕ → ℤ)
    (hd_lt : ∀ {i}, i < t → d i = c i) (hd_t : d t = branch) (hy0 : y 0 = α)
    (hyInterior : ∀ {i}, 0 < i → i + 1 < t → y i = 2) (hyLast : y (t - 1) = 1)
    (hyt : y t = 1)
    (hinterior : ∀ i, 0 < i → i + 1 < t → (T.weight (c i) : ℤ) = w)
    (hedge : ∀ i, 0 < i → i + 1 < t → T.intersection (c i) (c (i + 1)) = w)
    (hwb : (T.weight branch : ℤ) = w) (hw₁ : (T.weight (c (t - 1)) : ℤ) = w)
    (ha₂b : T.intersection (c (t - 2)) branch = w)
    (hrow0 : T.intersection (c 0) (c 0) * α + T.intersection (c 0) (c 1) * 2 = 0)
    (hrow1 : T.intersection (c 1) (c 0) * α + T.intersection (c 1) (c 1) * 2 +
      T.intersection (c 1) (c 2) * 2 = 0) :
    ∀ i < t + 1, 0 ≤ ∑ j ∈ range (t + 1), T.intersection (d i) (d j) * y j := by
  have hforkCard := hf.toIsSelfIntersectionMinusTwoChain.le_card_snoc hf.branch_ne
  have hchainCard : t < Fintype.card T.Component := by omega
  have hw₂ := hinterior (t - 2) (by omega) (by omega)
  have ha₃₂ : T.intersection (c (t - 3)) (c (t - 2)) = w := by
    have hthird_last_succ : t - 3 + 1 = t - 2 := by omega
    simpa only [hthird_last_succ] using hedge (t - 3) (by omega) (by omega)
  have ha₂₁ : T.intersection (c (t - 2)) (c (t - 1)) = w := by
    have hpenultimate_succ : t - 2 + 1 = t - 1 := by omega
    simpa only [hpenultimate_succ] using hedge (t - 2) (by omega) (by omega)
  have hchainSum {i : ℕ} :
      (∑ j ∈ range t, T.intersection (c i) (d j) * y j) =
        ∑ j ∈ range t, T.intersection (c i) (c j) * y j :=
    Finset.sum_congr rfl fun j hj ↦ by rw [hd_lt (mem_range.mp hj)]
  -- The affine certificate has six kinds of rows.  Each helper first restricts the row to
  -- its nonzero neighbours and then verifies the resulting weighted sum.
  have hbranchRow :
      0 ≤ ∑ j ∈ range (t + 1), T.intersection (d t) (d j) * y j := by
    rw [sum_range_succ, hd_t, hyt]
    have hsum : (∑ j ∈ range t, T.intersection branch (d j) * y j) =
        T.intersection branch (d (t - 2)) * y (t - 2) := by
      refine Finset.sum_eq_single (s := range t)
        (f := fun j ↦ T.intersection branch (d j) * y j) (t - 2)
        (fun j hj hji ↦ ?_) (fun hj ↦ ?_)
      · rw [hd_lt (mem_range.mp hj), T.intersection_comm,
          hf.branch_intersection_eq_zero (mem_range.mp hj) (by omega), zero_mul]
      · exact absurd (mem_range.mpr (by omega)) hj
    rw [hsum, hd_lt (by omega), T.intersection_comm branch, ha₂b,
      hyInterior (i := t - 2) (by omega) (by omega), hf.branch_intersection_self, hwb]
    exact le_of_eq (by ring)
  have hleftRow :
      0 ≤ ∑ j ∈ range (t + 1), T.intersection (d 0) (d j) * y j := by
    rw [sum_range_succ, hd_lt (by omega), hd_t, hchainSum,
      hf.toIsSelfIntersectionMinusTwoChain.left_sum_eq hchainCard (by omega) y,
      hy0, hyInterior (i := 1) (by omega) (by omega)]
    rw [hf.branch_intersection_eq_zero (by omega) (by omega), zero_mul, add_zero]
    exact hrow0.ge
  have hnextLeftRow :
      0 ≤ ∑ j ∈ range (t + 1), T.intersection (d 1) (d j) * y j := by
    rw [sum_range_succ, hd_lt (by omega), hd_t, hchainSum,
      hf.toIsSelfIntersectionMinusTwoChain.interior_sum_eq hchainCard y
        (i := 1) (by omega) (by omega),
      hy0, hyInterior (i := 1) (by omega) (by omega),
      hyInterior (i := 2) (by omega) (by omega)]
    rw [hf.branch_intersection_eq_zero (by omega) (by omega), zero_mul, add_zero]
    exact hrow1.ge
  have hforkRow :
      0 ≤ ∑ j ∈ range (t + 1), T.intersection (d (t - 2)) (d j) * y j := by
    have hthird_last : t - 2 - 1 = t - 3 := by omega
    have hpenultimate_succ : t - 2 + 1 = t - 1 := by omega
    rw [sum_range_succ, hd_lt (by omega), hd_t, hchainSum,
      hf.toIsSelfIntersectionMinusTwoChain.interior_sum_eq hchainCard y
        (i := t - 2) (by omega) (by omega),
      hthird_last, hpenultimate_succ,
      hyInterior (i := t - 3) (by omega) (by omega),
      hyInterior (i := t - 2) (by omega) (by omega), hyLast,
      T.intersection_comm (c (t - 2)) (c (t - 3)), ha₃₂,
      hf.intersection_self (t - 2) (by omega), hw₂, ha₂₁, ha₂b, hyt]
    exact le_of_eq (by ring)
  have hlastRow :
      0 ≤ ∑ j ∈ range (t + 1), T.intersection (d (t - 1)) (d j) * y j := by
    rw [sum_range_succ, hd_lt (by omega), hd_t, hchainSum,
      hf.toIsSelfIntersectionMinusTwoChain.right_sum_eq hchainCard (by omega) y,
      hyInterior (i := t - 2) (by omega) (by omega), hyLast,
      T.intersection_comm, ha₂₁, hf.intersection_self (t - 1) (by omega), hw₁]
    rw [hf.branch_intersection_eq_zero (by omega) (by omega), zero_mul, add_zero]
    exact le_of_eq (by ring)
  have hinteriorRow (i : ℕ) (hi1 : 1 < i) (hit : i < t)
      (hic : i ≠ t - 2) (hilast : i ≠ t - 1) :
      0 ≤ ∑ j ∈ range (t + 1), T.intersection (d i) (d j) * y j := by
    exact Eq.ge (affine_interior_sum_eq_zero hf d y hd_lt hd_t hyInterior
      hinterior hedge hi1 hit hic hilast)
  have hrow : ∀ i < t + 1,
      0 ≤ ∑ j ∈ range (t + 1), T.intersection (d i) (d j) * y j := by
    intro i hi
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hit
    · exact hbranchRow
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact hleftRow
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hi0) with rfl | hi1
    · exact hnextLeftRow
    by_cases hic : i = t - 2
    · simpa only [hic] using hforkRow
    by_cases hilast : i = t - 1
    · simpa only [hilast] using hlastRow
    exact hinteriorRow i hi1 hit hic hilast
  exact hrow

/-- The exceptional left-end weights allowed for a chain cannot occur after attaching the
second leaf. -/
private lemma left_weight_eq (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : t + 1 < Fintype.card T.Component) (ht : 4 < t) {w : ℕ+}
    (hinterior : ∀ i, 0 < i → i + 1 < t → (T.weight (c i) : ℤ) = w)
    (hedge : ∀ i, 0 < i → i + 1 < t → T.intersection (c i) (c (i + 1)) = w)
    (hWleft : (T.weight (c 0) : ℤ) = w ∨ (T.weight (c 0) : ℤ) = 2 * w ∨
      2 * (T.weight (c 0) : ℤ) = w)
    (hwb : (T.weight branch : ℤ) = w) (hw₁ : (T.weight (c (t - 1)) : ℤ) = w)
    (ha₂b : T.intersection (c (t - 2)) branch = w) :
    (T.weight (c 0) : ℤ) = w := by
  -- Extend the fork weights to a positive kernel vector of the affine fork.  Its rows at
  -- the two left endpoints, branch point, right endpoint, and remaining interior points
  -- contradict negative definiteness on a proper subset.
  rcases hWleft with h | hexceptional
  · exact h
  · exfalso
    -- Both exceptional weights give the same two vanishing left-end rows, with coefficient
    -- one or two at the first component respectively.
    obtain ⟨α, hαpos, h01α, hrow0⟩ :
        ∃ α : ℤ, 0 < α ∧
          T.intersection (c 0) (c 1) * α = 2 * w ∧
          T.intersection (c 0) (c 0) * α + T.intersection (c 0) (c 1) * 2 = 0 := by
      rcases hexceptional with h | h
      · have h01 : T.intersection (c 0) (c 1) = 2 * w := by
          rw [T.intersection_eq_max_weight (by omega)
            (hf.intersection_self 0 (by omega)) (hf.intersection_self 1 (by omega))
            (hf.intersection_succ_pos 0 (by omega)), h,
            hinterior 1 (by omega) (by omega)]
          exact max_eq_left (by omega)
        refine ⟨1, one_pos, by rw [h01]; ring, ?_⟩
        rw [hf.intersection_self 0 (by omega), h, h01]
        ring
      · have h01 : T.intersection (c 0) (c 1) = w := by
          rw [T.intersection_eq_max_weight (by omega)
            (hf.intersection_self 0 (by omega)) (hf.intersection_self 1 (by omega))
            (hf.intersection_succ_pos 0 (by omega)), hinterior 1 (by omega) (by omega)]
          exact max_eq_right (by omega)
        refine ⟨2, two_pos, by rw [h01]; ring, ?_⟩
        rw [hf.intersection_self 0 (by omega), h01]
        linarith
    have hrow1 : T.intersection (c 1) (c 0) * α + T.intersection (c 1) (c 1) * 2 +
        T.intersection (c 1) (c 2) * 2 = 0 := by
      rw [T.intersection_comm (c 1) (c 0), hf.intersection_self 1 (by omega),
        hinterior 1 (by omega) (by omega), hedge 1 (by omega) (by omega)]
      linarith
    let d : ℕ → T.Component := fun i ↦ if i = t then branch else c i
    let y : ℕ → ℤ := fun i ↦ if i = 0 then α else if i + 1 < t then 2 else 1
    have hd_lt {i : ℕ} (hi : i < t) : d i = c i := by simp [d, ne_of_lt hi]
    have hd_t : d t = branch := by simp [d]
    have hy0 : y 0 = α := by simp [y]
    have hyInterior {i : ℕ} (hi : 0 < i) (hit : i + 1 < t) : y i = 2 := by
      simp [y, ne_of_gt hi, hit]
    have hyLast : y (t - 1) = 1 := by
      have hlast_ne_zero : t - 1 ≠ 0 := by omega
      have hlast_not_interior : ¬ t - 1 + 1 < t := by omega
      simp [y, hlast_ne_zero, hlast_not_interior]
    have hyt : y t = 1 := by
      have ht_ne_zero : t ≠ 0 := by omega
      simp [y, ht_ne_zero]
    have hinj : ∀ i < t + 1, ∀ j < t + 1, d i = d j → i = j := by
      simpa only [d] using hf.toIsSelfIntersectionMinusTwoChain.injOn_snoc hf.branch_ne
    have hrow : ∀ i < t + 1,
        0 ≤ ∑ j ∈ range (t + 1), T.intersection (d i) (d j) * y j :=
      affine_sum_nonneg hf ht α d y hd_lt hd_t hy0 hyInterior hyLast hyt
        hinterior hedge hwb hw₁ ha₂b hrow0 hrow1
    exact (T.not_forall_sum_intersection_mul_nonneg_of_pos hinj hcard
      (y := y) (fun i _ ↦ by simp only [y]; split_ifs <;> omega)
      ⟨0, by omega, by rw [hy0]; exact hαpos⟩) hrow

private theorem exists_weight_intersection_eq_of_four_lt
    (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : t + 1 < Fintype.card T.Component) (ht : 4 < t) :
    ∃ w : ℕ+, (∀ i < t, (T.weight (c i) : ℤ) = w) ∧ (T.weight branch : ℤ) = w ∧
      (∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) = w) ∧
      T.intersection (c (t - 2)) branch = w := by
  have hchainCard : t < Fintype.card T.Component := by omega
  obtain ⟨w, hw₄, -, -, hw₁, hwb, -, -, -, ha₂b,
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
  have hleft := left_weight_eq hf hcard ht hinterior hedge hWleft hwb hw₁ ha₂b
  refine ⟨w, ?_, hwb, ?_, ha₂b⟩
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

/-- The three-component-chain case of the fork classification. -/
private theorem exists_weight_intersection_eq_three
    (hf : T.IsSelfIntersectionMinusTwoFork 3 c branch)
    (hcard : 3 + 1 < Fintype.card T.Component) :
    ∃ w : ℕ+, (∀ i < 3, (T.weight (c i) : ℤ) = w) ∧ (T.weight branch : ℤ) = w ∧
      (∀ i, i + 1 < 3 → T.intersection (c i) (c (i + 1)) = w) ∧
      T.intersection (c (3 - 2)) branch = w := by
  obtain ⟨w, hw₁, hw₀, hw₂, hwb, ha₁₀, ha₁₂, ha₁b, -, -, -⟩ :=
    T.exists_weight_intersection_star_four_eq (by omega)
      (hf.intersection_self 1 (by omega)) (hf.intersection_self 0 (by omega))
      (hf.intersection_self 2 (by omega)) hf.branch_intersection_self
      (hf.ne (by omega) (by omega) (by omega)) (hf.branch_ne 0 (by omega)).symm
      (hf.branch_ne 2 (by omega)).symm
      (T.intersection_comm (c 0) (c 1) ▸ hf.intersection_succ_pos 0 (by omega))
      (hf.intersection_succ_pos 1 (by omega)) hf.branch_intersection_pos
  refine ⟨w, ?_, hwb, ?_, ha₁b⟩
  · intro i hi
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi_cases with rfl | rfl | rfl
    · exact hw₀
    · exact hw₁
    · exact hw₂
  · intro i hi
    have hi_cases : i = 0 ∨ i = 1 := by omega
    rcases hi_cases with rfl | rfl
    · exact T.intersection_comm (c 1) (c 0) ▸ ha₁₀
    · exact ha₁₂

/-- The four-component-chain case of the fork classification. -/
private theorem exists_weight_intersection_eq_four
    (hf : T.IsSelfIntersectionMinusTwoFork 4 c branch)
    (hcard : 4 + 1 < Fintype.card T.Component) :
    ∃ w : ℕ+, (∀ i < 4, (T.weight (c i) : ℤ) = w) ∧ (T.weight branch : ℤ) = w ∧
      (∀ i, i + 1 < 4 → T.intersection (c i) (c (i + 1)) = w) ∧
      T.intersection (c (4 - 2)) branch = w := by
  obtain ⟨w, hw₀, hw₁, hw₂, hw₃, hwb, ha₀₁, ha₁₂, ha₂₃, ha₂b,
      -, -, -, -, -, -⟩ := T.exists_weight_intersection_fork_five_eq (by omega)
    (hf.intersection_self 0 (by omega)) (hf.intersection_self 1 (by omega))
    (hf.intersection_self 2 (by omega)) (hf.intersection_self 3 (by omega))
    hf.branch_intersection_self (hf.ne (by omega) (by omega) (by omega))
    (hf.ne (by omega) (by omega) (by omega)) (hf.branch_ne 0 (by omega)).symm
    (hf.ne (by omega) (by omega) (by omega)) (hf.branch_ne 1 (by omega)).symm
    (hf.branch_ne 3 (by omega)).symm (hf.intersection_succ_pos 0 (by omega))
    (hf.intersection_succ_pos 1 (by omega)) (hf.intersection_succ_pos 2 (by omega))
    hf.branch_intersection_pos
  refine ⟨w, ?_, hwb, ?_, ha₂b⟩
  · intro i hi
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi_cases with rfl | rfl | rfl | rfl
    · exact hw₀
    · exact hw₁
    · exact hw₂
    · exact hw₃
  · intro i hi
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi_cases with rfl | rfl | rfl
    · exact ha₀₁
    · exact ha₁₂
    · exact ha₂₃

/-- A proper fork whose chain has length at least three is simply laced: all its component
weights agree and each displayed intersection is that common weight.  Together with
`TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.branch_intersection_eq_zero` and
`TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.intersection_eq_zero`, this is the full
classification of [Stacks, Lemma 55.5.9](https://stacks.math.columbia.edu/tag/0C8D). -/
theorem exists_weight_intersection_eq (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : t + 1 < Fintype.card T.Component) :
    ∃ w : ℕ+, (∀ i < t, (T.weight (c i) : ℤ) = w) ∧ (T.weight branch : ℤ) = w ∧
      (∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) = w) ∧
      T.intersection (c (t - 2)) branch = w := by
  have ht := hf.two_lt
  rcases lt_or_ge t 5 with ht5 | ht5
  · have ht_cases : t = 3 ∨ t = 4 := by omega
    rcases ht_cases with rfl | rfl
    · exact exists_weight_intersection_eq_three hf hcard
    · exact exists_weight_intersection_eq_four hf hcard
  · exact exists_weight_intersection_eq_of_four_lt hf hcard (by omega)

/-- Removing the unbranched endpoint of a fork whose chain has length at least four gives a fork
on the remaining components. -/
lemma tail (hf : T.IsSelfIntersectionMinusTwoFork t c branch) (ht : 3 < t) :
    T.IsSelfIntersectionMinusTwoFork (t - 1) (fun i ↦ c (i + 1)) branch where
  toIsSelfIntersectionMinusTwoChain :=
    by simpa [Nat.add_comm] using
      hf.toIsSelfIntersectionMinusTwoChain.shift (r := 1) (s := t - 1) (by omega)
  two_lt := by omega
  branch_ne i hi := hf.branch_ne (i + 1) (by omega)
  branch_intersection_self := hf.branch_intersection_self
  branch_intersection_pos := by
    have ht₂ : t - 1 - 2 + 1 = t - 2 := by omega
    simpa only [ht₂] using hf.branch_intersection_pos

/-- The chain components of a fork together with its extra leaf exhaust a numerical type with
`t + 1` components. -/
lemma insert_image_range_eq_univ (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) :
    insert branch ((range t).image c) = (univ : Finset T.Component) := by
  apply eq_univ_of_card
  rw [card_insert_of_notMem (by
    intro h
    obtain ⟨i, hi, hci⟩ := mem_image.mp h
    exact hf.branch_ne i (mem_range.mp hi) hci.symm),
    card_image_of_injOn (by
      intro i hi j hj hij
      exact hf.injOn i (mem_range.mp hi) j (mem_range.mp hj) hij), card_range]
  exact hcard.symm

/-- For a fork exhausting a numerical type, the fibre relation at any component splits into the
term of the extra leaf and a sum over the chain. -/
lemma fiber_relation (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) (i : T.Component) :
    (T.multiplicity branch : ℤ) * T.intersection i branch +
      ∑ j ∈ range t, (T.multiplicity (c j) : ℤ) * T.intersection i (c j) = 0 := by
  classical
  have h := T.fiber_relation i
  rw [← hf.insert_image_range_eq_univ hcard, sum_insert, sum_image] at h
  · exact h
  · intro j hj k hk hjk
    exact hf.injOn j (mem_range.mp hj) k (mem_range.mp hk) hjk
  · intro hbranch
    obtain ⟨j, hj, hbj⟩ := mem_image.mp hbranch
    exact hf.branch_ne j (mem_range.mp hj) hbj.symm

/-- The chain part of the fibre relation of an exhaustive fork, with the intersection numbers on
the left of each term as in the chain row lemmas. -/
private lemma sum_range_intersection_mul_multiplicity
    (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) (i : T.Component) :
    ∑ j ∈ range t, T.intersection i (c j) * (T.multiplicity (c j) : ℤ) =
      -((T.multiplicity branch : ℤ) * T.intersection i branch) := by
  simp_rw [mul_comm (T.intersection i _)]
  linarith [hf.fiber_relation hcard i]

/-- For a fork exhausting a numerical type, the fibre relation at the unbranched endpoint has
only its diagonal and adjacent terms. -/
lemma left_fiber_relation (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) :
    (T.multiplicity (c 0) : ℤ) * T.intersection (c 0) (c 0) +
      T.multiplicity (c 1) * T.intersection (c 0) (c 1) = 0 := by
  have ht := hf.two_lt
  have h := hf.sum_range_intersection_mul_multiplicity hcard (c 0)
  rw [hf.left_sum_eq (by omega) (by omega),
    hf.branch_intersection_eq_zero (by omega) (by omega)] at h
  linarith

/-- For a fork exhausting a numerical type, the fibre relation at an interior chain component
other than the branch point has only its diagonal and two adjacent terms. -/
lemma interior_fiber_relation (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) {i : ℕ} (hi : 0 < i) (hit : i + 1 < t)
    (hifork : i ≠ t - 2) :
    (T.multiplicity (c (i - 1)) : ℤ) * T.intersection (c i) (c (i - 1)) +
        T.multiplicity (c i) * T.intersection (c i) (c i) +
      T.multiplicity (c (i + 1)) * T.intersection (c i) (c (i + 1)) = 0 := by
  have h := hf.sum_range_intersection_mul_multiplicity hcard (c i)
  rw [hf.interior_sum_eq (by omega) _ hi hit,
    hf.branch_intersection_eq_zero (by omega) hifork] at h
  linarith

/-- For a fork exhausting a numerical type, the fibre relation at the branch point `c (t - 2)`
has its diagonal term, its two chain neighbours and the extra leaf. -/
lemma fork_fiber_relation (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) :
    (T.multiplicity (c (t - 3)) : ℤ) * T.intersection (c (t - 2)) (c (t - 3)) +
          T.multiplicity (c (t - 2)) * T.intersection (c (t - 2)) (c (t - 2)) +
        T.multiplicity (c (t - 1)) * T.intersection (c (t - 2)) (c (t - 1)) +
      T.multiplicity branch * T.intersection (c (t - 2)) branch = 0 := by
  have ht := hf.two_lt
  have h := hf.sum_range_intersection_mul_multiplicity hcard (c (t - 2))
  have ht₃ : t - 2 - 1 = t - 3 := by omega
  have ht₁ : t - 2 + 1 = t - 1 := by omega
  rw [hf.interior_sum_eq (by omega) _ (i := t - 2) (by omega) (by omega), ht₃, ht₁] at h
  linarith

/-- For a fork exhausting a numerical type, the fibre relation at the terminal chain component
has only its diagonal and adjacent terms. -/
lemma right_fiber_relation (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) :
    (T.multiplicity (c (t - 2)) : ℤ) * T.intersection (c (t - 1)) (c (t - 2)) +
      T.multiplicity (c (t - 1)) * T.intersection (c (t - 1)) (c (t - 1)) = 0 := by
  have ht := hf.two_lt
  have h := hf.sum_range_intersection_mul_multiplicity hcard (c (t - 1))
  rw [hf.right_sum_eq (by omega) (by omega),
    hf.branch_intersection_eq_zero (by omega) (by omega)] at h
  linarith

/-- For a fork exhausting a numerical type, the fibre relation at the extra leaf has only its
diagonal term and the branch point. -/
lemma branch_fiber_relation (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) :
    (T.multiplicity (c (t - 2)) : ℤ) * T.intersection branch (c (t - 2)) +
      T.multiplicity branch * T.intersection branch branch = 0 := by
  have ht := hf.two_lt
  have h := hf.sum_range_intersection_mul_multiplicity hcard branch
  rw [sum_eq_single (t - 2) (fun j hj hjne ↦ by
      rw [T.intersection_comm, hf.branch_intersection_eq_zero (mem_range.mp hj) hjne, zero_mul])
    (fun h ↦ absurd (mem_range.mpr (by omega)) h)] at h
  linarith

end IsSelfIntersectionMinusTwoFork

/-- Every component of a numerical type exhausted by a fork `(c, b)` of chain length `t` is either
`b` or `c i` for some `i < t`. -/
lemma IsSelfIntersectionMinusTwoFork.eq_or_exists_lt_eq_of_card_eq {t : ℕ} {c : ℕ → T.Component}
    {b : T.Component} (hf : T.IsSelfIntersectionMinusTwoFork t c b)
    (hcard : Fintype.card T.Component = t + 1) (v : T.Component) :
    v = b ∨ ∃ i < t, c i = v := by
  classical
  have hu := hf.insert_image_range_eq_univ hcard
  simpa [← hu] using mem_univ v

/-- Enumerate an exhaustive fork by its chain indices, followed by its extra leaf. -/
noncomputable def IsSelfIntersectionMinusTwoFork.equivFinOfCardEq
    (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) : Fin (t + 1) ≃ T.Component :=
  Equiv.ofBijective (fun i ↦ if (i : ℕ) = t then branch else c i)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun i j hij ↦ Fin.ext (hf.injOn_snoc hf.branch_ne i (by omega) j (by omega) hij),
        by simpa using hcard.symm⟩)

/-- Evaluation of the enumeration of an exhaustive fork at a chain index or its extra leaf. -/
@[simp]
lemma IsSelfIntersectionMinusTwoFork.equivFinOfCardEq_apply
    (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) (i : Fin (t + 1)) :
    hf.equivFinOfCardEq hcard i = if (i : ℕ) = t then branch else c i := by
  rw [equivFinOfCardEq, Equiv.ofBijective_apply]

end NumericalType

end TauCeti
