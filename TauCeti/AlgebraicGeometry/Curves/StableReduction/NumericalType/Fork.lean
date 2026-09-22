/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Chain
import TauCeti.Algebra.BigOperators.Finset.Range
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
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.le_card`: a fork contains at least `t + 1`
  distinct components.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.branch_intersection_eq_zero`: the extra
  component meets no other component of the chain, without a properness assumption.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.exists_weight_intersection_eq`: the
  weights and intersections of a proper fork whose chain has length at least three are all the
  simply-laced ones.
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

/-- The chain followed by the extra branch component is injective on its first `t + 1` terms. -/
lemma injOn_snoc (hf : T.IsSelfIntersectionMinusTwoFork t c branch) :
    ∀ i < t + 1, ∀ j < t + 1,
      (if i = t then branch else c i) = (if j = t then branch else c j) → i = j := by
  intro i hi j hj hij
  by_cases hit : i = t
  · by_cases hjt : j = t
    · exact hit.trans hjt.symm
    · simp only [hit, hjt, ↓reduceIte] at hij
      exact (hf.branch_ne j (by omega) hij).elim
  · by_cases hjt : j = t
    · simp only [hit, hjt, ↓reduceIte] at hij
      exact (hf.branch_ne i (by omega) hij.symm).elim
    · simp only [hit, hjt, ↓reduceIte] at hij
      exact hf.injOn i (by omega) j (by omega) hij

/-- A fork contains at least `t + 1` distinct components. -/
lemma le_card (hf : T.IsSelfIntersectionMinusTwoFork t c branch) :
    t + 1 ≤ Fintype.card T.Component := by
  let e : Fin (t + 1) → T.Component := fun j ↦ if (j : ℕ) = t then branch else c j
  simpa using Fintype.card_le_of_injective e (by
    intro p q hpq
    apply Fin.ext
    exact hf.injOn_snoc p (by omega) q (by omega) hpq)

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
      simp only [show t - 2 ≠ t - 1 by omega,
        show t - 2 + 1 = t - 1 by omega, ↓reduceIte]
      exact hf.branch_intersection_pos
    · have hj' : j + 1 < t - 1 := by omega
      simp only [show j ≠ t - 1 by omega, ne_of_lt hj', ↓reduceIte]
      exact hf.toIsSelfIntersectionMinusTwoChain.intersection_succ_pos j hj

/-- The extra leaf of a fork whose chain has length at least three meets no chain component other
than the one indexed by `t - 2`. -/
lemma branch_intersection_eq_zero (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    {i : ℕ} (hi : i < t) (hne : i ≠ t - 2) :
    T.intersection (c i) branch = 0 := by
  have ht := hf.two_lt
  have hforkCard := hf.le_card
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
  have hforkCard := hf.le_card
  have hchainCard : t < Fintype.card T.Component := by omega
  have hprefix : (∑ j ∈ range t, T.intersection (c i) (d j) * y j) =
      ∑ j ∈ range t, T.intersection (c i) (c j) * y j :=
    Finset.sum_congr rfl fun j hj ↦ by rw [hd_lt (mem_range.mp hj)]
  have hprev : T.intersection (c (i - 1)) (c i) = w := by
    simpa only [show i - 1 + 1 = i by omega] using hedge (i - 1) (by omega) (by omega)
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
  have hforkCard := hf.le_card
  have hchainCard : t < Fintype.card T.Component := by omega
  have hw₂ := hinterior (t - 2) (by omega) (by omega)
  have ha₃₂ : T.intersection (c (t - 3)) (c (t - 2)) = w := by
    simpa only [show t - 3 + 1 = t - 2 by omega] using hedge (t - 3) (by omega) (by omega)
  have ha₂₁ : T.intersection (c (t - 2)) (c (t - 1)) = w := by
    simpa only [show t - 2 + 1 = t - 1 by omega] using hedge (t - 2) (by omega) (by omega)
  have hchainSum {i : ℕ} (hi : i < t) :
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
    rw [sum_range_succ, hd_lt (by omega), hd_t, hchainSum (by omega),
      hf.toIsSelfIntersectionMinusTwoChain.left_sum_eq hchainCard (by omega) y,
      hy0, hyInterior (i := 1) (by omega) (by omega)]
    rw [hf.branch_intersection_eq_zero (by omega) (by omega), zero_mul, add_zero]
    exact hrow0.ge
  have hnextLeftRow :
      0 ≤ ∑ j ∈ range (t + 1), T.intersection (d 1) (d j) * y j := by
    rw [sum_range_succ, hd_lt (by omega), hd_t, hchainSum (by omega),
      hf.toIsSelfIntersectionMinusTwoChain.interior_sum_eq hchainCard y
        (i := 1) (by omega) (by omega),
      hy0, hyInterior (i := 1) (by omega) (by omega),
      hyInterior (i := 2) (by omega) (by omega)]
    rw [hf.branch_intersection_eq_zero (by omega) (by omega), zero_mul, add_zero]
    exact hrow1.ge
  have hforkRow :
      0 ≤ ∑ j ∈ range (t + 1), T.intersection (d (t - 2)) (d j) * y j := by
    rw [sum_range_succ, hd_lt (by omega), hd_t, hchainSum (by omega),
      hf.toIsSelfIntersectionMinusTwoChain.interior_sum_eq hchainCard y
        (i := t - 2) (by omega) (by omega),
      show t - 2 - 1 = t - 3 by omega, show t - 2 + 1 = t - 1 by omega,
      hyInterior (i := t - 3) (by omega) (by omega),
      hyInterior (i := t - 2) (by omega) (by omega), hyLast,
      T.intersection_comm (c (t - 2)) (c (t - 3)), ha₃₂,
      hf.intersection_self (t - 2) (by omega), hw₂, ha₂₁, ha₂b, hyt]
    exact le_of_eq (by ring)
  have hlastRow :
      0 ≤ ∑ j ∈ range (t + 1), T.intersection (d (t - 1)) (d j) * y j := by
    rw [sum_range_succ, hd_lt (by omega), hd_t, hchainSum (by omega),
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
      simp [y, show t - 1 ≠ 0 by omega, show ¬t - 1 + 1 < t by omega]
    have hyt : y t = 1 := by simp [y, show t ≠ 0 by omega]
    have hinj : ∀ i < t + 1, ∀ j < t + 1, d i = d j → i = j := by
      simpa only [d] using hf.injOn_snoc
    have hrow : ∀ i < t + 1,
        0 ≤ ∑ j ∈ range (t + 1), T.intersection (d i) (d j) * y j :=
      affine_sum_nonneg hf ht α d y hd_lt hd_t hy0 hyInterior hyLast hyt
        hinterior hedge hwb hw₁ ha₂b hrow0 hrow1
    exact (T.not_forall_sum_intersection_mul_nonneg_of_pos hinj hcard
      (y := y) (fun i hi ↦ by simp only [y]; split_ifs <;> omega)
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

end IsSelfIntersectionMinusTwoFork

end NumericalType

end TauCeti
