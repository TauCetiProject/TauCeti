/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Chain
import TauCeti.Algebra.BigOperators.Finset.Range
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Long paths of minimal numerical types of genus one

This file classifies the numerical data on a numerical type whose components form a path of
length at least six and all have self-intersection `-2w`. Up to reversing the path, there are
three possibilities. The interior weights are constant, and the endpoint weights are respectively
half and double, both half, or both double the interior weight. The fibre relations then determine
the multiplicities.

These are the three arbitrary-length path families in the classification of minimal numerical
types of genus one. They extend the last three five-component path shapes.

## References

* [Stacks Project, Lemma 55.6.2, cases (26)--(28), Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T).
* The weight calculation uses
  `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.exists_weight_eq_except_one_end`,
  which formalizes [Stacks Project, Lemma 55.5.8, Tag 0C89](https://stacks.math.columbia.edu/tag/0C89).
-/

public section

namespace TauCeti.NumericalType

open Finset

universe u

variable {T : NumericalType.{u}}

/-- The three path shapes with at least six components among the minimal numerical types of genus
one. Positions below `n` list the components consecutively along the path. -/
def IsGenusOneLongPathShape (T : NumericalType) (n : ℕ) (c : ℕ → T.Component) : Prop :=
  ∃ w m : ℤ, 0 < w ∧ 0 < m ∧
    (((∀ i < n, (T.weight (c i) : ℤ) =
          if i = 0 then w else if i + 1 = n then 4 * w else 2 * w) ∧
        (∀ i < n, (T.multiplicity (c i) : ℤ) =
          if i + 1 = n then m else 2 * m) ∧
        (∀ i, i + 1 < n → T.intersection (c i) (c (i + 1)) =
          if i + 2 = n then 4 * w else 2 * w)) ∨
      ((∀ i < n, (T.weight (c i) : ℤ) =
          if i = 0 ∨ i + 1 = n then w else 2 * w) ∧
        (∀ i < n, (T.multiplicity (c i) : ℤ) = m) ∧
        (∀ i, i + 1 < n → T.intersection (c i) (c (i + 1)) = 2 * w)) ∨
      ((∀ i < n, (T.weight (c i) : ℤ) =
          if i = 0 ∨ i + 1 = n then 2 * w else w) ∧
        (∀ i < n, (T.multiplicity (c i) : ℤ) =
          if i = 0 ∨ i + 1 = n then m else 2 * m) ∧
        (∀ i, i + 1 < n → T.intersection (c i) (c (i + 1)) =
          if i = 0 ∨ i + 2 = n then 2 * w else w)))

/-- Unfold `IsGenusOneLongPathShape` into the three weight, multiplicity and intersection
patterns of the arbitrary-length path cases in the genus-one classification. -/
theorem isGenusOneLongPathShape_iff {n : ℕ} {c : ℕ → T.Component} :
    T.IsGenusOneLongPathShape n c ↔
      ∃ w m : ℤ, 0 < w ∧ 0 < m ∧
        (((∀ i < n, (T.weight (c i) : ℤ) =
              if i = 0 then w else if i + 1 = n then 4 * w else 2 * w) ∧
            (∀ i < n, (T.multiplicity (c i) : ℤ) =
              if i + 1 = n then m else 2 * m) ∧
            (∀ i, i + 1 < n → T.intersection (c i) (c (i + 1)) =
              if i + 2 = n then 4 * w else 2 * w)) ∨
          ((∀ i < n, (T.weight (c i) : ℤ) =
              if i = 0 ∨ i + 1 = n then w else 2 * w) ∧
            (∀ i < n, (T.multiplicity (c i) : ℤ) = m) ∧
            (∀ i, i + 1 < n → T.intersection (c i) (c (i + 1)) = 2 * w)) ∨
          ((∀ i < n, (T.weight (c i) : ℤ) =
              if i = 0 ∨ i + 1 = n then 2 * w else w) ∧
            (∀ i < n, (T.multiplicity (c i) : ℤ) =
              if i = 0 ∨ i + 1 = n then m else 2 * m) ∧
            (∀ i, i + 1 < n → T.intersection (c i) (c (i + 1)) =
              if i = 0 ∨ i + 2 = n then 2 * w else w))) :=
  Iff.rfl

private lemma fiber_relation_range {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c)
    (hcard : Fintype.card T.Component = n) (i : ℕ) :
    ∑ j ∈ range n, (T.multiplicity (c j) : ℤ) * T.intersection (c i) (c j) = 0 := by
  classical
  have hu : (range n).image c = (univ : Finset T.Component) := by
    apply eq_univ_of_card
    simp [hc.card_image_range, hcard]
  have h := T.fiber_relation (c i)
  rw [← hu, sum_image] at h
  · exact h
  · intro a ha b hb hab
    exact hc.injOn a (mem_range.mp ha) b (mem_range.mp hb) hab

private lemma fiber_relation_left {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c)
    (hcard : Fintype.card T.Component = n) (hn : 2 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0) :
    (T.multiplicity (c 0) : ℤ) * T.intersection (c 0) (c 0) +
      T.multiplicity (c 1) * T.intersection (c 0) (c 1) = 0 := by
  have h := fiber_relation_range hc hcard 0
  rw [sum_range_eq_of_eq_zero_off_pair (a := 0) (b := 1) (by omega) (by omega) (by omega)
    (fun j hj hj0 hj1 ↦ by rw [hzero 0 (by omega) j hj hj0.symm (by omega) (by omega), mul_zero])
    rfl] at h
  exact h

private lemma fiber_relation_interior {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c)
    (hcard : Fintype.card T.Component = n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0) {i : ℕ} (hi : 0 < i) (hin : i + 1 < n) :
    (T.multiplicity (c (i - 1)) : ℤ) * T.intersection (c i) (c (i - 1)) +
        T.multiplicity (c i) * T.intersection (c i) (c i) +
      T.multiplicity (c (i + 1)) * T.intersection (c i) (c (i + 1)) = 0 := by
  have h := fiber_relation_range hc hcard i
  rw [sum_range_eq_of_eq_zero_off_triple (a := i - 1) (b := i) (d := i + 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun j hj hprev hself hnext ↦ by
      rw [hzero i (by omega) j hj hself.symm (by omega) (by omega), mul_zero]) rfl] at h
  exact h

private lemma fiber_relation_right {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c)
    (hcard : Fintype.card T.Component = n) (hn : 2 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0) :
    (T.multiplicity (c (n - 2)) : ℤ) * T.intersection (c (n - 1)) (c (n - 2)) +
      T.multiplicity (c (n - 1)) * T.intersection (c (n - 1)) (c (n - 1)) = 0 := by
  have h := fiber_relation_range hc hcard (n - 1)
  rw [sum_range_eq_of_eq_zero_off_pair (a := n - 2) (b := n - 1)
    (by omega) (by omega) (by omega)
    (fun j hj hprev hself ↦ by
      rw [hzero (n - 1) (by omega) j hj hself.symm (by omega) (by omega), mul_zero]) rfl] at h
  exact h

private lemma interior_weight_eq {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n) :
    ∃ W : ℤ, 0 < W ∧
      (∀ i, 0 < i → i + 1 < n → (T.weight (c i) : ℤ) = W) ∧
      ((T.weight (c 0) : ℤ) = W ∨ (T.weight (c 0) : ℤ) = 2 * W ∨
        2 * (T.weight (c 0) : ℤ) = W) ∧
      ((T.weight (c (n - 1)) : ℤ) = W ∨ (T.weight (c (n - 1)) : ℤ) = 2 * W ∨
        2 * (T.weight (c (n - 1)) : ℤ) = W) := by
  obtain ⟨W, hW, hpint, hp0, -, -⟩ :=
    (hc.mono (show n - 1 ≤ n by omega)).exists_weight_eq_except_one_end (by omega) (by omega)
  obtain ⟨W', -, hsint, -, hslast, -⟩ :=
    (hc.shift (r := 1) (s := n - 1) (by omega)).exists_weight_eq_except_one_end
      (by omega) (by omega)
  have hWW : W = W' := by
    have hp := hpint 2 (by omega) (by omega)
    have hs := hsint 1 (by omega) (by omega)
    simpa using hp.symm.trans hs
  refine ⟨W, hW, ?_, hp0, ?_⟩
  · intro i hi hin
    by_cases h : i + 1 < n - 1
    · exact hpint i hi h
    · have hs := hsint (i - 1) (by omega) (by omega)
      have hiindex : 1 + (i - 1) = i := by omega
      rw [hiindex] at hs
      calc
        (T.weight (c i) : ℤ) = W' := hs
        _ = W := hWW.symm
  · have hindex : 1 + (n - 1 - 1) = n - 1 := by omega
    rcases hslast with h | h | h
    · have hh : (T.weight (c (n - 1)) : ℤ) = W' := by simpa only [hindex] using h
      exact .inl (hh.trans hWW.symm)
    · have hh : (T.weight (c (n - 1)) : ℤ) = 2 * W' := by simpa only [hindex] using h
      exact .inr (.inl (hh.trans (congrArg (2 * ·) hWW.symm)))
    · have hh : 2 * (T.weight (c (n - 1)) : ℤ) = W' := by simpa only [hindex] using h
      exact .inr (.inr (hh.trans hWW.symm))

private lemma edge_eq_max_weight {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n) {i : ℕ}
    (hi : i + 1 < n) :
    T.intersection (c i) (c (i + 1)) =
      max (T.weight (c i) : ℤ) (T.weight (c (i + 1)) : ℤ) :=
  T.intersection_eq_max_weight (by rw [hcard]; omega) (hc.intersection_self i (by omega))
    (hc.intersection_self (i + 1) hi) (hc.intersection_succ_pos i hi)

private lemma multiplicity_eq_of_left_half {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0)
    {W : ℤ} (hW : 0 < W)
    (hint : ∀ i, 0 < i → i + 1 < n → (T.weight (c i) : ℤ) = W)
    (hleft : 2 * (T.weight (c 0) : ℤ) = W) :
    ∀ i < n - 1, (T.multiplicity (c i) : ℤ) = T.multiplicity (c 0) := by
  have hedge (i : ℕ) (hi : i + 1 < n - 1) : T.intersection (c i) (c (i + 1)) = W := by
    rw [edge_eq_max_weight hc hcard hn (by omega)]
    have hnext := hint (i + 1) (by omega) (by omega)
    rw [hnext, max_eq_right]
    by_cases hi0 : i = 0
    · subst i; omega
    · rw [hint i (by omega) (by omega)]
  have hone : (T.multiplicity (c 1) : ℤ) = T.multiplicity (c 0) := by
    have h := fiber_relation_left hc hcard (by omega) hzero
    rw [hc.intersection_self 0 (by omega), hedge 0 (by omega)] at h
    apply mul_left_cancel₀ hW.ne'
    linear_combination h + (T.multiplicity (c 0) : ℤ) * hleft
  intro i
  induction i using Nat.twoStepInduction with
  | zero => intro; rfl
  | one => intro; exact hone
  | more i hi hi₁ =>
      intro hin
      have h := fiber_relation_interior hc hcard hzero (i := i + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel, Nat.add_assoc] at h
      rw [T.intersection_comm (c (i + 1)) (c i), hedge i (by omega),
        hc.intersection_self (i + 1) (by omega), hint (i + 1) (by omega) (by omega),
        hedge (i + 1) (by omega), hi (by omega), hi₁ (by omega)] at h
      apply mul_left_cancel₀ hW.ne'
      linear_combination h

private lemma multiplicity_eq_two_mul_of_left_double {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0)
    {W : ℤ} (hW : 0 < W)
    (hint : ∀ i, 0 < i → i + 1 < n → (T.weight (c i) : ℤ) = W)
    (hleft : (T.weight (c 0) : ℤ) = 2 * W) :
    ∀ i < n - 1, 0 < i →
      (T.multiplicity (c i) : ℤ) = 2 * T.multiplicity (c 0) := by
  have hedge0 : T.intersection (c 0) (c 1) = 2 * W := by
    rw [edge_eq_max_weight hc hcard hn (by omega), hleft, hint 1 (by omega) (by omega),
      max_eq_left (by omega)]
  have hedge (i : ℕ) (hi : 0 < i) (hin : i + 1 < n - 1) :
      T.intersection (c i) (c (i + 1)) = W := by
    rw [edge_eq_max_weight hc hcard hn (by omega), hint i hi (by omega),
      hint (i + 1) (by omega) (by omega), max_self]
  have hone : (T.multiplicity (c 1) : ℤ) = 2 * T.multiplicity (c 0) := by
    have h := fiber_relation_left hc hcard (by omega) hzero
    rw [hc.intersection_self 0 (by omega), hleft, hedge0] at h
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hW.ne')
    linear_combination h
  intro i
  induction i using Nat.twoStepInduction with
  | zero => omega
  | one => intro _ _; exact hone
  | more i hi hi₁ =>
      intro hin _
      have h := fiber_relation_interior hc hcard hzero (i := i + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel, Nat.add_assoc] at h
      by_cases hi0 : i = 0
      · subst i
        norm_num at h
        rw [T.intersection_comm (c 1) (c 0), hedge0,
          hc.intersection_self 1 (by omega), hint 1 (by omega) (by omega),
          hedge 1 (by omega) (by omega), hone] at h
        apply mul_left_cancel₀ hW.ne'
        linear_combination h
      · rw [T.intersection_comm (c (i + 1)) (c i), hedge i (by omega) (by omega),
          hc.intersection_self (i + 1) (by omega), hint (i + 1) (by omega) (by omega),
          hedge (i + 1) (by omega) (by omega), hi (by omega) (by omega),
          hi₁ (by omega) (by omega)] at h
        apply mul_left_cancel₀ hW.ne'
        linear_combination h

private lemma multiplicity_eq_succ_mul_of_left_equal {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0)
    {W : ℤ} (hW : 0 < W)
    (hint : ∀ i, 0 < i → i + 1 < n → (T.weight (c i) : ℤ) = W)
    (hleft : (T.weight (c 0) : ℤ) = W) :
    ∀ i < n - 1,
      (T.multiplicity (c i) : ℤ) = (i + 1 : ℕ) * T.multiplicity (c 0) := by
  have hedge (i : ℕ) (hi : i + 1 < n - 1) : T.intersection (c i) (c (i + 1)) = W := by
    rw [edge_eq_max_weight hc hcard hn (by omega), hint (i + 1) (by omega) (by omega)]
    by_cases hi0 : i = 0
    · rw [hi0, hleft, max_self]
    · rw [hint i (by omega) (by omega), max_self]
  have hone : (T.multiplicity (c 1) : ℤ) = 2 * T.multiplicity (c 0) := by
    have h := fiber_relation_left hc hcard (by omega) hzero
    rw [hc.intersection_self 0 (by omega), hleft, hedge 0 (by omega)] at h
    apply mul_left_cancel₀ hW.ne'
    linear_combination h
  intro i
  induction i using Nat.twoStepInduction with
  | zero => simp
  | one => intro; simpa using hone
  | more i hi hi₁ =>
      intro hin
      have h := fiber_relation_interior hc hcard hzero (i := i + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel, Nat.add_assoc] at h
      rw [T.intersection_comm (c (i + 1)) (c i), hedge i (by omega),
        hc.intersection_self (i + 1) (by omega), hint (i + 1) (by omega) (by omega),
        hedge (i + 1) (by omega), hi (by omega), hi₁ (by omega)] at h
      rw [show i + (1 + 1) = i + 2 by omega] at h
      apply mul_left_cancel₀ hW.ne'
      push_cast at h ⊢
      linear_combination h

private lemma false_of_left_equal {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0)
    {W : ℤ} (hW : 0 < W)
    (hint : ∀ i, 0 < i → i + 1 < n → (T.weight (c i) : ℤ) = W)
    (hleft : (T.weight (c 0) : ℤ) = W)
    (hright : (T.weight (c (n - 1)) : ℤ) = W ∨
      (T.weight (c (n - 1)) : ℤ) = 2 * W ∨
      2 * (T.weight (c (n - 1)) : ℤ) = W) : False := by
  have hmul := multiplicity_eq_succ_mul_of_left_equal hc hcard hn hzero hW hint hleft
  have hprev := hmul (n - 2) (by omega)
  have hbefore := hmul (n - 3) (by omega)
  have hprevIndex : ((n - 2 : ℕ) : ℤ) + 1 = (n : ℤ) - 1 := by omega
  have hbeforeIndex : ((n - 3 : ℕ) : ℤ) + 1 = (n : ℤ) - 2 := by omega
  have hm0 : (0 : ℤ) < T.multiplicity (c 0) := by simp
  have hR := fiber_relation_right hc hcard (by omega) hzero
  have hP := fiber_relation_interior hc hcard hzero (i := n - 2) (by omega) (by omega)
  rw [show n - 2 - 1 = n - 3 by omega, show n - 2 + 1 = n - 1 by omega] at hP
  have hedgeBefore : T.intersection (c (n - 3)) (c (n - 2)) = W := by
    have h := edge_eq_max_weight hc hcard hn (i := n - 3) (by omega)
    rw [show n - 3 + 1 = n - 2 by omega] at h
    rw [hint (n - 3) (by omega) (by omega), hint (n - 2) (by omega) (by omega),
      max_self] at h
    exact h
  rw [T.intersection_comm (c (n - 2)) (c (n - 3)), hedgeBefore,
    hc.intersection_self (n - 2) (by omega), hint (n - 2) (by omega) (by omega)] at hP
  rcases hright with hright | hright | hright
  · have hedgeLast : T.intersection (c (n - 2)) (c (n - 1)) = W := by
      have h := edge_eq_max_weight hc hcard hn (i := n - 2) (by omega)
      rw [show n - 2 + 1 = n - 1 by omega] at h
      rw [hint (n - 2) (by omega) (by omega), hright, max_self] at h
      exact h
    rw [T.intersection_comm (c (n - 1)) (c (n - 2)), hedgeLast,
      hc.intersection_self (n - 1) (by omega), hright] at hR
    rw [hedgeLast] at hP
    have eR : (T.multiplicity (c (n - 2)) : ℤ) =
        2 * T.multiplicity (c (n - 1)) := by
      apply mul_left_cancel₀ hW.ne'
      linear_combination hR
    have eP : (T.multiplicity (c (n - 3)) : ℤ) + T.multiplicity (c (n - 1)) =
        2 * T.multiplicity (c (n - 2)) := by
      apply mul_left_cancel₀ hW.ne'
      linear_combination hP
    push_cast at hprev hbefore
    rw [hprevIndex] at hprev
    rw [hbeforeIndex] at hbefore
    have hmlast : (0 : ℤ) < T.multiplicity (c (n - 1)) := by simp
    nlinarith
  · have hedgeLast : T.intersection (c (n - 2)) (c (n - 1)) = 2 * W := by
      have h := edge_eq_max_weight hc hcard hn (i := n - 2) (by omega)
      rw [show n - 2 + 1 = n - 1 by omega] at h
      rw [hint (n - 2) (by omega) (by omega), hright, max_eq_right (by omega)] at h
      exact h
    rw [T.intersection_comm (c (n - 1)) (c (n - 2)), hedgeLast,
      hc.intersection_self (n - 1) (by omega), hright] at hR
    rw [hedgeLast] at hP
    have eR : (T.multiplicity (c (n - 2)) : ℤ) =
        2 * T.multiplicity (c (n - 1)) := by
      apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hW.ne')
      linear_combination hR
    rw [eR] at hP
    have hbeforeLast : (T.multiplicity (c (n - 3)) : ℤ) =
        2 * T.multiplicity (c (n - 1)) := by
      apply mul_left_cancel₀ hW.ne'
      linear_combination hP
    push_cast at hprev hbefore
    rw [hprevIndex] at hprev
    rw [hbeforeIndex] at hbefore
    nlinarith
  · have hedgeLast : T.intersection (c (n - 2)) (c (n - 1)) = W := by
      have h := edge_eq_max_weight hc hcard hn (i := n - 2) (by omega)
      rw [show n - 2 + 1 = n - 1 by omega] at h
      rw [hint (n - 2) (by omega) (by omega), max_eq_left (by omega)] at h
      exact h
    rw [T.intersection_comm (c (n - 1)) (c (n - 2)), hedgeLast,
      hc.intersection_self (n - 1) (by omega)] at hR
    rw [hedgeLast] at hP
    have eR : (T.multiplicity (c (n - 2)) : ℤ) = T.multiplicity (c (n - 1)) := by
      apply mul_left_cancel₀ hW.ne'
      linear_combination hR + (T.multiplicity (c (n - 1)) : ℤ) * hright
    rw [eR] at hP
    have hbeforeLast : (T.multiplicity (c (n - 3)) : ℤ) =
        T.multiplicity (c (n - 1)) := by
      apply mul_left_cancel₀ hW.ne'
      linear_combination hP
    push_cast at hprev hbefore
    rw [hprevIndex] at hprev
    rw [hbeforeIndex] at hbefore
    nlinarith

private lemma right_multiplicity_eq_of_right_half {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0)
    {W : ℤ} (hW : 0 < W)
    (hint : ∀ i, 0 < i → i + 1 < n → (T.weight (c i) : ℤ) = W)
    (hright : 2 * (T.weight (c (n - 1)) : ℤ) = W) :
    (T.multiplicity (c (n - 2)) : ℤ) = T.multiplicity (c (n - 1)) := by
  have hedge : T.intersection (c (n - 2)) (c (n - 1)) = W := by
    have h := edge_eq_max_weight hc hcard hn (i := n - 2) (by omega)
    rw [show n - 2 + 1 = n - 1 by omega] at h
    rw [hint (n - 2) (by omega) (by omega), max_eq_left (by omega)] at h
    exact h
  have h := fiber_relation_right hc hcard (by omega) hzero
  rw [T.intersection_comm (c (n - 1)) (c (n - 2)), hedge,
    hc.intersection_self (n - 1) (by omega)] at h
  apply mul_left_cancel₀ hW.ne'
  linear_combination h + (T.multiplicity (c (n - 1)) : ℤ) * hright

private lemma right_multiplicity_eq_of_right_double {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0)
    {W : ℤ} (hW : 0 < W)
    (hint : ∀ i, 0 < i → i + 1 < n → (T.weight (c i) : ℤ) = W)
    (hright : (T.weight (c (n - 1)) : ℤ) = 2 * W) :
    (T.multiplicity (c (n - 2)) : ℤ) = 2 * T.multiplicity (c (n - 1)) := by
  have hedge : T.intersection (c (n - 2)) (c (n - 1)) = 2 * W := by
    have h := edge_eq_max_weight hc hcard hn (i := n - 2) (by omega)
    rw [show n - 2 + 1 = n - 1 by omega] at h
    rw [hint (n - 2) (by omega) (by omega), hright, max_eq_right (by omega)] at h
    exact h
  have h := fiber_relation_right hc hcard (by omega) hzero
  rw [T.intersection_comm (c (n - 1)) (c (n - 2)), hedge,
    hc.intersection_self (n - 1) (by omega), hright] at h
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hW.ne')
  linear_combination h

private lemma nonconsecutive_zero_reverse {n : ℕ} {c : ℕ → T.Component}
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0) :
    ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c (n - 1 - i)) (c (n - 1 - j)) = 0 := by
  intro i hi j hj hij hnext hprev
  apply hzero (n - 1 - i) (by omega) (n - 1 - j) (by omega) <;> omega

private lemma shape_of_left_half_right_double {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0)
    {W : ℤ} (hW : 0 < W)
    (hint : ∀ i, 0 < i → i + 1 < n → (T.weight (c i) : ℤ) = W)
    (hleft : 2 * (T.weight (c 0) : ℤ) = W)
    (hright : (T.weight (c (n - 1)) : ℤ) = 2 * W) :
    T.IsGenusOneLongPathShape n c := by
  have hmul := multiplicity_eq_of_left_half hc hcard hn hzero hW hint hleft
  have hrightMul := right_multiplicity_eq_of_right_double hc hcard hn hzero hW hint hright
  have hm0 : (T.multiplicity (c 0) : ℤ) = 2 * T.multiplicity (c (n - 1)) := by
    rw [← hrightMul, hmul (n - 2) (by omega)]
  refine ⟨T.weight (c 0), T.multiplicity (c (n - 1)), by simp, by simp, .inl ⟨?_, ?_, ?_⟩⟩
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp
    by_cases hilast : i + 1 = n
    · simp only [hi0, hilast, ↓reduceIte]
      rw [show i = n - 1 by omega, hright]
      nlinarith
    · simp only [hi0, hilast, ↓reduceIte]
      rw [hint i (by omega) (by omega)]
      nlinarith
  · intro i hi
    by_cases hilast : i + 1 = n
    · simp only [hilast, ↓reduceIte]
      rw [show i = n - 1 by omega]
    · simp only [hilast, ↓reduceIte]
      rw [hmul i (by omega), hm0]
  · intro i hi
    by_cases hilast : i + 2 = n
    · simp only [hilast, ↓reduceIte]
      have h := edge_eq_max_weight hc hcard hn (i := i) hi
      rw [show i + 1 = n - 1 by omega, hint i (by omega) (by omega), hright,
        max_eq_right (by omega)] at h
      rw [show i + 1 = n - 1 by omega]
      nlinarith
    · simp only [hilast, ↓reduceIte]
      have h := edge_eq_max_weight hc hcard hn (i := i) hi
      rw [hint (i + 1) (by omega) (by omega)] at h
      by_cases hi0 : i = 0
      · subst i
        simp only [Nat.zero_add] at h ⊢
        rw [max_eq_right (by nlinarith)] at h
        nlinarith
      · rw [hint i (by omega) (by omega), max_self] at h
        nlinarith

private lemma shape_of_both_half {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0)
    {W : ℤ} (hW : 0 < W)
    (hint : ∀ i, 0 < i → i + 1 < n → (T.weight (c i) : ℤ) = W)
    (hleft : 2 * (T.weight (c 0) : ℤ) = W)
    (hright : 2 * (T.weight (c (n - 1)) : ℤ) = W) :
    T.IsGenusOneLongPathShape n c := by
  have hmul := multiplicity_eq_of_left_half hc hcard hn hzero hW hint hleft
  have hrightMul := right_multiplicity_eq_of_right_half hc hcard hn hzero hW hint hright
  have hlast : (T.multiplicity (c (n - 1)) : ℤ) = T.multiplicity (c 0) := by
    rw [← hrightMul, hmul (n - 2) (by omega)]
  refine ⟨T.weight (c 0), T.multiplicity (c 0), by simp, by simp, .inr (.inl ⟨?_, ?_, ?_⟩)⟩
  · intro i hi
    by_cases hend : i = 0 ∨ i + 1 = n
    · simp only [hend, ↓reduceIte]
      rcases hend with rfl | hend
      · rfl
      · rw [show i = n - 1 by omega]
        nlinarith
    · simp only [hend, ↓reduceIte]
      rw [hint i (by omega) (by omega)]
      nlinarith
  · intro i hi
    by_cases hilast : i + 1 = n
    · rw [show i = n - 1 by omega, hlast]
    · exact hmul i (by omega)
  · intro i hi
    have h := edge_eq_max_weight hc hcard hn (i := i) hi
    by_cases hilast : i + 2 = n
    · rw [show i + 1 = n - 1 by omega, hint i (by omega) (by omega),
        max_eq_left (by nlinarith)] at h
      rw [show i + 1 = n - 1 by omega]
      nlinarith
    rw [hint (i + 1) (by omega) (by omega)] at h
    by_cases hi0 : i = 0
    · subst i
      simp only [Nat.zero_add] at h ⊢
      rw [max_eq_right (by nlinarith)] at h
      nlinarith
    · rw [hint i (by omega) (by omega), max_self] at h
      nlinarith

private lemma shape_of_both_double {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0)
    {W : ℤ} (hW : 0 < W)
    (hint : ∀ i, 0 < i → i + 1 < n → (T.weight (c i) : ℤ) = W)
    (hleft : (T.weight (c 0) : ℤ) = 2 * W)
    (hright : (T.weight (c (n - 1)) : ℤ) = 2 * W) :
    T.IsGenusOneLongPathShape n c := by
  have hmul := multiplicity_eq_two_mul_of_left_double hc hcard hn hzero hW hint hleft
  have hrightMul := right_multiplicity_eq_of_right_double hc hcard hn hzero hW hint hright
  have hlast : (T.multiplicity (c (n - 1)) : ℤ) = T.multiplicity (c 0) := by
    have hprev := hmul (n - 2) (by omega) (by omega)
    nlinarith
  refine ⟨W, T.multiplicity (c 0), hW, by simp, .inr (.inr ⟨?_, ?_, ?_⟩)⟩
  · intro i hi
    by_cases hend : i = 0 ∨ i + 1 = n
    · simp only [hend, ↓reduceIte]
      rcases hend with rfl | hend
      · exact hleft
      · rw [show i = n - 1 by omega, hright]
    · simp only [hend, ↓reduceIte]
      exact hint i (by omega) (by omega)
  · intro i hi
    by_cases hend : i = 0 ∨ i + 1 = n
    · simp only [hend, ↓reduceIte]
      rcases hend with rfl | hend
      · rfl
      · rw [show i = n - 1 by omega, hlast]
    · simp only [hend, ↓reduceIte]
      exact hmul i (by omega) (by omega)
  · intro i hi
    by_cases hend : i = 0 ∨ i + 2 = n
    · simp only [hend, ↓reduceIte]
      rcases hend with rfl | hend
      · have h := edge_eq_max_weight hc hcard hn (i := 0) hi
        rw [hleft, hint 1 (by omega) (by omega), max_eq_left (by omega)] at h
        simpa using h
      · have h := edge_eq_max_weight hc hcard hn (i := i) hi
        rw [show i + 1 = n - 1 by omega, hint i (by omega) (by omega), hright,
          max_eq_right (by omega)] at h
        simpa only [show i + 1 = n - 1 by omega] using h
    · simp only [hend, ↓reduceIte]
      have h := edge_eq_max_weight hc hcard hn (i := i) hi
      rw [hint i (by omega) (by omega), hint (i + 1) (by omega) (by omega), max_self] at h
      exact h

/-- A path of at least six components exhausting a numerical type, with self-intersections
`-2w`, has one of the three arbitrary-length genus-one path shapes, possibly after reversing its
orientation. This is cases (26)--(28) of Stacks, Tag 0C8T. -/
theorem isGenusOneLongPathShape_or_isGenusOneLongPathShape {n : ℕ}
    (hcard : Fintype.card T.Component = n) (hn : 6 ≤ n) {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0) :
    T.IsGenusOneLongPathShape n c ∨
      T.IsGenusOneLongPathShape n (fun i ↦ c (n - 1 - i)) := by
  obtain ⟨W, hW, hint, hleft, hright⟩ := interior_weight_eq hc hcard hn
  let cr : ℕ → T.Component := fun i ↦ c (n - 1 - i)
  have hcRev : T.IsSelfIntersectionMinusTwoChain n cr := hc.reverse
  have hzeroRev := nonconsecutive_zero_reverse hzero
  have hintRev : ∀ i, 0 < i → i + 1 < n → (T.weight (cr i) : ℤ) = W := by
    intro i hi hin
    exact hint (n - 1 - i) (by omega) (by omega)
  rcases hleft with hleft | hleft | hleft
  · exact (false_of_left_equal hc hcard hn hzero hW hint hleft hright).elim
  · rcases hright with hright | hright | hright
    · have hleftRev : (T.weight (cr 0) : ℤ) = W := by simpa [cr] using hright
      have hrightRev : (T.weight (cr (n - 1)) : ℤ) = 2 * W := by
        simpa [cr, show n - 1 - (n - 1) = 0 by omega] using hleft
      exact (false_of_left_equal hcRev hcard hn hzeroRev hW hintRev hleftRev
        (.inr (.inl hrightRev))).elim
    · exact .inl (shape_of_both_double hc hcard hn hzero hW hint hleft hright)
    · right
      have hleftRev : 2 * (T.weight (cr 0) : ℤ) = W := by simpa [cr] using hright
      have hrightRev : (T.weight (cr (n - 1)) : ℤ) = 2 * W := by
        simpa [cr, show n - 1 - (n - 1) = 0 by omega] using hleft
      exact shape_of_left_half_right_double hcRev hcard hn hzeroRev hW hintRev
        hleftRev hrightRev
  · rcases hright with hright | hright | hright
    · have hleftRev : (T.weight (cr 0) : ℤ) = W := by simpa [cr] using hright
      have hrightRev : 2 * (T.weight (cr (n - 1)) : ℤ) = W := by
        simpa [cr, show n - 1 - (n - 1) = 0 by omega] using hleft
      exact (false_of_left_equal hcRev hcard hn hzeroRev hW hintRev hleftRev
        (.inr (.inr hrightRev))).elim
    · exact .inl (shape_of_left_half_right_double hc hcard hn hzero hW hint hleft hright)
    · exact .inl (shape_of_both_half hc hcard hn hzero hW hint hleft hright)

/-- A minimal numerical type of genus one whose components form a path of length at least six has
one of the three arbitrary-length path shapes in cases (26)--(28) of Stacks, Tag 0C8T, possibly
after reversing the path. -/
theorem isGenusOneLongPathShape_or_isGenusOneLongPathShape_of_isMinimal_and_arithmeticGenus_eq_one
    {n : ℕ} (hcard : Fintype.card T.Component = n) (hn : 6 ≤ n)
    (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1) {c : ℕ → T.Component}
    (hinj : ∀ i < n, ∀ j < n, c i = c j → i = j)
    (hpos : ∀ i, i + 1 < n → 0 < T.intersection (c i) (c (i + 1)))
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0) :
    T.IsGenusOneLongPathShape n c ∨
      T.IsGenusOneLongPathShape n (fun i ↦ c (n - 1 - i)) := by
  have h₂ := (T.isMinimal_and_arithmeticGenus_eq_one_iff (by omega)).mp ⟨hT, hg⟩
  apply T.isGenusOneLongPathShape_or_isGenusOneLongPathShape hcard hn
  · exact ⟨hinj, fun i hi ↦ (T.isMinusTwoIndex_iff.mp (h₂ (c i))).2, hpos⟩
  · exact hzero

end TauCeti.NumericalType
