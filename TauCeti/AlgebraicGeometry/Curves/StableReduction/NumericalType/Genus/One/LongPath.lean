/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Chain
import TauCeti.Algebra.Group.AffineSequence
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

universe u

variable {T : NumericalType.{u}}

/-- The numerical data of the three arbitrary-length path shapes among the minimal numerical
types of genus one: the weights, multiplicities and consecutive intersection numbers of
`c 0, …, c (n - 1)` follow one of three patterns. This predicate records only these numerical
patterns; that `c` is a path of length at least six exhausting the components, with
nonconsecutive components not meeting, must be supplied as separate hypotheses. -/
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

/-- The fibre relation at an interior component `c (i + 1)` of constant weight `W`, whose left
edge has intersection number `W`. -/
private lemma multiplicity_add_eq_two_mul {n : ℕ} {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain n c) (hcard : Fintype.card T.Component = n)
    (hn : 6 ≤ n)
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0)
    {W : ℤ} (hW : 0 < W)
    (hint : ∀ i, 0 < i → i + 1 < n → (T.weight (c i) : ℤ) = W) {i : ℕ} (hi : i + 3 < n)
    (hedge : T.intersection (c i) (c (i + 1)) = W) :
    (T.multiplicity (c i) : ℤ) + T.multiplicity (c (i + 2)) =
      2 * T.multiplicity (c (i + 1)) := by
  have hnext : T.intersection (c (i + 1)) (c (i + 2)) = W := by
    rw [edge_eq_max_weight hc hcard hn (by omega), hint (i + 1) (by omega) (by omega),
      hint (i + 1 + 1) (by omega) (by omega), max_self]
  have h := interior_fiber_relation hc.injOn hcard hzero (i := i + 1) (by omega) (by omega)
  rw [Nat.add_sub_cancel, show i + 1 + 1 = i + 2 by omega,
    T.intersection_comm (c (i + 1)) (c i), hedge, hnext,
    hc.intersection_self (i + 1) (by omega), hint (i + 1) (by omega) (by omega)] at h
  apply mul_left_cancel₀ hW.ne'
  linear_combination h

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
    have h := left_fiber_relation hc.injOn hcard (by omega) hzero
    rw [hc.intersection_self 0 (by omega), hedge 0 (by omega)] at h
    apply mul_left_cancel₀ hW.ne'
    linear_combination h + (T.multiplicity (c 0) : ℤ) * hleft
  intro i hi
  rw [eq_add_nsmul_sub_of_add_eq_two_nsmul (f := fun i ↦ (T.multiplicity (c i) : ℤ))
    (fun i hi ↦ multiplicity_add_eq_two_mul hc hcard hn hzero hW hint (by omega)
      (hedge i (by omega))) i hi, hone, sub_self, smul_zero, add_zero]

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
    have h := left_fiber_relation hc.injOn hcard (by omega) hzero
    rw [hc.intersection_self 0 (by omega), hleft, hedge0] at h
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hW.ne')
    linear_combination h
  have htwo : (T.multiplicity (c 2) : ℤ) = 2 * T.multiplicity (c 0) := by
    have h := interior_fiber_relation hc.injOn hcard hzero (i := 1) (by omega) (by omega)
    rw [Nat.sub_self, T.intersection_comm (c 1) (c 0), hedge0,
      hc.intersection_self 1 (by omega), hint 1 (by omega) (by omega),
      hedge 1 (by omega) (by omega), hone] at h
    apply mul_left_cancel₀ hW.ne'
    linear_combination h
  intro i hi hi0
  have h := eq_add_nsmul_sub_of_add_eq_two_nsmul (N := n - 2)
    (f := fun j ↦ (T.multiplicity (c (j + 1)) : ℤ))
    (fun j hj ↦ multiplicity_add_eq_two_mul hc hcard hn hzero hW hint (by omega)
      (hedge (j + 1) (by omega) (by omega))) (i - 1) (by omega)
  simp only [Nat.sub_add_cancel hi0, Nat.zero_add, show 1 + 1 = 2 from rfl, hone, htwo,
    sub_self, smul_zero, add_zero] at h
  exact h

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
    have h := left_fiber_relation hc.injOn hcard (by omega) hzero
    rw [hc.intersection_self 0 (by omega), hleft, hedge 0 (by omega)] at h
    apply mul_left_cancel₀ hW.ne'
    linear_combination h
  intro i hi
  rw [eq_add_nsmul_sub_of_add_eq_two_nsmul (f := fun i ↦ (T.multiplicity (c i) : ℤ))
    (fun i hi ↦ multiplicity_add_eq_two_mul hc hcard hn hzero hW hint (by omega)
      (hedge i (by omega))) i hi, hone, nsmul_eq_mul]
  push_cast
  linear_combination

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
  have h := right_fiber_relation hc.injOn hcard (by omega) hzero
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
  have h := right_fiber_relation hc.injOn hcard (by omega) hzero
  rw [T.intersection_comm (c (n - 1)) (c (n - 2)), hedge,
    hc.intersection_self (n - 1) (by omega), hright] at h
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hW.ne')
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
  push_cast at hprev hbefore
  rw [show ((n - 2 : ℕ) : ℤ) + 1 = (n : ℤ) - 1 by omega] at hprev
  rw [show ((n - 3 : ℕ) : ℤ) + 1 = (n : ℤ) - 2 by omega] at hbefore
  have hm0 : (0 : ℤ) < T.multiplicity (c 0) := by simp
  have hedge (i : ℕ) (hi : 0 < i) (hin : i + 1 < n) : T.intersection (c i) (c (i + 1)) =
      max W (T.weight (c (i + 1)) : ℤ) := by
    rw [edge_eq_max_weight hc hcard hn hin, hint i hi hin]
  have hedgeBefore := hedge (n - 3) (by omega) (by omega)
  have hedgeLast := hedge (n - 2) (by omega) (by omega)
  rw [show n - 3 + 1 = n - 2 by omega, hint (n - 2) (by omega) (by omega), max_self]
    at hedgeBefore
  rw [show n - 2 + 1 = n - 1 by omega] at hedgeLast
  have hP := interior_fiber_relation hc.injOn hcard hzero (i := n - 2) (by omega) (by omega)
  rw [show n - 2 - 1 = n - 3 by omega, show n - 2 + 1 = n - 1 by omega,
    T.intersection_comm (c (n - 2)) (c (n - 3)), hedgeBefore, hedgeLast,
    hc.intersection_self (n - 2) (by omega), hint (n - 2) (by omega) (by omega)] at hP
  rcases hright with hright | hright | hright
  · have hR := right_fiber_relation hc.injOn hcard (by omega) hzero
    rw [T.intersection_comm (c (n - 1)) (c (n - 2)), hedgeLast,
      hc.intersection_self (n - 1) (by omega), hright, max_self] at hR
    rw [hright, max_self] at hP
    have eR : (T.multiplicity (c (n - 2)) : ℤ) = 2 * T.multiplicity (c (n - 1)) := by
      apply mul_left_cancel₀ hW.ne'
      linear_combination hR
    have eP : (T.multiplicity (c (n - 3)) : ℤ) + T.multiplicity (c (n - 1)) =
        2 * T.multiplicity (c (n - 2)) := by
      apply mul_left_cancel₀ hW.ne'
      linear_combination hP
    have hmlast : (0 : ℤ) < T.multiplicity (c (n - 1)) := by simp
    nlinarith
  · have eR := right_multiplicity_eq_of_right_double hc hcard hn hzero hW hint hright
    rw [hright, max_eq_right (by omega), eR] at hP
    have eP : (T.multiplicity (c (n - 3)) : ℤ) = 2 * T.multiplicity (c (n - 1)) := by
      apply mul_left_cancel₀ hW.ne'
      linear_combination hP
    nlinarith
  · have eR := right_multiplicity_eq_of_right_half hc hcard hn hzero hW hint hright
    rw [max_eq_left (by omega), eR] at hP
    have eP : (T.multiplicity (c (n - 3)) : ℤ) = T.multiplicity (c (n - 1)) := by
      apply mul_left_cancel₀ hW.ne'
      linear_combination hP
    nlinarith

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
  have hzeroRev := intersection_reverse_eq_zero_of_nonconsecutive hzero
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

/-- For a genus-one long path on a minus-two chain exhausting all components, some component's
weight divides every weight with quotient at most four, and some component's multiplicity
divides every multiplicity with quotient at most six. -/
lemma IsGenusOneLongPathShape.exists_weight_and_multiplicity_dvd_and_le
    {n : ℕ} {c : ℕ → T.Component} (hlong : T.IsGenusOneLongPathShape n c)
    (hn : 3 ≤ n) (hcard : Fintype.card T.Component = n)
    (hc : T.IsSelfIntersectionMinusTwoChain n c) :
    (∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j) ∧
      (∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
        (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j) := by
  classical
  obtain ⟨w, m, _, _, ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩⟩ :=
    isGenusOneLongPathShape_iff.mp hlong
  · refine T.exists_weight_and_multiplicity_dvd_and_le_of_int (nw := 4) (nm := 6) (c 0) (c (n - 1))
      (fun i ↦ ?_) (fun i ↦ ?_)
    all_goals simp only [← Nat.lt_succ_iff, Nat.exists_lt_succ_right]
    · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
      have hwk := hw k hk; have hw0 := hw 0 (by omega); split_ifs at hwk hw0 <;> omega
    · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
      have hmk := hm k hk; have hm0 := hm (n - 1) (by omega); split_ifs at hmk hm0 <;> omega
  · refine T.exists_weight_and_multiplicity_dvd_and_le_of_int (nw := 4) (nm := 6)
      (c 0) (c 0) (fun i ↦ ?_) (fun i ↦ ?_)
    all_goals simp only [← Nat.lt_succ_iff, Nat.exists_lt_succ_right]
    · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
      have hwk := hw k hk; have hw0 := hw 0 (by omega); split_ifs at hwk hw0 <;> omega
    · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
      have hmk := hm k hk; have hm0 := hm 0 (by omega); omega
  · refine T.exists_weight_and_multiplicity_dvd_and_le_of_int (nw := 4) (nm := 6)
      (c 1) (c 0) (fun i ↦ ?_) (fun i ↦ ?_)
    all_goals simp only [← Nat.lt_succ_iff, Nat.exists_lt_succ_right]
    · have hw1 := hw 1 (by omega); rw [ite_eq_right (by omega)] at hw1
      obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
      have hwk := hw k hk; split_ifs at hwk <;> omega
    · have hm0 := hm 0 (by omega); rw [ite_eq_left (by omega)] at hm0
      obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
      have hmk := hm k hk; split_ifs at hmk <;> omega

end TauCeti.NumericalType
