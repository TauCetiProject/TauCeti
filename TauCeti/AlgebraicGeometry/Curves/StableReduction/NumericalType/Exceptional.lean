/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Fork
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Branch
import Mathlib.Tactic.IntervalCases

/-!
# Exceptional configurations of `(-2)`-indices

This file continues the classification of connected proper subgraphs of `(-2)`-indices in a
numerical type with the exceptional diagram `E₇`.  A chain of six components with an extra leaf
at its fourth component is simply laced: all seven weights and all six displayed intersections
agree, and there are no other edges.  This gives the weight and intersection part of
[Stacks, Lemma 55.5.13](https://stacks.math.columbia.edu/tag/0C8J).

Extending the length-two arm of this diagram by one component produces the affine `E₇`
diagram.  Its marks `(1, 2, 3, 4, 3, 2, 1, 2)` form a positive kernel vector for the displayed
intersection matrix.  Negative definiteness on a proper family of components therefore rules
out this configuration, which is
[Stacks, Lemma 55.5.15](https://stacks.math.columbia.edu/tag/0C8N).

## Main results

* `TauCeti.NumericalType.exists_weight_intersection_branch_seven_eq`: the `E₇`
  configuration is simply laced.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.intersection_branch_eq_zero`:
  a distinct eighth `(-2)`-index cannot meet the middle component of the chain, excluding the
  affine `E₇` configuration.
-/

public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable (T : NumericalType.{u})

/-- A chain `c₁ - c₂ - c₃ - c₄ - c₅ - c₆` of `(-2)`-indices, together with a
seventh `(-2)`-index meeting `c₄`, is simply laced.  Thus all seven weights agree, every
displayed intersection is that common weight, and the seventh component meets no other component
of the chain.  Together with the chain's no-chord theorem, this gives the weight and intersection
claims for the proper `E₇` configuration in
[Stacks, Lemma 55.5.13](https://stacks.math.columbia.edu/tag/0C8J). -/
theorem exists_weight_intersection_branch_seven_eq
    {c : ℕ → T.Component} (hc : T.IsSelfIntersectionMinusTwoChain 6 c)
    {branch : T.Component} (hbranch_ne : ∀ i < 6, branch ≠ c i)
    (hbranch_self : T.intersection branch branch = -(2 * (T.weight branch : ℤ)))
    (hbranch_pos : 0 < T.intersection (c 3) branch) :
    ∃ w : ℕ+, (∀ i < 6, (T.weight (c i) : ℤ) = w) ∧
      (T.weight branch : ℤ) = w ∧
      (∀ i, i + 1 < 6 → T.intersection (c i) (c (i + 1)) = w) ∧
      T.intersection (c 3) branch = w ∧
      ∀ i < 6, i ≠ 3 → T.intersection (c i) branch = 0 := by
  -- The first five chain components and the extra leaf form a fork; its generic classification
  -- fixes all data except the final component `c 5`.
  have hf : T.IsSelfIntersectionMinusTwoFork 5 c branch := {
    toIsSelfIntersectionMinusTwoChain := hc.mono (by omega)
    two_lt := by omega
    branch_ne := fun i hi ↦ hbranch_ne i (by omega)
    branch_intersection_self := hbranch_self
    branch_intersection_pos := by norm_num; exact hbranch_pos }
  have hcard : 6 < Fintype.card T.Component := hc.le_card_snoc hbranch_ne
  obtain ⟨w, hw, hwb, hedge, hab⟩ := hf.exists_weight_intersection_eq hcard
  -- The `E₆` subconfiguration on `c 1, …, c 5` and the same leaf supplies the final weight,
  -- edge, and non-edge.
  obtain ⟨w', _, _, hw₃, _, hw₅, -, -, -, -, ha₄₅, -, -, -, -, -, -, -, -, -,
      -, hbranch5⟩ :=
    T.exists_weight_intersection_branch_six_eq (c₁ := c 1) (c₂ := c 2) (c₃ := c 3)
      (c₄ := c 4) (c₅ := c 5) (c₆ := branch) hcard
      (hc.intersection_self 1 (by omega)) (hc.intersection_self 2 (by omega))
      (hc.intersection_self 3 (by omega)) (hc.intersection_self 4 (by omega))
      (hc.intersection_self 5 (by omega)) hbranch_self
      (hc.ne (by omega) (by omega) (by omega))
      (hc.ne (by omega) (by omega) (by omega))
      (hc.ne (by omega) (by omega) (by omega)) (hbranch_ne 1 (by omega)).symm
      (hc.ne (by omega) (by omega) (by omega))
      (hc.ne (by omega) (by omega) (by omega)) (hbranch_ne 2 (by omega)).symm
      (hc.ne (by omega) (by omega) (by omega))
      (hbranch_ne 4 (by omega)).symm (hbranch_ne 5 (by omega)).symm
      (hc.intersection_succ_pos 1 (by omega)) (hc.intersection_succ_pos 2 (by omega))
      (hc.intersection_succ_pos 3 (by omega)) (hc.intersection_succ_pos 4 (by omega))
      hbranch_pos
  have hww : (w' : ℤ) = w := hw₃.symm.trans (hw 3 (by omega))
  have hw5 : (T.weight (c 5) : ℤ) = w := hw₅.trans hww
  have ha45 : T.intersection (c 4) (c 5) = w := ha₄₅.trans hww
  refine ⟨w, ?_, hwb, ?_, hab, ?_⟩
  · intro i hi
    by_cases hi5 : i < 5
    · exact hw i hi5
    · have : i = 5 := by omega
      simpa [this] using hw5
  · intro i hi
    by_cases hi4 : i < 4
    · exact hedge i (by omega)
    · have : i = 4 := by omega
      simpa [this] using ha45
  · intro i hi hi3
    by_cases hi5 : i < 5
    · exact hf.branch_intersection_eq_zero hi5 (by omega)
    · have : i = 5 := by omega
      simpa [this] using hbranch5

namespace IsSelfIntersectionMinusTwoChain

/-- A distinct eighth `(-2)`-index cannot meet the middle component of a chain of seven
`(-2)`-indices when the numerical type has any further component.  This excludes the affine
`E₇` diagram as a proper subgraph, as in
[Stacks, Lemma 55.5.15](https://stacks.math.columbia.edu/tag/0C8N). -/
theorem intersection_branch_eq_zero {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain 7 c)
    (hcard : 8 < Fintype.card T.Component) {branch : T.Component}
    (hbranch_ne : ∀ i < 7, branch ≠ c i)
    (hbranch_self : T.intersection branch branch = -(2 * (T.weight branch : ℤ))) :
    T.intersection (c 3) branch = 0 := by
  by_contra hbranch_nonzero
  have hbranch_pos : 0 < T.intersection (c 3) branch :=
    (T.offDiagonal_nonneg _ _ (hbranch_ne 3 (by omega)).symm).lt_of_ne
      (Ne.symm hbranch_nonzero)
  -- Classify the two overlapping finite `E₇` subdiagrams obtained by omitting the right,
  -- respectively left, endpoint. This identifies every entry of the affine diagram.
  obtain ⟨w, hw, hwb, hedge, hab, hbranch_zero⟩ :=
    T.exists_weight_intersection_branch_seven_eq (hc.mono (by omega))
      (fun i hi ↦ hbranch_ne i (by omega)) hbranch_self hbranch_pos
  let r : ℕ → T.Component := fun i ↦ c (6 - i)
  have hr : T.IsSelfIntersectionMinusTwoChain 6 r := by
    simpa [r] using hc.reverse.mono (s := 6) (by omega)
  obtain ⟨w', hwr, -, hredge, -, hrbranch_zero⟩ :=
    T.exists_weight_intersection_branch_seven_eq hr (fun i hi ↦ hbranch_ne (6 - i) (by omega))
      hbranch_self (by simpa [r] using hbranch_pos)
  have hww : (w' : ℤ) = w := (hwr 3 (by omega)).symm.trans (hw 3 (by omega))
  have hweight (i : ℕ) (hi : i < 7) : (T.weight (c i) : ℤ) = w := by
    obtain h | rfl : i < 6 ∨ i = 6 := by omega
    · exact hw i h
    · simpa [r, hww] using hwr 0 (by omega)
  have hedge' (i : ℕ) (hi : i + 1 < 7) : T.intersection (c i) (c (i + 1)) = w := by
    obtain h | rfl : i < 5 ∨ i = 5 := by omega
    · exact hedge i (by omega)
    · rw [T.intersection_comm]
      simpa [r, hww] using hredge 0 (by omega)
  have hentry {i j : ℕ} (hi : i < 7) (hj : j < 7) :=
    hc.intersection_eq_ite (by omega) hweight hedge' hi hj
  have hbranch_entry {i : ℕ} (hi : i < 7) :
      T.intersection (c i) branch = if i = 3 then (w : ℤ) else 0 := by
    split_ifs with h3
    · subst h3
      exact hab
    · obtain h | rfl : i < 6 ∨ i = 6 := by omega
      · exact hbranch_zero i h h3
      · simpa [r] using hrbranch_zero 0 (by omega) (by omega)
  -- The affine `E₇` marks `1, 2, 3, 4, 3, 2, 1` on the chain and `2` on the branch give a
  -- positive vector whose rows all vanish, contradicting negative definiteness.
  let d : ℕ → T.Component := fun i ↦ if i = 7 then branch else c i
  let y : ℕ → ℤ := fun i ↦ if i = 7 then 2 else if i ≤ 3 then i + 1 else 7 - i
  have hd_inj : ∀ i < 8, ∀ j < 8, d i = d j → i = j := by
    simpa only [d] using hc.injOn_snoc hbranch_ne
  refine T.not_forall_sum_intersection_mul_nonneg_of_pos hd_inj hcard (y := y)
    (fun i _ ↦ by simp only [y]; split_ifs <;> omega) ⟨0, by omega, by simp [y]⟩ fun i hi ↦ ?_
  interval_cases i <;>
    norm_num [Finset.sum_range_succ, d, y] <;>
    simp [hentry, hbranch_entry, T.intersection_comm branch, hbranch_self, hwb] <;>
    omega

end IsSelfIntersectionMinusTwoChain

end NumericalType

end TauCeti
