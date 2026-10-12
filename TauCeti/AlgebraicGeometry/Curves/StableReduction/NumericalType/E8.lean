/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Fork
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Branch
import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Exceptional `E₈` configurations of `(-2)`-indices

This file treats finite and affine `E₈` configurations of `(-2)`-indices occurring in the
classification of connected proper subgraphs of a numerical type. A chain of seven components
with an extra leaf at its fifth component is simply laced: all eight weights and all seven
displayed intersections agree, and there are no other edges. This is
[Stacks, Lemma 55.5.14](https://stacks.math.columbia.edu/tag/0C8L).

Extending the long arm by one component produces the affine `E₈` diagram. Its marks form a
positive kernel vector for the displayed intersection matrix. Negative definiteness on a proper
family of components therefore rules out this configuration, which is
[Stacks, Lemma 55.5.16](https://stacks.math.columbia.edu/tag/0C8P).

## Main results

* `IsSelfIntersectionMinusTwoChain.exists_weight_intersection_branch_eight_eq`: the finite `E₈`
  configuration is simply laced.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.not_affineE8`: the affine `E₈`
  configuration cannot be a proper subgraph of `(-2)`-indices.
-/

public section

namespace TauCeti

open Finset

namespace NumericalType

universe u

variable (T : NumericalType.{u})

variable {T}

namespace IsSelfIntersectionMinusTwoChain

/-- A chain `c₀ - c₁ - ⋯ - c₆` of `(-2)`-indices, together with an eighth
`(-2)`-index meeting `c₄`, is simply laced. Thus all eight weights agree, every displayed
intersection is that common weight, and the eighth component meets no other component of the
chain. This gives the classification of the `E₈` configuration in
[Stacks, Lemma 55.5.14](https://stacks.math.columbia.edu/tag/0C8L). -/
theorem exists_weight_intersection_branch_eight_eq
    {c : ℕ → T.Component} (hc : T.IsSelfIntersectionMinusTwoChain 7 c)
    {branch : T.Component} (hbranch_ne : ∀ i < 7, branch ≠ c i)
    (hbranch_self : T.intersection branch branch = -(2 * (T.weight branch : ℤ)))
    (hbranch_pos : 0 < T.intersection (c 4) branch) :
    ∃ w : ℕ+, (∀ i < 7, (T.weight (c i) : ℤ) = w) ∧
      (T.weight branch : ℤ) = w ∧
      (∀ i, i + 1 < 7 → T.intersection (c i) (c (i + 1)) = w) ∧
      T.intersection (c 4) branch = w ∧
      ∀ i < 7, i ≠ 4 → T.intersection (c i) branch = 0 := by
  -- The first six chain components and the extra leaf form a fork. Its generic classification
  -- fixes all data except the final component `c 6`.
  have hf : T.IsSelfIntersectionMinusTwoFork 6 c branch := {
    toIsSelfIntersectionMinusTwoChain := hc.mono (by omega)
    two_lt := by omega
    branch_ne := fun i hi ↦ hbranch_ne i (by omega)
    branch_intersection_self := hbranch_self
    branch_intersection_pos := by norm_num; exact hbranch_pos }
  have hcard : 7 < Fintype.card T.Component := by
    have height := hc.le_card_snoc hbranch_ne
    omega
  obtain ⟨w, hw, hwb, hedge, hab⟩ := hf.exists_weight_intersection_eq hcard
  -- Reversing the final five chain components gives the finite `E₆` configuration that
  -- supplies the remaining weight, edge, and non-edge.
  obtain ⟨w', hw₆, hw₅, -, -, -, -, ha₆₅, -, -, -, -, -, -, -, hz₆b,
      -, -, -, -, -, -⟩ :=
    T.exists_weight_intersection_branch_six_eq (c₁ := c 6) (c₂ := c 5) (c₃ := c 4)
      (c₄ := c 3) (c₅ := c 2) (c₆ := branch) (by omega)
      (hc.intersection_self 6 (by omega)) (hc.intersection_self 5 (by omega))
      (hc.intersection_self 4 (by omega)) (hc.intersection_self 3 (by omega))
      (hc.intersection_self 2 (by omega)) hbranch_self
      (hc.ne (by omega) (by omega) (by omega))
      (hc.ne (by omega) (by omega) (by omega))
      (hc.ne (by omega) (by omega) (by omega)) (hbranch_ne 6 (by omega)).symm
      (hc.ne (by omega) (by omega) (by omega))
      (hc.ne (by omega) (by omega) (by omega)) (hbranch_ne 5 (by omega)).symm
      (hc.ne (by omega) (by omega) (by omega))
      (hbranch_ne 3 (by omega)).symm (hbranch_ne 2 (by omega)).symm
      (T.intersection_comm (c 5) (c 6) ▸ hc.intersection_succ_pos 5 (by omega))
      (T.intersection_comm (c 4) (c 5) ▸ hc.intersection_succ_pos 4 (by omega))
      (T.intersection_comm (c 3) (c 4) ▸ hc.intersection_succ_pos 3 (by omega))
      (T.intersection_comm (c 2) (c 3) ▸ hc.intersection_succ_pos 2 (by omega))
      hbranch_pos
  have hww : (w' : ℤ) = w := hw₅.symm.trans (hw 5 (by omega))
  have hw6 : (T.weight (c 6) : ℤ) = w := hw₆.trans hww
  have ha56 : T.intersection (c 5) (c 6) = w := by
    rw [T.intersection_comm, ha₆₅, hww]
  refine ⟨w, ?_, hwb, ?_, hab, ?_⟩
  · intro i hi
    by_cases hi6 : i < 6
    · exact hw i hi6
    · have : i = 6 := by omega
      simpa [this] using hw6
  · intro i hi
    by_cases hi5 : i < 5
    · exact hedge i (by omega)
    · have : i = 5 := by omega
      simpa [this] using ha56
  · intro i hi hi4
    by_cases hi6 : i < 6
    · exact hf.branch_intersection_eq_zero hi6 (by omega)
    · have : i = 6 := by omega
      simpa [this] using hz₆b

/-- The affine `E₈` diagram cannot occur as a proper subgraph of `(-2)`-indices. Concretely,
a chain of eight `(-2)`-indices cannot have a distinct ninth `(-2)`-index meeting the component
`c₅` when the numerical type has any further component. This is
[Stacks, Lemma 55.5.16](https://stacks.math.columbia.edu/tag/0C8P). -/
theorem not_affineE8 {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain 8 c)
    (hcard : 9 < Fintype.card T.Component) {branch : T.Component}
    (hbranch_ne : ∀ i < 8, branch ≠ c i)
    (hbranch_self : T.intersection branch branch = -(2 * (T.weight branch : ℤ)))
    (hbranch_pos : 0 < T.intersection (c 5) branch) : False := by
  -- The first seven chain components and the leaf form a proper fork, identifying all entries
  -- except those involving the right endpoint `c 7`.
  have hf : T.IsSelfIntersectionMinusTwoFork 7 c branch := {
    toIsSelfIntersectionMinusTwoChain := hc.mono (by omega)
    two_lt := by omega
    branch_ne := fun i hi ↦ hbranch_ne i (by omega)
    branch_intersection_self := hbranch_self
    branch_intersection_pos := by norm_num; exact hbranch_pos }
  obtain ⟨w, hw, hwb, hedge, hab⟩ := hf.exists_weight_intersection_eq (by omega)
  -- Omitting the left endpoint leaves the finite `E₈` diagram and supplies the remaining
  -- weight, edge, and non-edge.
  let r : ℕ → T.Component := fun i ↦ c (1 + i)
  have hr : T.IsSelfIntersectionMinusTwoChain 7 r := hc.shift (by omega)
  have hrbranch_ne : ∀ i < 7, branch ≠ r i := by
    intro i hi
    exact hbranch_ne (1 + i) (by omega)
  obtain ⟨w', hwr, -, hredge, -, hrbranch_zero⟩ :=
    hr.exists_weight_intersection_branch_eight_eq hrbranch_ne hbranch_self
      (by simpa [r] using hbranch_pos)
  have hww : (w' : ℤ) = w := (hwr 4 (by omega)).symm.trans (hw 5 (by omega))
  have hw7 : (T.weight (c 7) : ℤ) = w := by
    simpa [r, hww] using hwr 6 (by omega)
  have hedge67 : T.intersection (c 6) (c 7) = w := by
    simpa [r, hww] using hredge 5 (by omega)
  have hbranch7 : T.intersection (c 7) branch = 0 := by
    simpa [r] using hrbranch_zero 6 (by omega) (by omega)
  have hweight : ∀ i < 8, (T.weight (c i) : ℤ) = w := by
    intro i hi
    by_cases hi7 : i < 7
    · exact hw i hi7
    · have : i = 7 := by omega
      simpa [this] using hw7
  have hedge' : ∀ i, i + 1 < 8 → T.intersection (c i) (c (i + 1)) = w := by
    intro i hi
    by_cases hi6 : i < 6
    · exact hedge i (by omega)
    · have : i = 6 := by omega
      simpa [this] using hedge67
  have hbranch_zero : ∀ i < 8, i ≠ 5 → T.intersection (c i) branch = 0 := by
    intro i hi hi5
    by_cases hi7 : i < 7
    · exact hf.branch_intersection_eq_zero hi7 (by omega)
    · have : i = 7 := by omega
      simpa [this] using hbranch7
  have hentry {i j : ℕ} (hi : i < 8) (hj : j < 8) :
      T.intersection (c i) (c j) =
        if i = j then -(2 * (w : ℤ))
        else if i + 1 = j ∨ j + 1 = i then w else 0 := by
    exact hc.intersection_eq_ite (by omega) hweight hedge' hi hj
  have hbranch_entry {i : ℕ} (hi : i < 8) :
      T.intersection (c i) branch = if i = 5 then (w : ℤ) else 0 := by
    split_ifs with h
    · subst h
      exact hab
    · exact hbranch_zero i hi h
  -- Relabel the nine components by the canonical affine-`E₈` numbering. The existing marks
  -- then give the positive vector excluded by negative definiteness.
  let d : ℕ → T.Component := fun i ↦ if i = 8 then branch else c i
  let e : Fin 9 → Fin AffineDynkinType.E8.nodes := ![8, 7, 6, 5, 4, 0, 2, 3, 1]
  let y : ℕ → ℤ := fun i ↦
    if hi : i < 9 then AffineDynkinType.E8.marks (e ⟨i, hi⟩) else 0
  have hd_inj : ∀ i < 9, ∀ j < 9, d i = d j → i = j := by
    simpa only [d] using hc.injOn_snoc hbranch_ne
  refine T.not_forall_sum_intersection_mul_nonneg_of_pos hd_inj hcard (y := y) ?_ ?_ ?_
  · intro i hi
    simpa [y, hi] using (AffineDynkinType.marks_pos (e ⟨i, hi⟩)).le
  · refine ⟨0, by omega, ?_⟩
    simpa [y] using (AffineDynkinType.marks_pos (e ⟨0, by omega⟩))
  · intro i hi
    interval_cases i <;>
      norm_num [Finset.sum_range_succ, d, y, e, AffineDynkinType.marks_E8] <;>
      simp [hentry, hbranch_entry, T.intersection_comm branch, hbranch_self, hwb] <;>
      omega

end IsSelfIntersectionMinusTwoChain

end NumericalType

end TauCeti
