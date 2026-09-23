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
# Exceptional configurations of `(-2)`-indices

This file continues the classification of connected proper subgraphs of `(-2)`-indices in a
numerical type with the exceptional diagram `E₇`.  A chain of six components with an extra leaf
at its fourth component is simply laced: all seven weights and all six displayed intersections
agree, and there are no other edges.  This is
[Stacks, Lemma 55.5.13](https://stacks.math.columbia.edu/tag/0C8J).

Extending both length-three arms of this diagram by one component produces the affine `E₇`
diagram.  Its marks `(1, 2, 3, 4, 3, 2, 1, 2)` form a positive kernel vector for the displayed
intersection matrix.  Negative definiteness on a proper family of components therefore rules
out this configuration, which is
[Stacks, Lemma 55.5.15](https://stacks.math.columbia.edu/tag/0C8N).

## Main results

* `TauCeti.NumericalType.exists_weight_intersection_branch_seven_eq`: the `E₇`
  configuration is simply laced.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoChain.not_affineE7`: the affine `E₇`
  configuration cannot be a proper subgraph of `(-2)`-indices.
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
of the chain.  Together with the chain's no-chord theorem, this gives the classification of the
proper `E₇` configuration in
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
  let f : Fin 7 → T.Component := fun i ↦ if (i : ℕ) = 6 then branch else c i
  have hf_injective : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_cases hi6 : (i : ℕ) = 6
    · by_cases hj6 : (j : ℕ) = 6
      · exact hi6.trans hj6.symm
      · exact (hbranch_ne j (by omega) (by simpa [f, hi6, hj6] using hij)).elim
    · by_cases hj6 : (j : ℕ) = 6
      · exact (hbranch_ne i (by omega) (by simpa [f, hi6, hj6] using hij.symm)).elim
      · exact hc.injOn i (by omega) j (by omega) (by simpa [f, hi6, hj6] using hij)
  have hcard : 6 < Fintype.card T.Component := by
    have := Fintype.card_le_of_injective f hf_injective
    have hseven : 7 ≤ Fintype.card T.Component := by simpa using this
    omega
  obtain ⟨w, hw, hwb, hedge, hab⟩ := hf.exists_weight_intersection_eq hcard
  -- The `E₆` subconfiguration on `c 1, …, c 5` and the same leaf supplies the final weight,
  -- edge, and non-edge.
  obtain ⟨w', hw₁, hw₂, hw₃, hw₄, hw₅, -, -, -, -, ha₄₅, -, -, -, -, -, -, -, -, -,
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

/-- The affine `E₇` diagram cannot occur as a proper subgraph of `(-2)`-indices.  Concretely,
a chain of seven `(-2)`-indices cannot have a distinct eighth `(-2)`-index meeting its middle
component when the numerical type has any further component.  This is
[Stacks, Lemma 55.5.15](https://stacks.math.columbia.edu/tag/0C8N). -/
theorem not_affineE7 {c : ℕ → T.Component}
    (hc : T.IsSelfIntersectionMinusTwoChain 7 c)
    (hcard : 8 < Fintype.card T.Component) {branch : T.Component}
    (hbranch_ne : ∀ i < 7, branch ≠ c i)
    (hbranch_self : T.intersection branch branch = -(2 * (T.weight branch : ℤ)))
    (hbranch_pos : 0 < T.intersection (c 3) branch) : False := by
  -- Classify the two overlapping finite `E₇` subdiagrams obtained by omitting the right,
  -- respectively left, endpoint. This identifies every entry of the affine diagram.
  obtain ⟨w, hw, hwb, hedge, hab, hbranch_zero⟩ :=
    T.exists_weight_intersection_branch_seven_eq (hc.mono (by omega))
      (fun i hi ↦ hbranch_ne i (by omega)) hbranch_self hbranch_pos
  let r : ℕ → T.Component := fun i ↦ c (6 - i)
  have hr : T.IsSelfIntersectionMinusTwoChain 6 r := {
    injOn i hi j hj hij := by
      have h := hc.injOn (6 - i) (by omega) (6 - j) (by omega) hij
      omega
    intersection_self i hi := by
      exact hc.intersection_self (6 - i) (by omega)
    intersection_succ_pos i hi := by
      have h := hc.intersection_succ_pos (5 - i) (by omega)
      have hsucc : 5 - i + 1 = 6 - i := by omega
      have hrev : 6 - (i + 1) = 5 - i := by omega
      rw [hsucc] at h
      simpa only [r, hrev, T.intersection_comm] using h }
  have hrbranch_ne : ∀ i < 6, branch ≠ r i := by
    intro i hi
    exact hbranch_ne (6 - i) (by omega)
  obtain ⟨w', hwr, -, hredge, -, hrbranch_zero⟩ :=
    T.exists_weight_intersection_branch_seven_eq hr hrbranch_ne hbranch_self
      (by simpa [r] using hbranch_pos)
  have hww : (w' : ℤ) = w := (hwr 3 (by omega)).symm.trans (hw 3 (by omega))
  have hw6 : (T.weight (c 6) : ℤ) = w := by
    simpa [r, hww] using hwr 0 (by omega)
  have hedge56 : T.intersection (c 5) (c 6) = w := by
    rw [T.intersection_comm]
    simpa [r, hww] using hredge 0 (by omega)
  have hbranch6 : T.intersection (c 6) branch = 0 := by
    simpa [r] using hrbranch_zero 0 (by omega) (by omega)
  have hweight : ∀ i < 7, (T.weight (c i) : ℤ) = w := by
    intro i hi
    by_cases hi6 : i < 6
    · exact hw i hi6
    · have : i = 6 := by omega
      simpa [this] using hw6
  have hedge' : ∀ i, i + 1 < 7 → T.intersection (c i) (c (i + 1)) = w := by
    intro i hi
    by_cases hi5 : i < 5
    · exact hedge i (by omega)
    · have : i = 5 := by omega
      simpa [this] using hedge56
  have hzero : ∀ {i j}, i < 7 → j < 7 → i + 1 < j →
      T.intersection (c i) (c j) = 0 := by
    intro i j hi hj hij
    exact hc.intersection_eq_zero (by omega) hi hj (by omega) (by omega) (by omega)
  have hbranch_zero' : ∀ i < 7, i ≠ 3 → T.intersection (c i) branch = 0 := by
    intro i hi hi3
    by_cases hi6 : i < 6
    · exact hbranch_zero i hi6 hi3
    · have : i = 6 := by omega
      simpa [this] using hbranch6
  have hentry {i j : ℕ} (hi : i < 7) (hj : j < 7) :
      T.intersection (c i) (c j) =
        if i = j then -(2 * (w : ℤ))
        else if i + 1 = j ∨ j + 1 = i then w else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte]
      rw [hc.intersection_self i hi, hweight i hi]
    · simp only [hij, ↓reduceIte]
      by_cases hadj : i + 1 = j ∨ j + 1 = i
      · simp only [hadj, ↓reduceIte]
        rcases hadj with rfl | hji
        · exact hedge' i (by omega)
        · rw [T.intersection_comm]
          subst i
          exact hedge' j (by omega)
      · simp only [hadj, ↓reduceIte]
        rcases lt_or_gt_of_ne hij with hijlt | hjilt
        · exact hzero hi hj (by omega)
        · rw [T.intersection_comm]
          exact hzero hj hi (by omega)
  have hbranch_entry {i : ℕ} (hi : i < 7) :
      T.intersection (c i) branch = if i = 3 then (w : ℤ) else 0 := by
    by_cases hi3 : i = 3
    · subst i
      simp only [↓reduceIte]
      exact hab
    · simp only [hi3, ↓reduceIte]
      exact hbranch_zero' i hi hi3
  -- Relabel the eight components by the canonical affine-`E₇` numbering. The existing root-system
  -- marks then give the positive vector excluded by negative definiteness.
  let d : ℕ → T.Component := fun i ↦ if i < 7 then c i else branch
  let e : Fin 8 → Fin AffineDynkinType.E7.nodes := ![4, 3, 2, 0, 5, 6, 7, 1]
  let y : ℕ → ℤ := fun i ↦
    if hi : i < 8 then AffineDynkinType.E7.marks (e ⟨i, hi⟩) else 0
  have hd_inj : ∀ i < 8, ∀ j < 8, d i = d j → i = j := by
    intro i hi j hj hij
    by_cases hi7 : i < 7
    · by_cases hj7 : j < 7
      · exact hc.injOn i hi7 j hj7 (by simpa [d, hi7, hj7] using hij)
      · have hj_eq : j = 7 := by omega
        subst j
        exact (hbranch_ne i hi7 (by simpa [d, hi7] using hij.symm)).elim
    · have hi_eq : i = 7 := by omega
      subst i
      by_cases hj7 : j < 7
      · exact (hbranch_ne j hj7 (by simpa [d, hj7] using hij)).elim
      · omega
  refine T.not_forall_sum_intersection_mul_nonneg_of_pos hd_inj hcard (y := y) ?_ ?_ ?_
  · intro i hi
    simpa [y, hi] using (AffineDynkinType.marks_pos (e ⟨i, hi⟩)).le
  · refine ⟨0, by omega, ?_⟩
    simpa [y] using (AffineDynkinType.marks_pos (e ⟨0, by omega⟩))
  · intro i hi
    interval_cases i <;>
      norm_num [Finset.sum_range_succ, d, y, e, AffineDynkinType.marks_E7] <;>
      simp [hentry, hbranch_entry, T.intersection_comm branch, hbranch_self, hwb] <;>
      omega

end IsSelfIntersectionMinusTwoChain

end NumericalType

end TauCeti
