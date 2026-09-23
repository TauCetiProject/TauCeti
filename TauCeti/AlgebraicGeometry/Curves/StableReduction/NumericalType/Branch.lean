/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.ProperSubgraph
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Branched chains of `(-2)`-indices in a numerical type

A `(-2)`-index of a numerical type is a component `i` with `gᵢ = 0` and `aᵢᵢ = -2wᵢ`. The
configurations that `(-2)`-indices can form inside a numerical type with strictly more components
are of Dynkin-diagram shape. This file treats the six components obtained by attaching a branch
to the middle of a chain of five,

`c₁ - c₂ - c₃ - c₄ - c₅`, with a branch `c₆` at `c₃`,

that is, the diagram `E₆`. All six weights are equal, each of the five displayed intersection
numbers equals that common weight, and every other intersection number vanishes
([Stacks, Lemma 55.5.10](https://stacks.math.columbia.edu/tag/0C8F)).

The free end `c₆` of the branch meets no seventh component of self-intersection `-2w`: adding one
would lengthen the branch into the affine diagram of type `E₆`, whose intersection matrix is
singular ([Stacks, Lemma 55.5.12](https://stacks.math.columbia.edu/tag/0C8I)). The vector taking
the value three at the trivalent component `c₃`, two at its three neighbours and one at the three
ends spans the kernel, so the intersection form vanishes at it, which negative definiteness on
the vectors supported on a proper subset of the components forbids.

## Main results

* `TauCeti.NumericalType.exists_weight_intersection_branch_six_eq`: a chain of five
  `(-2)`-indices with a branch at its middle component is simply laced, with equal weights and no
  further edges.
* `TauCeti.NumericalType.intersection_eq_zero_of_branch_six`: the free end of that branch meets no
  seventh component of self-intersection `-2w`.
-/

public section

namespace TauCeti

namespace NumericalType

universe u

variable (T : NumericalType.{u})

/-- Six components of self-intersection `-2w` in a numerical type with more than six components
forming the branched chain

`c₁ - c₂ - c₃ - c₄ - c₅`, with a branch `c₆` at `c₃`,

all have the same weight, every displayed intersection equals that weight, and every other
intersection vanishes. This is the classification of
[Stacks, Lemma 55.5.10](https://stacks.math.columbia.edu/tag/0C8F). -/
theorem exists_weight_intersection_branch_six_eq (hcard : 6 < Fintype.card T.Component)
    {c₁ c₂ c₃ c₄ c₅ c₆ : T.Component}
    (h₁ : T.intersection c₁ c₁ = -(2 * (T.weight c₁ : ℤ)))
    (h₂ : T.intersection c₂ c₂ = -(2 * (T.weight c₂ : ℤ)))
    (h₃ : T.intersection c₃ c₃ = -(2 * (T.weight c₃ : ℤ)))
    (h₄ : T.intersection c₄ c₄ = -(2 * (T.weight c₄ : ℤ)))
    (h₅ : T.intersection c₅ c₅ = -(2 * (T.weight c₅ : ℤ)))
    (h₆ : T.intersection c₆ c₆ = -(2 * (T.weight c₆ : ℤ)))
    (h₁₃ : c₁ ≠ c₃) (h₁₄ : c₁ ≠ c₄) (h₁₅ : c₁ ≠ c₅) (h₁₆ : c₁ ≠ c₆)
    (h₂₄ : c₂ ≠ c₄) (h₂₅ : c₂ ≠ c₅) (h₂₆ : c₂ ≠ c₆)
    (h₃₅ : c₃ ≠ c₅) (h₄₆ : c₄ ≠ c₆) (h₅₆ : c₅ ≠ c₆)
    (e₁₂ : 0 < T.intersection c₁ c₂) (e₂₃ : 0 < T.intersection c₂ c₃)
    (e₃₄ : 0 < T.intersection c₃ c₄) (e₄₅ : 0 < T.intersection c₄ c₅)
    (e₃₆ : 0 < T.intersection c₃ c₆) :
    ∃ w : ℕ+, (T.weight c₁ : ℤ) = w ∧ (T.weight c₂ : ℤ) = w ∧ (T.weight c₃ : ℤ) = w ∧
      (T.weight c₄ : ℤ) = w ∧ (T.weight c₅ : ℤ) = w ∧ (T.weight c₆ : ℤ) = w ∧
      T.intersection c₁ c₂ = w ∧ T.intersection c₂ c₃ = w ∧ T.intersection c₃ c₄ = w ∧
      T.intersection c₄ c₅ = w ∧ T.intersection c₃ c₆ = w ∧
      T.intersection c₁ c₃ = 0 ∧ T.intersection c₁ c₄ = 0 ∧ T.intersection c₁ c₅ = 0 ∧
      T.intersection c₁ c₆ = 0 ∧ T.intersection c₂ c₄ = 0 ∧ T.intersection c₂ c₅ = 0 ∧
      T.intersection c₂ c₆ = 0 ∧ T.intersection c₃ c₅ = 0 ∧ T.intersection c₄ c₆ = 0 ∧
      T.intersection c₅ c₆ = 0 := by
  -- The fork with stem `c₁ - c₂ - c₃` and leaves `c₄` and `c₆` fixes five of the six weights,
  -- four of the five edges, and every intersection number not involving `c₅`.
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw₆, a₁₂, a₂₃, a₃₄, a₃₆, z₁₃, z₁₄, z₁₆, z₂₄, z₂₆, z₄₆⟩ :=
    T.exists_weight_intersection_fork_five_eq (by omega) h₁ h₂ h₃ h₄ h₆
      h₁₃ h₁₄ h₁₆ h₂₄ h₂₆ h₄₆ e₁₂ e₂₃ e₃₄ e₃₆
  -- Reading the fork from the other end of the chain adds `c₅`.
  obtain ⟨w', hw₅', -, hw₃', -, -, a₅₄, -, -, -, -, -, z₅₆, -, -, -⟩ :=
    T.exists_weight_intersection_fork_five_eq (by omega) h₅ h₄ h₃ h₂ h₆
      h₃₅.symm h₂₅.symm h₅₆ h₂₄.symm h₄₆ h₂₆
      (T.intersection_comm c₄ c₅ ▸ e₄₅) (T.intersection_comm c₃ c₄ ▸ e₃₄)
      (T.intersection_comm c₂ c₃ ▸ e₂₃) e₃₆
  -- Neither end of the chain meets the other, nor the interior of the chain.
  obtain ⟨-, -, z₁₅, -, z₂₅, z₃₅⟩ :=
    T.intersection_eq_zero_of_chain_five (by omega) h₁ h₂ h₃ h₄ h₅
      h₁₃ h₁₄ h₁₅ h₂₄ h₂₅ h₃₅ e₁₂ e₂₃ e₃₄ e₄₅
  have hww : (w' : ℤ) = w := hw₃'.symm.trans hw₃
  have a₄₅ : T.intersection c₄ c₅ = w := by rw [T.intersection_comm c₄ c₅, a₅₄, hww]
  exact ⟨w, hw₁, hw₂, hw₃, hw₄, hw₅'.trans hww, hw₆, a₁₂, a₂₃, a₃₄, a₄₅, a₃₆,
    z₁₃, z₁₄, z₁₅, z₁₆, z₂₄, z₂₅, z₂₆, z₃₅, z₄₆, z₅₆⟩

/-- The free end `c₆` of the branched chain

`c₁ - c₂ - c₃ - c₄ - c₅`, with a branch `c₆` at `c₃`,

of components of self-intersection `-2w` meets no seventh component of self-intersection `-2w`,
in a numerical type with more than seven components. In particular a chain of five `(-2)`-indices
with a leg of length two at its middle component does not occur as a proper subgraph
([Stacks, Lemma 55.5.12](https://stacks.math.columbia.edu/tag/0C8I)). -/
theorem intersection_eq_zero_of_branch_six (hcard : 7 < Fintype.card T.Component)
    {c₁ c₂ c₃ c₄ c₅ c₆ c₇ : T.Component}
    (h₁ : T.intersection c₁ c₁ = -(2 * (T.weight c₁ : ℤ)))
    (h₂ : T.intersection c₂ c₂ = -(2 * (T.weight c₂ : ℤ)))
    (h₃ : T.intersection c₃ c₃ = -(2 * (T.weight c₃ : ℤ)))
    (h₄ : T.intersection c₄ c₄ = -(2 * (T.weight c₄ : ℤ)))
    (h₅ : T.intersection c₅ c₅ = -(2 * (T.weight c₅ : ℤ)))
    (h₆ : T.intersection c₆ c₆ = -(2 * (T.weight c₆ : ℤ)))
    (h₇ : T.intersection c₇ c₇ = -(2 * (T.weight c₇ : ℤ)))
    (h₁₃ : c₁ ≠ c₃) (h₁₄ : c₁ ≠ c₄) (h₁₅ : c₁ ≠ c₅) (h₁₆ : c₁ ≠ c₆) (h₁₇ : c₁ ≠ c₇)
    (h₂₄ : c₂ ≠ c₄) (h₂₅ : c₂ ≠ c₅) (h₂₆ : c₂ ≠ c₆) (h₂₇ : c₂ ≠ c₇)
    (h₃₅ : c₃ ≠ c₅) (h₃₇ : c₃ ≠ c₇) (h₄₆ : c₄ ≠ c₆) (h₄₇ : c₄ ≠ c₇)
    (h₅₆ : c₅ ≠ c₆) (h₅₇ : c₅ ≠ c₇) (h₆₇ : c₆ ≠ c₇)
    (e₁₂ : 0 < T.intersection c₁ c₂) (e₂₃ : 0 < T.intersection c₂ c₃)
    (e₃₄ : 0 < T.intersection c₃ c₄) (e₄₅ : 0 < T.intersection c₄ c₅)
    (e₃₆ : 0 < T.intersection c₃ c₆) :
    T.intersection c₆ c₇ = 0 := by
  have h₁₂ : c₁ ≠ c₂ := by rintro rfl; linarith
  have h₂₃ : c₂ ≠ c₃ := by rintro rfl; linarith
  have h₃₄ : c₃ ≠ c₄ := by rintro rfl; linarith
  have h₄₅ : c₄ ≠ c₅ := by rintro rfl; linarith
  have h₃₆ : c₃ ≠ c₆ := by rintro rfl; linarith
  by_contra hne
  have e₆₇ : 0 < T.intersection c₆ c₇ :=
    (T.offDiagonal_nonneg c₆ c₇ h₆₇).lt_of_ne (Ne.symm hne)
  -- The branched chain on `c₁, …, c₆`.
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw₅, hw₆, a₁₂, a₂₃, a₃₄, a₄₅, a₃₆,
      z₁₃, z₁₄, z₁₅, z₁₆, z₂₄, z₂₅, z₂₆, z₃₅, z₄₆, z₅₆⟩ :=
    T.exists_weight_intersection_branch_six_eq (by omega) h₁ h₂ h₃ h₄ h₅ h₆
      h₁₃ h₁₄ h₁₅ h₁₆ h₂₄ h₂₅ h₂₆ h₃₅ h₄₆ h₅₆ e₁₂ e₂₃ e₃₄ e₄₅ e₃₆
  -- The branched chain on `c₁, …, c₃, c₆, c₇` and `c₄`, obtained by exchanging the roles of the
  -- leg `c₄ - c₅` and the lengthened branch `c₆ - c₇`.
  obtain ⟨w', hw₁', -, -, -, hw₇', -, -, -, -, a₆₇, -, -, -, z₁₇, -, -, z₂₇, -, z₃₇, -, z₇₄⟩ :=
    T.exists_weight_intersection_branch_six_eq (by omega) h₁ h₂ h₃ h₆ h₇ h₄
      h₁₃ h₁₆ h₁₇ h₁₄ h₂₆ h₂₇ h₂₄ h₃₇ h₄₆.symm h₄₇.symm e₁₂ e₂₃ e₃₆ e₆₇ e₃₄
  -- The remaining pair is the two ends of the chain `c₅ - c₄ - c₃ - c₆ - c₇`.
  obtain ⟨-, -, z₅₇, -, -, -⟩ :=
    T.intersection_eq_zero_of_chain_five (by omega) h₅ h₄ h₃ h₆ h₇
      h₃₅.symm h₅₆ h₅₇ h₄₆ h₄₇ h₃₇
      (T.intersection_comm c₄ c₅ ▸ e₄₅) (T.intersection_comm c₃ c₄ ▸ e₃₄) e₃₆ e₆₇
  have hww : (w' : ℤ) = w := hw₁'.symm.trans hw₁
  have hw₇ : (T.weight c₇ : ℤ) = w := hw₇'.trans hww
  have a₆₇' : T.intersection c₆ c₇ = w := by rw [a₆₇, hww]
  have z₄₇ : T.intersection c₄ c₇ = 0 := by rw [T.intersection_comm c₄ c₇]; exact z₇₄
  -- The configuration is now the affine diagram of type `E₆` scaled by `w`. Its marks give a
  -- positive vector for which every row sum vanishes, contradicting negative definiteness.
  let c : ℕ → T.Component := fun i ↦
    if i = 0 then c₁ else if i = 1 then c₂ else if i = 2 then c₃ else if i = 3 then c₄
      else if i = 4 then c₅ else if i = 5 then c₆ else c₇
  let y : ℕ → ℤ := fun i ↦
    if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 2
      else if i = 4 then 1 else if i = 5 then 2 else 1
  refine T.not_forall_sum_intersection_mul_nonneg_of_pos (c := c) ?_ hcard (y := y) ?_
    ⟨0, by omega, by simp [y]⟩ ?_
  · intro i hi j hj hij
    interval_cases i <;> interval_cases j <;>
      simp [c, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₂₃, h₂₄, h₂₅, h₂₆, h₂₇, h₃₄,
        h₃₅, h₃₆, h₃₇, h₄₅, h₄₆, h₄₇, h₅₆, h₅₇, h₆₇, h₁₂.symm, h₁₃.symm,
        h₁₄.symm, h₁₅.symm, h₁₆.symm, h₁₇.symm, h₂₃.symm, h₂₄.symm, h₂₅.symm,
        h₂₆.symm, h₂₇.symm, h₃₄.symm, h₃₅.symm, h₃₆.symm, h₃₇.symm, h₄₅.symm,
        h₄₆.symm, h₄₇.symm, h₅₆.symm, h₅₇.symm, h₆₇.symm] at hij ⊢
  · intro i hi
    interval_cases i <;> norm_num [y]
  · intro i hi
    interval_cases i <;> norm_num [Finset.sum_range_succ, c, y] <;>
      simp only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, hw₁, hw₂, hw₃, hw₄, hw₅, hw₆, hw₇,
        T.intersection_comm c₂ c₁, T.intersection_comm c₃ c₁,
        T.intersection_comm c₃ c₂, T.intersection_comm c₄ c₁,
        T.intersection_comm c₄ c₂, T.intersection_comm c₄ c₃,
        T.intersection_comm c₅ c₁, T.intersection_comm c₅ c₂,
        T.intersection_comm c₅ c₃, T.intersection_comm c₅ c₄,
        T.intersection_comm c₆ c₁, T.intersection_comm c₆ c₂,
        T.intersection_comm c₆ c₃, T.intersection_comm c₆ c₄,
        T.intersection_comm c₆ c₅, T.intersection_comm c₇ c₁,
        T.intersection_comm c₇ c₂, T.intersection_comm c₇ c₃,
        T.intersection_comm c₇ c₄, T.intersection_comm c₇ c₅,
        T.intersection_comm c₇ c₆, a₁₂, a₂₃, a₃₄, a₄₅, a₃₆, a₆₇', z₁₃, z₁₄,
        z₁₅, z₁₆, z₁₇, z₂₄, z₂₅, z₂₆, z₂₇, z₃₅, z₃₇, z₄₆, z₄₇, z₅₆,
        z₅₇] <;>
      omega

end NumericalType

end TauCeti
