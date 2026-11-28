/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AffineBoundTightening.Optimum
public import TauCeti.Analysis.AffineBoundTightening.Examples
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checks for the joint-width optimum

The existing two-row recurrence has a unique zero-width optimum. With no rows, two
incomparable smaller boxes have width one while their common greatest feasible box has
width two. The zero-coordinate case retains a nonempty public state and a unique complete
assignment. Finally two assignments have equal maximal variable width but different joint
width, so the full-assignment conclusion uses both variable and row widths.

These are finite controls for the qualified joint construction of Belotti, Cafieri, Lee and
Liberti, *Feasibility-Based Bounds Tightening via Fixed Points*, COCOA 2010, §4, pp. 71–73.
-/

public section

open scoped BigOperators
open Set

namespace TauCeti.AffineBoundTightening.Examples

noncomputable section

/-- The positive two-row recurrence has the canonical all-zero singleton as its unique entire
LP maximizer, with joint objective zero, although no finite iterate reaches the singleton. -/
theorem twoRow_unique_optimum {a : ℝ} (ha : 1 < a) :
    IsFeasible (twoRowMatrix a) (twoRowBox 1) (canonical (twoRowMatrix a) (twoRowBox 0)) ∧
    objective (canonical (twoRowMatrix a) (twoRowBox 0)) = 0 ∧
    IsMaxOn objective (feasibleSet (twoRowMatrix a) (twoRowBox 1))
      (canonical (twoRowMatrix a) (twoRowBox 0)) ∧
    (∀ p, IsFeasible (twoRowMatrix a) (twoRowBox 1) p →
      IsMaxOn objective (feasibleSet (twoRowMatrix a) (twoRowBox 1)) p →
      p = canonical (twoRowMatrix a) (twoRowBox 0)) ∧
    (∀ k, rawRun (twoRowMatrix a) (twoRowBox 1) k ≠ twoRowBox 0) := by
  obtain ⟨hrun, hlim, _, _, hfinite⟩ := twoRow_endpointLimit ha
  obtain ⟨hfeas, hmax, huniq⟩ := unique_full_width_optimum (twoRowMatrix a) (twoRowBox 1) hrun
  rw [hlim] at hfeas hmax huniq
  exact ⟨hfeas, by simp [objective_canonical, width_twoRowBox], hmax, huniq, hfinite⟩

/-- With no rows, the incomparable feasible boxes `[0, 1]` and `[1, 2]` both have width one,
strictly below the unique entire optimum `[0, 2]` of width two. -/
theorem zero_rows_unique_optimum (A : Matrix (Fin 0) (Fin 1) ℝ) :
    let q₀ : Raw 1 0 := (fun _ => 0, fun _ => 2)
    let q₁ : Raw 1 0 := (fun _ => 0, fun _ => 1)
    let q₂ : Raw 1 0 := (fun _ => 1, fun _ => 2)
    (IsFeasible A q₀ (canonical A q₁) ∧ objective (canonical A q₁) = 1) ∧
    (IsFeasible A q₀ (canonical A q₂) ∧ objective (canonical A q₂) = 1) ∧
    (¬ Within q₁ q₂ ∧ ¬ Within q₂ q₁) ∧
    (IsFeasible A q₀ (canonical A q₀) ∧ objective (canonical A q₀) = 2) ∧
    IsMaxOn objective (feasibleSet A q₀) (canonical A q₀) ∧
    (∀ p, IsFeasible A q₀ p → IsMaxOn objective (feasibleSet A q₀) p →
      p = canonical A q₀) := by
  intro q₀ q₁ q₂
  obtain ⟨h1, h2, h0, _, _⟩ := zero_rows_feasible_assignments A
  have hord : q₀.1 ≤ q₀.2 := fun _ => by norm_num [q₀]
  have hfix := (isFixedPt_step_zero_rows_iff A q₀ q₀).mpr Within.rfl
  have hrun := coe_publicRun_nonempty_of_isFixedPt_step hord hfix
  have hlim := endpointLimit_eq_self_of_isFixedPt hfix
  obtain ⟨_, hmax, huniq⟩ := unique_full_width_optimum A q₀ hrun
  rw [hlim] at hmax huniq
  refine ⟨h1, h2, ⟨?_, ?_⟩, h0, hmax, huniq⟩
  · intro hw
    have hh := hw.fst_le (.inl 0)
    norm_num [q₁, q₂] at hh
  · intro hw
    have hh := hw.le_snd (.inl 0)
    norm_num [q₁, q₂] at hh

/-- With no variables and no rows, every public iterate is nonempty and the canonical limit
assignment has objective zero; every feasible full assignment equals it. -/
theorem empty_dim_unique_optimum (A : Matrix (Fin 0) (Fin 0) ℝ) (q₀ : Raw 0 0) :
    (∀ k, (publicRun A q₀ k : Set (Coord 0 0 → ℝ)).Nonempty) ∧
    IsFeasible A q₀ (canonical A (endpointLimit A q₀)) ∧
    objective (canonical A (endpointLimit A q₀)) = 0 ∧
    IsMaxOn objective (feasibleSet A q₀) (canonical A (endpointLimit A q₀)) ∧
    (∀ p, IsFeasible A q₀ p → p = canonical A (endpointLimit A q₀)) := by
  have hord : q₀.1 ≤ q₀.2 := fun c => c.elim Fin.elim0 Fin.elim0
  have hfix := (isFixedPt_step_zero_rows_iff A q₀ q₀).mpr Within.rfl
  have hrun := coe_publicRun_nonempty_of_isFixedPt_step hord hfix
  obtain ⟨hfeas, hmax, _⟩ := unique_full_width_optimum A q₀ hrun
  refine ⟨hrun, hfeas, by simp [objective_eq_sum_add_sum], hmax, ?_⟩
  intro p hp
  rw [hp.eq_canonical, Subsingleton.elim p.endpoints (endpointLimit A q₀)]

/-- A row summing two variable coordinates, used to distinguish joint and variable-only width. -/
def widthComparisonMatrix : Matrix (Fin 1) (Fin 2) ℝ := fun _ _ => 1

/-- The fixed initial variable box `[0, 1]²` and row interval `[0, 2]`. -/
def widthComparisonInitial : Raw 2 1 :=
  (fun _ => 0, Sum.elim (fun _ => 1) (fun _ => 2))

/-- The same variable box with the smaller row interval `[1/2, 3/2]`. -/
def widthComparisonSmaller : Raw 2 1 :=
  (Sum.elim (fun _ => 0) (fun _ => 1 / 2), Sum.elim (fun _ => 1) (fun _ => 3 / 2))

/-- Variable width alone, deliberately omitting the row width from the joint objective. -/
def variableWidth (p : Assignment 2 1) : ℝ :=
  ∑ j : Fin 2, (p.endpoints.2 (.inl j) - p.endpoints.1 (.inl j))

private theorem widthComparison_feasible (q : Raw 2 1)
    (hq : q = widthComparisonInitial ∨ q = widthComparisonSmaller) :
    IsFeasible widthComparisonMatrix widthComparisonInitial
      (canonical widthComparisonMatrix q) := by
  have hzLo (r : Raw 2 1) (i : Fin 1) (j : Fin 2) :
      zLo widthComparisonMatrix r i j = r.1 (.inl j) := by
    rw [zLo_of_nonneg (A := widthComparisonMatrix) (q := r) (i := i) (j := j)
      (by norm_num [widthComparisonMatrix])]
    norm_num [widthComparisonMatrix]
  have hzHi (r : Raw 2 1) (i : Fin 1) (j : Fin 2) :
      zHi widthComparisonMatrix r i j = r.2 (.inl j) := by
    rw [zHi_of_nonneg (A := widthComparisonMatrix) (q := r) (i := i) (j := j)
      (by norm_num [widthComparisonMatrix])]
    norm_num [widthComparisonMatrix]
  rcases hq with rfl | rfl <;>
    refine
      { fst_le_snd := ?_
        within := ?_
        zL_eq := fun _ _ => by simp only [canonical_zL, canonical_endpoints]
        zU_eq := fun _ _ => by simp only [canonical_zU, canonical_endpoints]
        sum_zL_le := ?_
        le_sum_zU := ?_
        div_le_of_pos := ?_
        le_div_of_pos := ?_
        div_le_of_neg := ?_
        le_div_of_neg := ?_ }
  all_goals simp only [canonical_endpoints, canonical_zL, canonical_zU, hzLo, hzHi]
  all_goals
    solve
    | exact within_iff.mpr ⟨fun c => by cases c <;> norm_num [widthComparisonInitial,
        widthComparisonSmaller], fun c => by cases c <;> norm_num [widthComparisonInitial,
        widthComparisonSmaller]⟩
    | intro c; cases c <;> norm_num [widthComparisonInitial, widthComparisonSmaller]
    | intro i; norm_num [widthComparisonInitial, widthComparisonSmaller, Fin.sum_univ_two]
    | intro i j h; fin_cases j <;> norm_num [widthComparisonMatrix,
        widthComparisonInitial, widthComparisonSmaller,
        show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl] at *

/-- The two feasible width-comparison assignments have joint widths four and three but equal
variable width two, which is an upper bound for every feasible assignment. -/
theorem joint_and_variable_widths :
    IsFeasible widthComparisonMatrix widthComparisonInitial
      (canonical widthComparisonMatrix widthComparisonInitial) ∧
    IsFeasible widthComparisonMatrix widthComparisonInitial
      (canonical widthComparisonMatrix widthComparisonSmaller) ∧
    objective (canonical widthComparisonMatrix widthComparisonInitial) = 4 ∧
    objective (canonical widthComparisonMatrix widthComparisonSmaller) = 3 ∧
    variableWidth (canonical widthComparisonMatrix widthComparisonInitial) = 2 ∧
    variableWidth (canonical widthComparisonMatrix widthComparisonSmaller) = 2 ∧
    (∀ p, IsFeasible widthComparisonMatrix widthComparisonInitial p → variableWidth p ≤ 2) := by
  refine ⟨widthComparison_feasible _ (Or.inl rfl), widthComparison_feasible _ (Or.inr rfl),
    by norm_num [objective_eq_sum_add_sum, widthComparisonInitial],
    by norm_num [objective_eq_sum_add_sum, widthComparisonSmaller],
    by norm_num [variableWidth, widthComparisonInitial],
    by norm_num [variableWidth, widthComparisonSmaller], ?_⟩
  intro p hp
  have hl0 := hp.within.fst_le (.inl 0)
  have hl1 := hp.within.fst_le (.inl 1)
  have hu0 := hp.within.le_snd (.inl 0)
  have hu1 := hp.within.le_snd (.inl 1)
  simp only [widthComparisonInitial, Sum.elim_inl] at hl0 hl1 hu0 hu1
  simp only [variableWidth, Fin.sum_univ_two]
  linarith

/-- Both distinct width-comparison assignments are feasible and maximize variable width.
Only the wider row assignment maximizes joint width and equals the actual canonical
endpoint limit. -/
theorem variable_only_maximizers_distinct :
    let A := widthComparisonMatrix
    let q₀ := widthComparisonInitial
    let q₁ := widthComparisonSmaller
    IsFeasible A q₀ (canonical A q₀) ∧
    IsFeasible A q₀ (canonical A q₁) ∧
    IsMaxOn variableWidth (feasibleSet A q₀) (canonical A q₀) ∧
    IsMaxOn variableWidth (feasibleSet A q₀) (canonical A q₁) ∧
    canonical A q₀ ≠ canonical A q₁ ∧
    endpointLimit A q₀ = q₀ ∧
    IsMaxOn objective (feasibleSet A q₀) (canonical A q₀) ∧
    ¬ IsMaxOn objective (feasibleSet A q₀) (canonical A q₁) := by
  intro A q₀ q₁
  obtain ⟨hf0, hf1, hw0, hw1, hv0, hv1, hbound⟩ := joint_and_variable_widths
  have hfix := (isFeasible_canonical_iff.mp hf0).2
  have hord := (isFeasible_canonical_iff.mp hf0).1
  have hlim := endpointLimit_eq_self_of_isFixedPt hfix
  have hrun := coe_publicRun_nonempty_of_isFixedPt_step hord hfix
  have hmax := (unique_full_width_optimum A q₀ hrun).2.1
  rw [hlim] at hmax
  refine ⟨hf0, hf1, isMaxOn_iff.mpr (fun p hp => ?_),
    isMaxOn_iff.mpr (fun p hp => ?_), ?_, hlim, hmax, ?_⟩
  · rw [hv0]
    exact hbound p (mem_feasibleSet.mp hp)
  · rw [hv1]
    exact hbound p (mem_feasibleSet.mp hp)
  · intro he
    have hew := congrArg objective he
    rw [hw0, hw1] at hew
    norm_num at hew
  · intro hsmall
    have hh := (isMaxOn_iff.mp hsmall) _ (mem_feasibleSet.mpr hf0)
    rw [hw0, hw1] at hh
    norm_num at hh

end

end TauCeti.AffineBoundTightening.Examples
