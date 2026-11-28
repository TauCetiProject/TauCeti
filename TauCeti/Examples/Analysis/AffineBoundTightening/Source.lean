/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.AffineBoundTightening.Examples
public import TauCeti.Analysis.AffineBoundTightening.Source
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Checks for bounded original-coordinate bound tightening

These checks cover initialization with an inconsistent affine row, empty coordinate
families, signed and zero coefficients, and a bounded original model with effective
nonlinear and integer restrictions. The model minimizes `(x₀ - 1)² + x₁²` subject to
`x₀ + x₁ ≤ 2`, `1 ≤ x₀² + x₁²`, and integer `x₀`, with initial bounds `[0, 2]²`.
The point `(1, 0)` attains objective value zero and remains a minimizer at the actual
endpoint limit. No LP feasibility result is used by these preservation checks, and no general
attainment assertion is made.
-/

public section

open scoped BigOperators
open Set

namespace TauCeti.AffineBoundTightening.SourceExamples

noncomputable section

/-- The affine row `x₀ + x₁`. -/
def sumMatrix : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1]

/-- The initial joint box for `x₀ + x₁ ≤ 2` on `[0, 2]²`. -/
def initial : Raw 2 1 := sourceInitial sumMatrix ![2] ![0, 0] ![2, 2]

/-- The nonlinear restriction `1 ≤ x₀² + x₁²`. -/
def nonlinearRestriction : Set (Fin 2 → ℝ) := {x | 1 ≤ x 0 ^ 2 + x 1 ^ 2}

/-- The original model retains the nonlinear restriction and integrality of `x₀`. -/
def feasible : Set (Fin 2 → ℝ) := sourceSet sumMatrix ![2] nonlinearRestriction {0}

/-- The unchanged original objective has a zero-value minimizer at `(1, 0)`. -/
def objective (x : Fin 2 → ℝ) : ℝ := (x 0 - 1) ^ 2 + x 1 ^ 2

/-- The row interval for `x₀ + x₁ ≤ 2` on `[0, 2]²` initializes to `[0, 2]`. -/
theorem initial_row : initial.1 (.inr 0) = 0 ∧ initial.2 (.inr 0) = 2 := by
  constructor
  · simp only [initial, sourceInitial_fst_inr, imageLo_def, Fin.sum_univ_two]
    rw [zLo_of_nonneg (A := sumMatrix) (i := 0) (j := 0) (by norm_num [sumMatrix]),
      zLo_of_nonneg (A := sumMatrix) (i := 0) (j := 1) (by norm_num [sumMatrix])]
    norm_num [sumMatrix]
  · simp [initial]

/-- Initialization can be ordered while no affine graph point is enclosed. -/
theorem ordered_initial_without_graph :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![1]
    let q := sourceInitial A ![0] ![1] ![1]
    q.1 ≤ q.2 ∧ q.1 (.inr 0) = 0 ∧ q.2 (.inr 0) = 0 ∧
      ¬ ∃ x, graph A x ∈ Icc q.1 q.2 := by
  intro A q
  have hlo : q.1 (.inr 0) = 0 := by
    simp only [q, sourceInitial_fst_inr, imageLo_def, Fin.sum_univ_one]
    rw [zLo_of_nonneg (A := A) (i := 0) (j := 0) (by norm_num [A])]
    norm_num [A]
  refine ⟨sourceInitial_fst_le_snd A ![0] le_rfl, hlo,
    by simp [q], ?_⟩
  rintro ⟨x, hx⟩
  have hx' := mem_Icc_sourceInitial_graph_iff.mp hx
  have hl := hx'.1.1 0
  have hr := hx'.2 0
  norm_num [A, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ] at hl hr
  linarith

/-- With no affine rows, graph membership in the initialization is just variable-box membership. -/
theorem no_rows_initial_graph_iff {n : ℕ} (A : Matrix (Fin 0) (Fin n) ℝ)
    (r : Fin 0 → ℝ) (l u x : Fin n → ℝ) :
    graph A x ∈ Icc (sourceInitial A r l u).1 (sourceInitial A r l u).2 ↔ x ∈ Icc l u := by
  constructor
  · intro hx
    exact (mem_Icc_sourceInitial_graph_iff.mp hx).1
  · intro hx
    exact mem_Icc_sourceInitial_graph_iff.mpr ⟨hx, fun i => Fin.elim0 i⟩

/-- Removing affine rows leaves the extra restriction and integrality condition intact. -/
theorem no_rows_sourceSet_iff {n : ℕ} (A : Matrix (Fin 0) (Fin n) ℝ)
    (r : Fin 0 → ℝ) (extra : Set (Fin n → ℝ)) (integers : Finset (Fin n)) (x : Fin n → ℝ) :
    x ∈ sourceSet A r extra integers ↔
      x ∈ extra ∧ ∀ j ∈ integers, ∃ z : ℤ, x j = (z : ℝ) := by
  rw [mem_sourceSet]
  constructor
  · intro hx
    exact ⟨hx.2.1, hx.2.2⟩
  · rintro ⟨he, hi⟩
    exact ⟨fun i => Fin.elim0 i, he, hi⟩

/-- With no variables, initialization is ordered and its enclosed graph condition is `0 ≤ r`. -/
theorem no_variables_initial {m : ℕ} (A : Matrix (Fin m) (Fin 0) ℝ)
    (r : Fin m → ℝ) (l u x : Fin 0 → ℝ) :
    (sourceInitial A r l u).1 ≤ (sourceInitial A r l u).2 ∧
      (graph A x ∈ Icc (sourceInitial A r l u).1 (sourceInitial A r l u).2 ↔
        ∀ i, 0 ≤ r i) := by
  refine ⟨sourceInitial_fst_le_snd A r (fun j => Fin.elim0 j), ?_⟩
  rw [mem_Icc_sourceInitial_graph_iff]
  simp [mem_Icc, Pi.le_def]

/-- At zero variables and rows the initialized graph survives every actual public iterate. -/
theorem zero_dimensions (A : Matrix (Fin 0) (Fin 0) ℝ) (r : Fin 0 → ℝ)
    (l u x : Fin 0 → ℝ) :
    (∀ k, (publicRun A (sourceInitial A r l u) k : Set (Coord 0 0 → ℝ)).Nonempty) ∧
      variableBox (endpointLimit A (sourceInitial A r l u)) = univ := by
  have hg : graph A x ∈ Icc (sourceInitial A r l u).1 (sourceInitial A r l u).2 :=
    mem_Icc_sourceInitial_graph_iff.mpr
      ⟨⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩, fun i => Fin.elim0 i⟩
  refine ⟨coe_publicRun_nonempty_of_graph hg, ?_⟩
  apply Set.eq_univ_of_forall
  intro _
  exact mem_variableBox.mpr fun j => Fin.elim0 j

/-- Negative and zero coefficients and a negative row cap retain their signed initialization. -/
theorem signed_initialization :
    let A : Matrix (Fin 1) (Fin 2) ℝ := !![-2, 0]
    let q := sourceInitial A ![-1] ![1, 2] ![3, 4]
    q.1 (.inr 0) = -6 ∧ q.2 (.inr 0) = -1 ∧ graph A ![1, 2] ∈ Icc q.1 q.2 := by
  intro A q
  have hlo : q.1 (.inr 0) = -6 := by
    simp only [q, sourceInitial_fst_inr, imageLo_def, Fin.sum_univ_two]
    rw [zLo_of_nonpos (A := A) (i := 0) (j := 0) (by norm_num [A]),
      zLo_of_zero (A := A) (i := 0) (j := 1) (by norm_num [A])]
    norm_num [A]
  refine ⟨hlo, by simp [q], ?_⟩
  apply mem_Icc_sourceInitial_graph_iff.mpr
  constructor
  · constructor <;> intro j <;> fin_cases j <;> norm_num
  · intro i
    fin_cases i
    norm_num [A, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ]

/-- An empty extra set makes the original feasible set empty, with any affine or integer data. -/
theorem empty_extra {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (integers : Finset (Fin n)) : sourceSet A r ∅ integers = ∅ := by
  ext x
  simp

/-- With no designated integer coordinates the affine and extra restrictions still remain. -/
theorem empty_integers {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (extra : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    x ∈ sourceSet A r extra ∅ ↔ A.mulVec x ≤ r ∧ x ∈ extra := by
  simp

/-- The point `(1, 0)` satisfies every original restriction. -/
theorem optimum_feasible : ![1, 0] ∈ feasible := by
  unfold feasible
  rw [mem_sourceSet]
  refine ⟨?_, by norm_num [nonlinearRestriction], ?_⟩
  · intro i
    fin_cases i
    norm_num [sumMatrix, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ]
  · intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst j
    exact ⟨1, by norm_num⟩

/-- The point `(1, 0)` lies in the initial variable box. -/
theorem optimum_in_initial_box : ![1, 0] ∈ Icc (![0, 0] : Fin 2 → ℝ) ![2, 2] := by
  constructor <;> intro j <;> fin_cases j <;> norm_num

/-- A concrete feasible graph point proves nonemptiness of all actual public iterates. -/
theorem original_nonempty_run (k : ℕ) :
    (publicRun sumMatrix initial k : Set (Coord 2 1 → ℝ)).Nonempty := by
  apply coe_publicRun_nonempty_of_graph (x := ![1, 0])
  exact mem_Icc_sourceInitial_graph_iff.mpr
    ⟨optimum_in_initial_box, (mem_sourceSet.mp optimum_feasible).1⟩

/-- The original objective is nonnegative at every point, independently of feasibility. -/
theorem objective_nonneg (x : Fin 2 → ℝ) : 0 ≤ objective x := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- `(1, 0)` attains value zero for the original model, before and after the actual limit. -/
theorem attained_minimizer_preserved :
    (![1, 0] ∈ feasible ∩ Icc (![0, 0] : Fin 2 → ℝ) ![2, 2] ∧
      IsMinOn objective (feasible ∩ Icc ![0, 0] ![2, 2]) ![1, 0]) ∧
    (![1, 0] ∈ feasible ∩ variableBox (endpointLimit sumMatrix initial) ∧
      IsMinOn objective (feasible ∩ variableBox (endpointLimit sumMatrix initial)) ![1, 0]) ∧
    objective ![1, 0] = 0 := by
  have hz : objective ![1, 0] = 0 := by norm_num [objective]
  have hi : ![1, 0] ∈ feasible ∩ Icc (![0, 0] : Fin 2 → ℝ) ![2, 2] ∧
      IsMinOn objective (feasible ∩ Icc ![0, 0] ![2, 2]) ![1, 0] := by
    refine ⟨⟨optimum_feasible, optimum_in_initial_box⟩, ?_⟩
    intro y _
    rw [hz]
    exact objective_nonneg y
  have hp := source_preservation sumMatrix ![2] ![0, 0] ![2, 2]
    nonlinearRestriction {0} objective original_nonempty_run
  exact ⟨hi, (hp.2.2.2 ![1, 0]).mpr hi, hz⟩

/-- `(0, 0)` passes the affine, box and integer restrictions but fails the nonlinear restriction. -/
theorem nonlinear_restriction_effective :
    ![0, 0] ∈ sourceSet sumMatrix ![2] univ {0} ∩
      Icc (![0, 0] : Fin 2 → ℝ) ![2, 2] ∧ ![0, 0] ∉ nonlinearRestriction := by
  refine ⟨⟨?_, ?_⟩, by norm_num [nonlinearRestriction]⟩
  · rw [mem_sourceSet]
    refine ⟨?_, mem_univ _, ?_⟩
    · intro i
      fin_cases i
      norm_num [sumMatrix, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ]
    · intro j _
      exact ⟨0, by fin_cases j <;> norm_num⟩
  · constructor <;> intro j <;> fin_cases j <;> norm_num

/-- `(1/2, 1)` passes the affine, box and nonlinear restrictions but fails integrality of `x₀`. -/
theorem integrality_effective :
    ![(1 / 2 : ℝ), 1] ∈ sourceSet sumMatrix ![2] nonlinearRestriction ∅ ∩
      Icc (![0, 0] : Fin 2 → ℝ) ![2, 2] ∧ ![(1 / 2 : ℝ), 1] ∉ feasible := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_sourceSet]
    refine ⟨?_, by norm_num [nonlinearRestriction], by simp⟩
    intro i
    fin_cases i
    norm_num [sumMatrix, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_succ]
  · constructor <;> intro j <;> fin_cases j <;> norm_num
  · intro hx
    obtain ⟨z, hz⟩ := (mem_sourceSet.mp hx).2.2 0 (by simp)
    have hz0 : (0 : ℝ) < (z : ℝ) := by norm_num at hz; linarith
    have hz1 : (z : ℝ) < 1 := by norm_num at hz; linarith
    have hz0' : (0 : ℤ) < z := by exact_mod_cast hz0
    have hz1' : z < (0 : ℤ) + 1 := by exact_mod_cast hz1
    exact (not_le_of_gt hz0') (Int.lt_add_one_iff.mp hz1')

end

end TauCeti.AffineBoundTightening.SourceExamples

/-!
# One-way source infeasibility controls

The unit row with variable singleton one and cap zero has an infeasible scalar LP.
An empty extra set can instead give an empty original set with a feasible scalar LP.
Finally both directions of each native four-row equality give eight actual inequalities:
their scalar program is feasible and every public iterate is nonempty, but their original
bounded affine set is empty. Extra and integer restrictions remain unchanged throughout.
-/

public section

open scoped BigOperators
open Set

namespace TauCeti.AffineBoundTightening.SourceInfeasibilityExamples

noncomputable section

/-- The row `x ≤ 0` with `x = 1` has an infeasible scalar LP and an empty bounded source set,
independently of additional or designated-integer restrictions. -/
theorem unit_row_infeasible (extra : Set (Fin 1 → ℝ)) (integers : Finset (Fin 1)) :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![1]
    let q := sourceInitial A ![0] ![1] ![1]
    (¬ ∃ p, IsFeasible A q p) ∧ sourceSet A ![0] extra integers ∩ Icc ![1] ![1] = ∅ := by
  intro A q
  have hnone : ¬ ∃ p, IsFeasible A q p := by
    rintro ⟨p, hp⟩
    have hx : 1 ≤ p.endpoints.1 (.inl 0) := by
      simpa [q] using hp.within.fst_le (.inl 0)
    have hb : p.endpoints.1 (.inr 0) ≤ 0 := by
      simpa [q] using (hp.fst_le_snd (.inr 0)).trans (hp.within.le_snd (.inr 0))
    have hz : p.zL 0 0 = p.endpoints.1 (.inl 0) := by
      rw [hp.zL_eq 0 0, zLo_of_nonneg (A := A) (by norm_num [A])]
      norm_num [A]
    have hs := hp.sum_zL_le 0
    simp only [Fin.sum_univ_one, hz] at hs
    linarith
  exact ⟨hnone, source_infeasible A ![0] ![1] ![1] extra integers hnone⟩

/-- Empty extra restrictions can make the source empty while the zero graph still supplies
an actual feasible scalar singleton, with any designated integer coordinates. -/
theorem empty_extra_feasible_lp (integers : Finset (Fin 1)) :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 0
    let q := sourceInitial A ![0] ![0] ![0]
    IsFeasible A q (graphAssignment A ![0]) ∧
      sourceSet A ![0] ∅ integers ∩ Icc ![0] ![0] = ∅ := by
  intro A q
  constructor
  · apply isFeasible_graphAssignment
    apply mem_Icc_sourceInitial_graph_iff.mpr
    refine ⟨⟨le_rfl, le_rfl⟩, ?_⟩
    intro i
    norm_num [A, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_one]
  · rw [SourceExamples.empty_extra]
    simp

/-- Native four-row lower variable endpoints, namely `(-1,-1,-1)`. -/
def equalityLower : Fin 3 → ℝ := fun j => Examples.fourRowBox.1 (.inl j)

/-- Native four-row upper variable endpoints, namely `(1,1,1)`. -/
def equalityUpper : Fin 3 → ℝ := fun j => Examples.fourRowBox.2 (.inl j)

/-- Both actual inequality directions of each of the native four equalities. The first four
rows are the native matrix; the last four are their negatives. -/
def equalityRows : Matrix (Fin 8) (Fin 3) ℝ :=
  fun k => Fin.addCases (m := 4) (n := 4) (motive := fun _ => Fin 3 → ℝ)
    (fun i => Examples.fourRowMatrix i) (fun i j => -Examples.fourRowMatrix i j) k

/-- Caps for both inequality directions: the native upper row endpoints, then the negatives
of the lower endpoints, giving `(0,0,0,1,0,0,0,-1)`. -/
def equalityCaps : Fin 8 → ℝ :=
  fun k => Fin.addCases (m := 4) (n := 4) (motive := fun _ => ℝ)
    (fun i => Examples.fourRowBox.2 (.inr i)) (fun i => -Examples.fourRowBox.1 (.inr i)) k

/-- Copy the native fixed box to the positive rows and reflect its intervals on the negative
rows. Its variable box is unchanged. -/
def equalityBox : Raw 3 8 :=
  (Sum.elim equalityLower (fun k => Fin.addCases (m := 4) (n := 4) (motive := fun _ => ℝ)
    (fun i => Examples.fourRowBox.1 (.inr i)) (fun i => -Examples.fourRowBox.2 (.inr i)) k),
   Sum.elim equalityUpper (fun k => Fin.addCases (m := 4) (n := 4) (motive := fun _ => ℝ)
    (fun i => Examples.fourRowBox.2 (.inr i)) (fun i => -Examples.fourRowBox.1 (.inr i)) k))

/-- Actual source initialization of the eight inequalities on the native variable box. -/
def equalityInitial : Raw 3 8 :=
  sourceInitial equalityRows equalityCaps equalityLower equalityUpper

private theorem positive_products (q : Raw 3 8)
    (hl : ∀ j, q.1 (.inl j) = equalityLower j)
    (hu : ∀ j, q.2 (.inl j) = equalityUpper j) (i : Fin 4) (j : Fin 3) :
    zLo equalityRows q (i.castAdd 4) j = zLo Examples.fourRowMatrix Examples.fourRowBox i j ∧
    zHi equalityRows q (i.castAdd 4) j = zHi Examples.fourRowMatrix Examples.fourRowBox i j := by
  by_cases ha : 0 ≤ Examples.fourRowMatrix i j
  · have he : 0 ≤ equalityRows (i.castAdd 4) j := by simpa [equalityRows] using ha
    constructor
    · rw [zLo_of_nonneg he, zLo_of_nonneg ha, hl]
      simp only [equalityRows, Fin.addCases_left, equalityLower]
    · rw [zHi_of_nonneg he, zHi_of_nonneg ha, hu]
      simp only [equalityRows, Fin.addCases_left, equalityUpper]
  · have hn := le_of_not_ge ha
    have he : equalityRows (i.castAdd 4) j ≤ 0 := by simpa [equalityRows] using hn
    constructor
    · rw [zLo_of_nonpos he, zLo_of_nonpos hn, hu]
      simp only [equalityRows, Fin.addCases_left, equalityUpper]
    · rw [zHi_of_nonpos he, zHi_of_nonpos hn, hl]
      simp only [equalityRows, Fin.addCases_left, equalityLower]

private theorem negative_products (q : Raw 3 8)
    (hl : ∀ j, q.1 (.inl j) = equalityLower j)
    (hu : ∀ j, q.2 (.inl j) = equalityUpper j) (i : Fin 4) (j : Fin 3) :
    zLo equalityRows q (Fin.natAdd 4 i) j = -zHi Examples.fourRowMatrix Examples.fourRowBox i j ∧
    zHi equalityRows q (Fin.natAdd 4 i) j =
      -zLo Examples.fourRowMatrix Examples.fourRowBox i j := by
  have hcoef : equalityRows (Fin.natAdd 4 i) j = -Examples.fourRowMatrix i j := by
    simp only [equalityRows, Fin.addCases_right]
  by_cases ha : 0 ≤ Examples.fourRowMatrix i j
  · have he : equalityRows (Fin.natAdd 4 i) j ≤ 0 := by
      rw [hcoef]
      exact neg_nonpos.mpr ha
    constructor
    · rw [zLo_of_nonpos he, zHi_of_nonneg ha, hu]
      simp only [equalityRows, Fin.addCases_right, equalityUpper, neg_mul]
    · rw [zHi_of_nonpos he, zLo_of_nonneg ha, hl]
      simp only [equalityRows, Fin.addCases_right, equalityLower, neg_mul]
  · have hn := le_of_not_ge ha
    have he : 0 ≤ equalityRows (Fin.natAdd 4 i) j := by
      rw [hcoef]
      exact neg_nonneg.mpr hn
    constructor
    · rw [zLo_of_nonneg he, zHi_of_nonpos hn, hl]
      simp only [equalityRows, Fin.addCases_right, equalityLower, neg_mul]
    · rw [zHi_of_nonneg he, zLo_of_nonpos hn, hu]
      simp only [equalityRows, Fin.addCases_right, equalityUpper, neg_mul]

private theorem row_images (q : Raw 3 8)
    (hl : ∀ j, q.1 (.inl j) = equalityLower j)
    (hu : ∀ j, q.2 (.inl j) = equalityUpper j) (i : Fin 4) :
    imageLo equalityRows q (i.castAdd 4) = imageLo Examples.fourRowMatrix Examples.fourRowBox i ∧
    imageHi equalityRows q (i.castAdd 4) = imageHi Examples.fourRowMatrix Examples.fourRowBox i ∧
    imageLo equalityRows q (Fin.natAdd 4 i) =
      -imageHi Examples.fourRowMatrix Examples.fourRowBox i ∧
    imageHi equalityRows q (Fin.natAdd 4 i) =
      -imageLo Examples.fourRowMatrix Examples.fourRowBox i := by
  have hpL j := (positive_products q hl hu i j).1
  have hpU j := (positive_products q hl hu i j).2
  have hnL j := (negative_products q hl hu i j).1
  have hnU j := (negative_products q hl hu i j).2
  simp only [imageLo_def, imageHi_def, hpL, hpU, hnL, hnU, Finset.sum_neg_distrib, and_self]

private theorem row_rests (i : Fin 4) (j : Fin 3) :
    restLo equalityRows equalityBox (i.castAdd 4) j =
      restLo Examples.fourRowMatrix Examples.fourRowBox i j ∧
    restHi equalityRows equalityBox (i.castAdd 4) j =
      restHi Examples.fourRowMatrix Examples.fourRowBox i j ∧
    restLo equalityRows equalityBox (Fin.natAdd 4 i) j =
      -restHi Examples.fourRowMatrix Examples.fourRowBox i j ∧
    restHi equalityRows equalityBox (Fin.natAdd 4 i) j =
      -restLo Examples.fourRowMatrix Examples.fourRowBox i j := by
  have hpL k := (positive_products equalityBox (fun _ => rfl) (fun _ => rfl) i k).1
  have hpU k := (positive_products equalityBox (fun _ => rfl) (fun _ => rfl) i k).2
  have hnL k := (negative_products equalityBox (fun _ => rfl) (fun _ => rfl) i k).1
  have hnU k := (negative_products equalityBox (fun _ => rfl) (fun _ => rfl) i k).2
  simp only [restLo_def, restHi_def, hpL, hpU, hnL, hnU, Finset.sum_neg_distrib, and_self]

private theorem positive_inverses (i : Fin 4) (j : Fin 3) :
    inverseLo equalityRows equalityBox (i.castAdd 4) j =
      inverseLo Examples.fourRowMatrix Examples.fourRowBox i j ∧
    inverseHi equalityRows equalityBox (i.castAdd 4) j =
      inverseHi Examples.fourRowMatrix Examples.fourRowBox i j := by
  obtain ⟨hl, hu, _, _⟩ := row_rests i j
  have hcoef : equalityRows (i.castAdd 4) j = Examples.fourRowMatrix i j := by
    simp only [equalityRows, Fin.addCases_left]
  have hrL : equalityBox.1 (.inr (i.castAdd 4)) = Examples.fourRowBox.1 (.inr i) := by
    simp only [equalityBox, Sum.elim_inr, Fin.addCases_left]
  have hrU : equalityBox.2 (.inr (i.castAdd 4)) = Examples.fourRowBox.2 (.inr i) := by
    simp only [equalityBox, Sum.elim_inr, Fin.addCases_left]
  have hvL : equalityBox.1 (.inl j) = Examples.fourRowBox.1 (.inl j) := by
    simp only [equalityBox, Sum.elim_inl, equalityLower]
  have hvU : equalityBox.2 (.inl j) = Examples.fourRowBox.2 (.inl j) := by
    simp only [equalityBox, Sum.elim_inl, equalityUpper]
  rcases lt_trichotomy (Examples.fourRowMatrix i j) 0 with ha | ha | ha
  · have he : equalityRows (i.castAdd 4) j < 0 := by rw [hcoef]; exact ha
    constructor
    · rw [inverseLo_of_neg he, inverseLo_of_neg ha, hl, hrU, hcoef]
    · rw [inverseHi_of_neg he, inverseHi_of_neg ha, hu, hrL, hcoef]
  · have he : equalityRows (i.castAdd 4) j = 0 := hcoef.trans ha
    constructor
    · exact (inverseLo_of_zero he).trans (hvL.trans (inverseLo_of_zero ha).symm)
    · exact (inverseHi_of_zero he).trans (hvU.trans (inverseHi_of_zero ha).symm)
  · have he : 0 < equalityRows (i.castAdd 4) j := by rw [hcoef]; exact ha
    constructor
    · rw [inverseLo_of_pos he, inverseLo_of_pos ha, hu, hrL, hcoef]
    · rw [inverseHi_of_pos he, inverseHi_of_pos ha, hl, hrU, hcoef]

private theorem negative_inverses (i : Fin 4) (j : Fin 3) :
    inverseLo equalityRows equalityBox (Fin.natAdd 4 i) j =
      inverseLo Examples.fourRowMatrix Examples.fourRowBox i j ∧
    inverseHi equalityRows equalityBox (Fin.natAdd 4 i) j =
      inverseHi Examples.fourRowMatrix Examples.fourRowBox i j := by
  obtain ⟨_, _, hl, hu⟩ := row_rests i j
  have hcoef : equalityRows (Fin.natAdd 4 i) j = -Examples.fourRowMatrix i j := by
    simp only [equalityRows, Fin.addCases_right]
  have hrL : equalityBox.1 (.inr (Fin.natAdd 4 i)) = -Examples.fourRowBox.2 (.inr i) := by
    simp only [equalityBox, Sum.elim_inr, Fin.addCases_right]
  have hrU : equalityBox.2 (.inr (Fin.natAdd 4 i)) = -Examples.fourRowBox.1 (.inr i) := by
    simp only [equalityBox, Sum.elim_inr, Fin.addCases_right]
  have hvL : equalityBox.1 (.inl j) = Examples.fourRowBox.1 (.inl j) := by
    simp only [equalityBox, Sum.elim_inl, equalityLower]
  have hvU : equalityBox.2 (.inl j) = Examples.fourRowBox.2 (.inl j) := by
    simp only [equalityBox, Sum.elim_inl, equalityUpper]
  have hdiv (u v a : ℝ) : (-u - -v) / -a = (u - v) / a := by
    rw [div_neg, neg_sub_neg]
    ring
  rcases lt_trichotomy (Examples.fourRowMatrix i j) 0 with ha | ha | ha
  · have he : 0 < equalityRows (Fin.natAdd 4 i) j := by
      rw [hcoef]
      exact neg_pos.mpr ha
    constructor
    · rw [inverseLo_of_pos he, inverseLo_of_neg ha, hu, hrL, hcoef, hdiv]
    · rw [inverseHi_of_pos he, inverseHi_of_neg ha, hl, hrU, hcoef, hdiv]
  · have he : equalityRows (Fin.natAdd 4 i) j = 0 := hcoef.trans (neg_eq_zero.mpr ha)
    constructor
    · exact (inverseLo_of_zero he).trans (hvL.trans (inverseLo_of_zero ha).symm)
    · exact (inverseHi_of_zero he).trans (hvU.trans (inverseHi_of_zero ha).symm)
  · have he : equalityRows (Fin.natAdd 4 i) j < 0 := by
      rw [hcoef]
      exact neg_neg_of_pos ha
    constructor
    · rw [inverseLo_of_neg he, inverseLo_of_pos ha, hl, hrU, hcoef, hdiv]
    · rw [inverseHi_of_neg he, inverseHi_of_pos ha, hu, hrL, hcoef, hdiv]

private theorem equality_box_ordered : equalityBox.1 ≤ equalityBox.2 := by
  have ho := Examples.fourRow_feasible_without_graph_point.1
  intro c
  cases c with
  | inl j => exact ho (.inl j)
  | inr i =>
    refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun k => ?_) i
    · simpa only [equalityBox, Sum.elim_inr, Fin.addCases_left] using ho (.inr k)
    · simpa only [equalityBox, Sum.elim_inr, Fin.addCases_right] using
        neg_le_neg (ho (.inr k))

private theorem equality_box_within_initial : Within equalityBox equalityInitial := by
  have hrow := (isFixedPt_step_iff.mp Examples.fourRow_feasible_without_graph_point.2.1).2.1
  have himg := row_images
    (Sum.elim equalityLower (fun _ => 0), Sum.elim equalityUpper (fun _ => 0))
    (fun _ => rfl) (fun _ => rfl)
  apply within_iff.mpr
  constructor
  · intro c
    cases c with
    | inl j => simp [equalityBox, equalityInitial]
    | inr i =>
      refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun k => ?_) i
      · simp only [equalityInitial, sourceInitial_fst_inr, equalityBox, Sum.elim_inr,
          Fin.addCases_left]
        exact (min_le_left _ _).trans ((himg k).1.trans_le (hrow k).1)
      · simp only [equalityInitial, sourceInitial_fst_inr, equalityBox, Sum.elim_inr,
          Fin.addCases_right]
        exact (min_le_left _ _).trans ((himg k).2.2.1.trans_le (neg_le_neg (hrow k).2))
  · intro c
    cases c with
    | inl j => simp [equalityBox, equalityInitial]
    | inr i =>
      refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun k => ?_) i <;>
        simp [equalityBox, equalityInitial, equalityCaps]

private theorem equality_box_fixed :
    Function.IsFixedPt (step equalityRows equalityInitial) equalityBox := by
  obtain ⟨_, hrow, hinv⟩ :=
    isFixedPt_step_iff.mp Examples.fourRow_feasible_without_graph_point.2.1
  have himg := row_images equalityBox (fun _ => rfl) (fun _ => rfl)
  refine isFixedPt_step_iff.mpr ⟨equality_box_within_initial, ?_, ?_⟩
  · intro i
    refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun k => ?_) i
    · rw [(himg k).1, (himg k).2.1]
      simpa only [equalityBox, Sum.elim_inr, Fin.addCases_left] using hrow k
    · rw [(himg k).2.2.1, (himg k).2.2.2]
      simpa only [equalityBox, Sum.elim_inr, Fin.addCases_right] using
        And.intro (neg_le_neg (hrow k).2) (neg_le_neg (hrow k).1)
  · intro i j
    refine Fin.addCases (m := 4) (n := 4) (fun k => ?_) (fun k => ?_) i
    · rw [(positive_inverses k j).1, (positive_inverses k j).2]
      simpa only [equalityBox, Sum.elim_inl, equalityLower, equalityUpper] using hinv k j
    · rw [(negative_inverses k j).1, (negative_inverses k j).2]
      simpa only [equalityBox, Sum.elim_inl, equalityLower, equalityUpper] using hinv k j

private theorem equality_source_empty (extra : Set (Fin 3 → ℝ))
    (integers : Finset (Fin 3)) :
    sourceSet equalityRows equalityCaps extra integers ∩ Icc equalityLower equalityUpper = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hs, hx⟩
  have hr := (mem_sourceSet.mp hs).1
  have hg : graph Examples.fourRowMatrix x ∈ Icc Examples.fourRowBox.1 Examples.fourRowBox.2 := by
    apply mem_Icc_graph_iff.mpr
    refine ⟨fun j => ⟨hx.1 j, hx.2 j⟩, fun i => ?_⟩
    have hup := hr (i.castAdd 4)
    have hlo := hr (Fin.natAdd 4 i)
    simp only [Matrix.mulVec_apply_eq_sum, equalityRows, equalityCaps, Fin.addCases_left,
      Fin.addCases_right, neg_mul, Finset.sum_neg_distrib] at hup hlo
    exact ⟨neg_le_neg_iff.mp hlo, hup⟩
  exact Examples.fourRow_feasible_without_graph_point.2.2.2 x hg

/-- Both directions of the four inconsistent native equalities give eight inequalities with
an actual scalar-feasible canonical box and nonempty public iterates, yet no original feasible
point in the initial box, for arbitrary unchanged extra and integer restrictions. -/
theorem eight_rows_nonempty_but_source_empty (extra : Set (Fin 3 → ℝ))
    (integers : Finset (Fin 3)) :
    IsFeasible equalityRows equalityInitial (canonical equalityRows equalityBox) ∧
    (∀ k, (publicRun equalityRows equalityInitial k : Set (Coord 3 8 → ℝ)).Nonempty) ∧
    sourceSet equalityRows equalityCaps extra integers ∩ Icc equalityLower equalityUpper = ∅ :=
  ⟨isFeasible_canonical_iff.mpr ⟨equality_box_ordered, equality_box_fixed⟩,
    coe_publicRun_nonempty_of_isFixedPt_step equality_box_ordered equality_box_fixed,
    equality_source_empty extra integers⟩

end

end TauCeti.AffineBoundTightening.SourceInfeasibilityExamples
