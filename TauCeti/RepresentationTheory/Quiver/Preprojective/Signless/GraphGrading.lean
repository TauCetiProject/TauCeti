/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.LadderValley
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Signless

/-!
# Path grading for numerical graph words

For a finite simple graph with vertices labelled by natural numbers, every numerical
`TauCeti.signlessArrow` is homogeneous of degree one. Consequently, a valley word made from
these arrows is homogeneous in its word length. This packages the graph-word interface to the
path grading of the signless preprojective algebra. For an arbitrary simple graph, a product of
`n` backtracks at a common vertex has path degree `2 * n`.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

universe u

variable (k : Type u) [CommRing k] {n : ℕ} (G : SimpleGraph (Fin n))
  [∀ i, Fintype (G.neighborSet i)]

attribute [local instance] signlessPreprojectiveGradedAlgebra

/-- Every numerical graph arrow is homogeneous of degree one, including the zero returned for
nonadjacent or out-of-range endpoints. -/
theorem signlessArrow_mem_grade_one (i j : ℕ) :
    signlessArrow k G i j ∈ signlessPreprojectiveGrade k (DoubledQuiver G) 1 := by
  classical
  by_cases hbounds : i < n ∧ j < n
  · by_cases hadj : G.Adj ⟨i, hbounds.1⟩ ⟨j, hbounds.2⟩
    · -- `signlessArrow_of_adj` has `Fin n` endpoints, whose values are definitionally `i`, `j`.
      rw [show signlessArrow k G i j = _ from signlessArrow_of_adj k hadj]
      exact signlessPreprojectiveMk_mem_grade k _ (ofArrow_mem_grade_one _)
    · rw [signlessArrow_eq_zero k (fun hi hj h => hadj h)]
      exact Submodule.zero_mem _
  · rw [signlessArrow_eq_zero k (fun hi hj _ => hbounds ⟨hi, hj⟩)]
    exact Submodule.zero_mem _

/-- A valley word of numerical graph arrows with `s` descents and `r` climbs is homogeneous of
degree `s + r`. -/
theorem ladderValley_mem_grade (m s r : ℕ) :
    ladderValley (fun w => signlessArrow k G w (w + 1))
        (fun w => signlessArrow k G (w + 1) w) m s r ∈
      signlessPreprojectiveGrade k (DoubledQuiver G) (s + r) := by
  have hdesc : ∀ s,
      ladderValley (fun w => signlessArrow k G w (w + 1))
          (fun w => signlessArrow k G (w + 1) w) m s 0 ∈
        signlessPreprojectiveGrade k (DoubledQuiver G) s := by
    intro t
    induction t with
    | zero =>
        rw [ladderValley_zero_zero]
        exact SetLike.one_mem_graded _
    | succ t ih =>
        rw [← ladderValley_mul_d]
        simpa using mul_mem_signlessPreprojectiveGrade k _ ih
          (signlessArrow_mem_grade_one k G (m + t + 1) (m + t))
  induction r with
  | zero => simpa using hdesc s
  | succ r ih =>
      rw [← u_mul_ladderValley]
      simpa [add_assoc, add_comm, add_left_comm] using
        mul_mem_signlessPreprojectiveGrade k _
          (signlessArrow_mem_grade_one k G (m + r) (m + r + 1)) ih

/-- A product of backtracks `v → w → v` at a common vertex `v` has path degree twice the number of
backtracks. -/
theorem list_prod_signlessPreprojectiveMk_backtrackElem_mem_signlessPreprojectiveGrade
    {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] {v : V}
    (l : List {w // G.Adj v w}) :
    (l.map fun w => signlessPreprojectiveMk k _ (backtrackElem G k w.2)).prod ∈
      signlessPreprojectiveGrade k (DoubledQuiver G) (2 * l.length) := by
  simpa [map_list_prod, Function.comp_def, mul_comm] using signlessPreprojectiveMk_mem_grade k _
    (SetLike.list_prod_map_mem_graded l (fun _ => 2) _ fun w _ =>
      backtrackElem_mem_grade_two k G w.2)

end TauCeti
