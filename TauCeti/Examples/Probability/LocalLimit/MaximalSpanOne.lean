/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.LocalLimit.MaximalSpanOne
public import Mathlib.Probability.UniformOn
public import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# Examples of integer laws with and without maximal span one

* The uniform law on `{0, 2, 3}` has maximal span one: the differences of its atoms include
  `3 - 2 = 1`.
* The uniform law on `{0, 2}` does not: it is carried by `2ℤ`.
* The Rademacher law on `{-1, 1}`, and indeed every `Ber(1, -1, p)`, does not: it is carried by
  `1 + 2ℤ`. For `p > 0` its atoms nevertheless generate `ℤ` as a group, so the condition that the
  support generates `ℤ` would wrongly accept it; the differences of its atoms do not generate `ℤ`.
* The Bernoulli law `Ber(1, 0, p)` on `{0, 1}` with `0 < p < 1` has maximal span one, and a point
  mass does not.
-/

open MeasureTheory Measure ProbabilityTheory TauCeti.Probability unitInterval

open scoped Pointwise

namespace TauCeti.Examples.MaximalSpanOne

/-- The uniform law on `{0, 2, 3}` has maximal span one. -/
example : (uniformOn ({0, 2, 3} : Set ℤ)).HasMaximalSpanOne :=
  hasMaximalSpanOne_of_measure_singleton_ne_zero_of_measure_singleton_add_one_ne_zero (k := 2)
    (by simp [uniformOn_eq_zero_iff (Set.toFinite _)])
    (by norm_num [uniformOn_eq_zero_iff (Set.toFinite _)])

/-- The uniform law on `{0, 2}` does not have maximal span one: it is carried by `2ℤ`. -/
example : ¬ (uniformOn ({0, 2} : Set ℤ)).HasMaximalSpanOne := fun h ↦
  hasMaximalSpanOne_iff.1 h 0 2 le_rfl ((uniformOn_eq_zero_iff (Set.toFinite _)).2 (by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (rfl | rfl) <;> norm_num))

variable {p : I}

/-- The Rademacher-type law on `{-1, 1}` does not have maximal span one: it is carried by
`1 + 2ℤ`. -/
example : ¬ (Ber((1 : ℤ), -1, p)).HasMaximalSpanOne := by
  rw [hasMaximalSpanOne_bernoulliMeasure_iff]
  norm_num

/-- For `0 < p`, the atoms of `Ber(1, -1, p)` generate `ℤ` as a group: generation by the support is
weaker than maximal span one. -/
example (hp : 0 < (p : ℝ)) : AddSubgroup.closure {k : ℤ | Ber((1 : ℤ), -1, p) {k} ≠ 0} = ⊤ := by
  rw [eq_top_iff, ← Int.zmultiples_one, AddSubgroup.zmultiples_le]
  exact AddSubgroup.subset_closure (bernoulliMeasure_singleton_left_ne_zero hp)

/-- The differences of the atoms of `Ber(1, -1, p)` do not generate `ℤ`. -/
example : AddSubgroup.closure ({k : ℤ | Ber((1 : ℤ), -1, p) {k} ≠ 0} -
    {k : ℤ | Ber((1 : ℤ), -1, p) {k} ≠ 0}) ≠ ⊤ := by
  rw [Ne, ← hasMaximalSpanOne_iff_closure_sub_eq_top, hasMaximalSpanOne_bernoulliMeasure_iff]
  norm_num

/-- The Bernoulli law on `{0, 1}` with parameter `0 < p < 1` has maximal span one. -/
example (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1) : (Ber((1 : ℤ), 0, p)).HasMaximalSpanOne :=
  hasMaximalSpanOne_bernoulliMeasure_iff.2 ⟨by norm_num, hp₀, hp₁⟩

/-- A point mass does not have maximal span one. -/
example : ¬ (dirac (5 : ℤ)).HasMaximalSpanOne :=
  not_hasMaximalSpanOne_dirac 5

end TauCeti.Examples.MaximalSpanOne
