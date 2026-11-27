/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.LinearAlgebra.Matrix.Metzler
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Uniformized matrices of a two-state rate matrix

For the Q-matrix `Q = [[-2, 2], [1, -1]]`, whose largest total jump rate is `2`, the uniformized
matrix at the rate `r = 2` is the stochastic matrix `[[0, 1], [1/2, 1/2]]`, while at the rate
`r = 1` it is `[[-1, 2], [1, 0]]`, which has a negative entry and is not stochastic. The rate must
be at least every total jump rate. For `Q = 0` the uniformized matrix is `1` at every rate.
-/

public section

open Matrix

namespace TauCeti.UniformizedExamples

/-- The two-state rate matrix `[[-2, 2], [1, -1]]`. -/
abbrev Q₂ : Matrix (Fin 2) (Fin 2) ℝ := !![-2, 2; 1, -1]

/-- The two-state rate matrix `Q₂` is a Q-matrix. -/
theorem isQMatrix_Q₂ : Q₂.IsQMatrix :=
  ⟨isMetzler_iff.mpr fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp_all,
    fun i ↦ by fin_cases i <;> simp [Fin.sum_univ_two]⟩

example : Q₂.uniformized 2 = !![0, 1; 1 / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [uniformized_apply]

/-- At the rate `2`, the largest total jump rate, the uniformized matrix is stochastic. -/
example : Q₂.uniformized 2 ∈ rowStochastic ℝ (Fin 2) :=
  (uniformized_mem_rowStochastic_iff two_pos).mpr
    ⟨isQMatrix_Q₂, fun i ↦ by fin_cases i <;> norm_num⟩

example : Q₂.uniformized 1 = !![-1, 2; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [uniformized_apply]

/-- At the rate `1`, below the total jump rate `2` of the first state, the uniformized matrix is
not stochastic. -/
example : Q₂.uniformized 1 ∉ rowStochastic ℝ (Fin 2) := fun h ↦ by
  have := ((uniformized_mem_rowStochastic_iff one_pos).mp h).2 0
  norm_num at this

/-- The zero rate matrix has the identity as its uniformized matrix at every rate. -/
example (r : ℝ) : (0 : Matrix (Fin 2) (Fin 2) ℝ).uniformized r = 1 :=
  uniformized_zero_left r

end TauCeti.UniformizedExamples
