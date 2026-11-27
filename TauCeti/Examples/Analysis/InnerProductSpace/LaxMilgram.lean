/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram

/-!
# Check: the coercive solution map is not Mathlib's Lax--Milgram equivalence

On `V = ℝ` take the coercive form `q(u, v) = 2 u v` (`isCoercive_twoMul`) and the functional
`ℓ(v) = 6 v`. Mathlib's equivalence `IsCoercive.continuousLinearEquivOfBilin` is `v ↦ 2 v`
(`continuousLinearEquivOfBilin_twoMul_apply`), the Riesz vector of `ℓ` is `6`
(`toDual_symm_sixMul`), and the solution map `IsCoercive.solutionOfFunctional` gives `u = 3`
(`solutionOfFunctional_twoMul_sixMul`), with `q(3, v) = 6 v`, while the equivalence itself applied
to the Riesz vector would give `12` (`continuousLinearEquivOfBilin_twoMul_six`).
-/

public section

namespace TauCeti.Examples.LaxMilgram

open ContinuousLinearMap

/-- The form `q(u, v) = 2 u v` on `ℝ`. -/
noncomputable abbrev twoMul : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := (2 : ℝ) • mul ℝ ℝ

/-- The functional `ℓ(v) = 6 v` on `ℝ`. -/
noncomputable abbrev sixMul : StrongDual ℝ ℝ := (6 : ℝ) • ContinuousLinearMap.id ℝ ℝ

/-- `q(u, v) = 2 u v` is coercive. -/
theorem isCoercive_twoMul : IsCoercive twoMul :=
  ⟨2, two_pos, fun u ↦ by simp [Real.norm_eq_abs, mul_assoc, abs_mul_abs_self]⟩

/-- Mathlib's Lax--Milgram equivalence for `q(u, v) = 2 u v` is `v ↦ 2 v`. -/
theorem continuousLinearEquivOfBilin_twoMul_apply (v : ℝ) :
    isCoercive_twoMul.continuousLinearEquivOfBilin v = 2 * v := by
  have h := isCoercive_twoMul.continuousLinearEquivOfBilin_apply v 1
  simpa [real_inner_eq_re_inner, mul_comm] using h

/-- The Riesz vector of `ℓ(v) = 6 v` is `6`. -/
theorem toDual_symm_sixMul : (InnerProductSpace.toDual ℝ ℝ).symm sixMul = 6 := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := ℝ) (x := 1) (y := sixMul)
  simpa [real_inner_eq_re_inner, mul_comm] using h

/-- The solution map gives `u = 3` for `q(u, v) = 2 u v` and `ℓ(v) = 6 v`. -/
theorem solutionOfFunctional_twoMul_sixMul :
    isCoercive_twoMul.solutionOfFunctional sixMul = 3 := by
  refine (isCoercive_twoMul.eq_solutionOfFunctional fun v ↦ ?_).symm
  simp only [twoMul, sixMul, smul_apply, mul_apply', id_apply, smul_eq_mul]
  ring

/-- Mathlib's equivalence applied to the Riesz vector `6` of `ℓ` gives `12`, not the solution
`3`. -/
theorem continuousLinearEquivOfBilin_twoMul_six :
    isCoercive_twoMul.continuousLinearEquivOfBilin
      ((InnerProductSpace.toDual ℝ ℝ).symm sixMul) = 12 := by
  rw [toDual_symm_sixMul, continuousLinearEquivOfBilin_twoMul_apply]
  norm_num

end TauCeti.Examples.LaxMilgram
