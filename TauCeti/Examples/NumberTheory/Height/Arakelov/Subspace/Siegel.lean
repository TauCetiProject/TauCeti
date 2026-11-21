/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Height.Arakelov.SiegelsLemma

/-!
# Worked examples: Minkowski-ball and rational Euclidean Siegel bounds

This file illustrates `Submodule.exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow`,
`Submodule.exists_ne_zero_mem_intPoints_height2_le`, and
`Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le` on concrete rational systems:

* A single linear form `(1, 2)` in `ℚ²` has height `√5`, so
  `Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le` produces a nonzero integer kernel vector of
  Euclidean height at most `√2 * √5`; in fact the kernel is spanned by `(-2, 1)`, which has exact
  Euclidean height `√5`.
* The `1`-dimensional subspace `ℚ ∙ ![(1 : ℚ), 2]` satisfies both the sharp Minkowski-ball bound
  (`Submodule.exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow`, where
  `2 / √π * Γ(3 / 2) = 1`) and the rational bound
  (`Submodule.exists_ne_zero_mem_intPoints_height2_le`).
* A single nonzero linear form in `ℚ¹` (`U = V = 1`) has trivial kernel, showing that the strict
  inequality `Fintype.card m < Fintype.card ι` is necessary.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
-/

noncomputable section

open Module NumberField TauCeti
open scoped BigOperators Matrix

/-- Over `ℚ` with the single form `(1, 2)` in two variables (of Euclidean height `√5`), Siegel's
lemma gives a nonzero integer kernel vector of height at most `√2 * √5`, while the kernel vector
`(-2, 1)` has exact Euclidean height `√5`. -/
example :
    height2 ![(1 : ℚ), 2] = √5 ∧
      ![(1 : ℚ), 2] ⬝ᵥ ![(-2 : ℚ), 1] = 0 ∧
      height2 ![(-2 : ℚ), 1] = √5 ∧
      (∃ z : Fin 2 → ℤ, z ≠ 0 ∧ ![(1 : ℚ), 2] ⬝ᵥ (fun i ↦ (z i : ℚ)) = 0 ∧
        height2 (fun i ↦ (z i : ℚ)) ≤ √2 * √5) := by
  have h12 : height2 ![(1 : ℚ), 2] = √5 := by
    have hcast : ![(1 : ℚ), 2] = ((↑) : ℤ → ℚ) ∘ ![1, 2] := by
      ext i; fin_cases i <;> simp
    rw [hcast, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_two]
  have hm21_ker : ![(1 : ℚ), 2] ⬝ᵥ ![(-2 : ℚ), 1] = 0 := by
    norm_num [dotProduct, Fin.sum_univ_two]
  have hm21 : height2 ![(-2 : ℚ), 1] = √5 := by
    have hcast : ![(-2 : ℚ), 1] = ((↑) : ℤ → ℚ) ∘ ![-2, 1] := by
      ext i; fin_cases i <;> simp
    rw [hcast, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_two]
  refine ⟨h12, hm21_ker, hm21, ?_⟩
  let A : Matrix (Fin 1) (Fin 2) ℚ := Matrix.of fun _ ↦ ![(1 : ℚ), 2]
  have hA : ∀ i, A.row i ≠ 0 := by
    intro i h
    have := congrFun h 0
    simp [A] at this
  obtain ⟨z, hz0, hmul, hle⟩ :=
    Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le hA (by decide : Fintype.card (Fin 1) <
      Fintype.card (Fin 2))
  refine ⟨z, hz0, ?_, ?_⟩
  · simpa [A, Matrix.mulVec] using congrFun hmul 0
  · norm_num [A, h12] at hle
    exact hle

/-- Over `ℚ` on the `1`-dimensional subspace `V = ℚ ∙ ![(1 : ℚ), 2]`, both the Minkowski-ball
bound `Submodule.exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow` and the rational bound
`Submodule.exists_ne_zero_mem_intPoints_height2_le` produce a nonzero integral point with
`height2 ≤ √5`. -/
example :
    let V : Submodule ℚ (Fin 2 → ℚ) := ℚ ∙ ![(1 : ℚ), 2]
    (∃ z ∈ V.integerPoints, z ≠ 0 ∧ height2 (fun i ↦ (z i : ℚ)) ≤ V.subspaceHeight) ∧
      (∃ z ∈ V.intPoints, z ≠ 0 ∧ height2 (fun i ↦ (z i : ℚ)) ≤ V.subspaceHeight) := by
  intro V
  have hv0 : ![(1 : ℚ), 2] ≠ 0 := fun h ↦ one_ne_zero (congrFun h 0)
  have hV : V ≠ ⊥ := by simp [V]
  have hdim : Module.finrank ℚ V = 1 := finrank_span_singleton hv0
  have hconst :
      2 / √((Module.finrank ℚ ℚ : ℝ) * Real.pi) *
          Real.Gamma ((Module.finrank ℚ ℚ * Module.finrank ℚ V : ℝ) / 2 + 1) ^
            ((Module.finrank ℚ ℚ * Module.finrank ℚ V : ℝ)⁻¹) *
          |(NumberField.discr ℚ : ℝ)| ^ (1 / (2 * (Module.finrank ℚ ℚ : ℝ))) *
          V.subspaceHeight ^ (Module.finrank ℚ V : ℝ)⁻¹ =
        V.subspaceHeight := by
    have h32 : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
    have hGamma : Real.Gamma (3 / 2) = √Real.pi / 2 := by
      rw [h32, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
      ring
    rw [hdim, NumberField.discr_rat, finrank_self]
    norm_num
    rw [hGamma]
    have hpi : 0 < √Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    field_simp [hpi.ne']
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hzV, hz0, hle⟩ :=
      Submodule.exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow hV
    exact ⟨z, hzV, hz0, hle.trans_eq hconst⟩
  · obtain ⟨z, hzV, hz0, hle⟩ := Submodule.exists_ne_zero_mem_intPoints_height2_le hV
    refine ⟨z, hzV, hz0, hle.trans_eq ?_⟩
    simp [hdim]

/-- A single nonzero linear form in one variable has trivial kernel, confirming that the strict
inequality `Fintype.card m < Fintype.card ι` cannot be weakened to `≤`. -/
example : ¬ ∃ x : Fin 1 → ℚ, x ≠ 0 ∧ ![(1 : ℚ)] ⬝ᵥ x = 0 := by
  rintro ⟨x, hx0, hdot⟩
  apply hx0
  ext i
  fin_cases i
  simpa [dotProduct] using hdot

end
