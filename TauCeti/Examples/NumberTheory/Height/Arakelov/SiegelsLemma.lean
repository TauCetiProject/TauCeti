/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Height.Arakelov.SiegelsLemma

/-!
# Worked examples: Minkowski-ball and rational Euclidean Siegel bounds

This file illustrates `Submodule.exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow` and
`Submodule.exists_ne_zero_mem_intPoints_height2_le` on concrete rational systems:

* The `1`-dimensional subspace `ℚ ∙ ![(1 : ℚ), 2]` satisfies both the sharp Minkowski-ball bound
  (`Submodule.exists_ne_zero_mem_integerPoints_height2_le_mul_Gamma_rpow`, where
  `2 / √π * Γ(3 / 2) = 1`) and the rational bound
  (`Submodule.exists_ne_zero_mem_intPoints_height2_le`).

See `TauCeti.Examples.NumberTheory.Height.Arakelov.KernelBasis` for the full-rank `U = V = 1`
boundary example showing that `Fintype.card m < Fintype.card ι` is necessary.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
-/

noncomputable section

open Module NumberField TauCeti
open scoped BigOperators

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

end
