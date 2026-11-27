/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Dynamics.Entropy.FiniteType
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.LinearAlgebra.Matrix.Notation
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Positive

/-!
# Worked examples: entropy of subshifts of finite type

* **Golden-mean shift.** The sequences on two symbols with no two consecutive `1`s form the
  subshift of finite type with matrix `!![1,1;1,0]`. Its spectral radius is the golden ratio,
  with positive eigenvector `(φ, 1)`, so its entropy is `log ((1 + √5) / 2)`.
* **Full shift.** The all-ones matrix gives the full shift; its spectral radius is the size of
  the alphabet (eigenvector `1`), recovering `coverEntropy_shift_nat`'s value `log (card α)`.
-/

public section

open Set Dynamics SymbolicDynamics.FullShift TauCeti Real
open scoped Matrix goldenRatio

namespace TauCeti.FiniteTypeEntropyExamples

/-- The golden-mean transition matrix: from `0` go anywhere, from `1` go to `0`. -/
noncomputable def goldenMean : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]

theorem goldenMean_zero_or_one (i j : Fin 2) : goldenMean i j = 0 ∨ goldenMean i j = 1 := by
  fin_cases i <;> fin_cases j <;> simp [goldenMean]

theorem goldenMean_row (i : Fin 2) : ∃ j, goldenMean i j = 1 :=
  ⟨0, by fin_cases i <;> simp [goldenMean]⟩

/-- The spectral radius of the golden-mean matrix is the golden ratio. -/
theorem spectralRadius_goldenMean : spectralRadius ℝ goldenMean = ENNReal.ofReal φ := by
  have hM : ∀ i j, 0 ≤ goldenMean i j := fun i j ↦
    (goldenMean_zero_or_one i j).elim (·.ge) fun h ↦ h ▸ zero_le_one
  have hv : ∀ i, 0 < (![φ, 1] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i
    · exact goldenRatio_pos
    · exact one_pos
  have hMv : goldenMean *ᵥ ![φ, 1] = φ • ![φ, 1] := by
    ext i
    fin_cases i
    · simp [goldenMean, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      nlinarith [goldenRatio_sq]
    · simp [goldenMean, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [Matrix.spectralRadius_real_eq_of_nonneg hM,
    Matrix.spectralRadius_eq_of_mulVec_eq_smul hM hv hMv]

/-- The golden-mean shift has topological entropy `log ((1 + √5) / 2)`. -/
example [UniformSpace (Fin 2)] [DiscreteUniformity (Fin 2)] :
    coverEntropy (shift (1 : ℕ)) (sftSet goldenMean) = Real.log ((1 + √5) / 2) := by
  rw [coverEntropy_shift_sftSet goldenMean_zero_or_one goldenMean_row, spectralRadius_goldenMean,
    ENNReal.log_ofReal_of_pos goldenRatio_pos]

/-- The all-ones matrix defines the full shift. -/
theorem sftSet_one {α : Type*} : sftSet (Matrix.of fun _ _ ↦ (1 : ℝ) : Matrix α α ℝ) = univ := by
  ext x
  simp [mem_sftSet]

/-- For the all-ones matrix the entropy formula gives `log (card α)`, the entropy of the full
shift. -/
example {α : Type*} [Fintype α] [Nonempty α] [UniformSpace α] [DiscreteUniformity α] :
    coverEntropy (shift (1 : ℕ)) (sftSet (Matrix.of fun _ _ ↦ (1 : ℝ) : Matrix α α ℝ)) =
      ENNReal.log (Fintype.card α) := by
  classical
  have hM : ∀ i j : α, 0 ≤ (Matrix.of fun _ _ ↦ (1 : ℝ) : Matrix α α ℝ) i j := fun _ _ ↦ by
    simp
  have hMv : (Matrix.of fun _ _ ↦ (1 : ℝ) : Matrix α α ℝ) *ᵥ (fun _ ↦ 1) =
      (Fintype.card α : ℝ) • fun _ ↦ 1 := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [coverEntropy_shift_sftSet (M := Matrix.of fun _ _ ↦ (1 : ℝ)) (fun _ _ ↦ Or.inr rfl)
      (fun _ ↦ ⟨Classical.arbitrary α, rfl⟩),
    Matrix.spectralRadius_real_eq_of_nonneg hM,
    Matrix.spectralRadius_eq_of_mulVec_eq_smul hM (fun _ ↦ one_pos) hMv, ENNReal.ofReal_natCast]

end TauCeti.FiniteTypeEntropyExamples
