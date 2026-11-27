/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Dynamics.Entropy.FiniteType
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.LinearAlgebra.Matrix.Notation
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Nonnegative

/-!
# Worked examples: entropy of subshifts of finite type

* **Golden-mean shift.** The sequences on two symbols with no two consecutive `1`s form the
  subshift of finite type with transition matrix `!![1,1;1,0]`. Its spectral radius is the
  golden ratio, with positive eigenvector `(φ, 1)`, so its entropy is `log ((1 + √5) / 2)`.
* **Full shift.** The relation that is always true gives the full shift, with the all-ones
  transition matrix; its spectral radius is the size of the alphabet (eigenvector `1`),
  recovering `coverEntropy_shift_nat`'s value `log (card α)`.
-/

public section

open Set Dynamics SymbolicDynamics.FullShift TauCeti Real
open scoped Matrix goldenRatio

namespace TauCeti.FiniteTypeEntropyExamples

/-- The golden-mean relation: from `0` go anywhere, from `1` go to `0`. -/
def goldenMean (i j : Fin 2) : Bool :=
  i == 0 || j == 0

theorem goldenMean_row (i : Fin 2) : ∃ j, goldenMean i j :=
  ⟨0, by simp [goldenMean]⟩

/-- The transition matrix of the golden-mean relation is `!![1, 1; 1, 0]`. -/
theorem sftTransitionMatrix_goldenMean : sftTransitionMatrix ℝ goldenMean = !![1, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [goldenMean]

/-- The spectral radius of the golden-mean matrix is the golden ratio. -/
theorem spectralRadius_goldenMean :
    spectralRadius ℝ (sftTransitionMatrix ℝ goldenMean) = ENNReal.ofReal φ := by
  have hv : ∀ i, 0 < (![φ, 1] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i
    · exact goldenRatio_pos
    · exact one_pos
  have hMv : sftTransitionMatrix ℝ goldenMean *ᵥ ![φ, 1] = φ • ![φ, 1] := by
    rw [sftTransitionMatrix_goldenMean]
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      nlinarith [goldenRatio_sq]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [Matrix.spectralRadius_real_eq_of_nonneg (sftTransitionMatrix_nonneg _),
    Matrix.spectralRadius_eq_of_mulVec_eq_smul (sftTransitionMatrix_nonneg _) hv hMv]

/-- The golden-mean shift, with matrix `!![1, 1; 1, 0]`, has topological entropy
`log ((1 + √5) / 2)`. -/
example [UniformSpace (Fin 2)] [DiscreteUniformity (Fin 2)] :
    coverEntropy (shift (1 : ℕ)) (sftOneSided goldenMean) = Real.log ((1 + √5) / 2) := by
  rw [coverEntropy_shift_sftOneSided goldenMean_row, spectralRadius_goldenMean,
    ENNReal.log_ofReal_of_pos goldenRatio_pos]

/-- For the relation that is always true the entropy formula gives `log (card α)`, the entropy of
the full shift. -/
example {α : Type*} [Fintype α] [Nonempty α] [UniformSpace α] [DiscreteUniformity α] :
    coverEntropy (shift (1 : ℕ)) (sftOneSided (fun _ _ ↦ true : α → α → Bool)) =
      ENNReal.log (Fintype.card α) := by
  classical
  have hMv : sftTransitionMatrix ℝ (fun _ _ ↦ true : α → α → Bool) *ᵥ (fun _ ↦ 1) =
      (Fintype.card α : ℝ) • fun _ ↦ 1 := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [coverEntropy_shift_sftOneSided (fun _ ↦ ⟨Classical.arbitrary α, rfl⟩),
    Matrix.spectralRadius_real_eq_of_nonneg (sftTransitionMatrix_nonneg _),
    Matrix.spectralRadius_eq_of_mulVec_eq_smul (sftTransitionMatrix_nonneg _) (fun _ ↦ one_pos) hMv,
    ENNReal.ofReal_natCast]

end TauCeti.FiniteTypeEntropyExamples
