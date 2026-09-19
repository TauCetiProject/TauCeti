/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic

/-!
# Rank sublevel sets on the symmetric subspace

The symmetric matrices of rank at most `k` form a closed, hence measurable, subset of
`selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)`: the rank of a matrix is the rank of the
operator it induces on Euclidean space (`Matrix.rank_coe_toEuclideanCLM`), and having rank at
least `k + 1` is an open condition on operators.

Measurability is what upgrades an everywhere-true rank bound for a symmetric-matrix distribution,
such as the Gaussian-Gram Wishart law, to an almost-everywhere statement.

## Main declarations

* `TauCeti.isClosed_setOfPred_rank_le` — the symmetric matrices of rank at most `k` are closed.
* `TauCeti.measurableSet_setOfPred_rank_le` — they are measurable.
-/

public section

namespace TauCeti

variable {p : ℕ}

/-- **The symmetric matrices of rank at most `k` are closed.** -/
theorem isClosed_setOfPred_rank_le (k : ℕ) :
    IsClosed {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ k} := by
  rw [← isOpen_compl_iff]
  simp only [Set.compl_ofPred, not_le]
  let f : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.comp
      (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype
  -- `f` is the carrier coercion followed by `Matrix.toEuclideanCLM`, so its application is that
  -- operator on the nose.
  have hf (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      f A = Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ) (A : Matrix (Fin p) (Fin p) ℝ) := rfl
  have hrank (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      LinearMap.rank (f A : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) =
        (A : Matrix (Fin p) (Fin p) ℝ).rank := by
    rw [hf, Matrix.rank_coe_toEuclideanCLM]
  have hset : {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      k < (A : Matrix (Fin p) (Fin p) ℝ).rank} =
      f ⁻¹' {g | (k + 1 : ℕ) ≤ (g : EuclideanSpace ℝ (Fin p) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin p)).rank} := by
    ext A
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hrank, Nat.cast_le]
    exact Nat.lt_iff_add_one_le
  rw [hset]
  exact (isOpen_setOfPred_nat_le_rank (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin p))
    (F := EuclideanSpace ℝ (Fin p)) (k + 1)).preimage
      (LinearMap.continuous_of_finiteDimensional f)

/-- The symmetric matrices of rank at most `k` are measurable. -/
theorem measurableSet_setOfPred_rank_le (k : ℕ) :
    MeasurableSet {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).rank ≤ k} :=
  (isClosed_setOfPred_rank_le k).measurableSet

end TauCeti
