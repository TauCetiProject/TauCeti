/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Positive definite quaternionic matrices

Defines `Matrix.QuatPosDef` for Hermitian quaternionic matrices with `(star v ⬝ᵥ (M *ᵥ v)).re > 0`
on nonzero vectors, with sum expansion (`Matrix.quatPosDef_iff_sum`) and cone operations
(`Matrix.QuatPosDef.add`, `Matrix.QuatPosDef.smul`).
-/

public section

open scoped Matrix Quaternion

namespace Matrix

section

variable {n : Type*} [Fintype n]

/-- A quaternionic matrix `M : Matrix n n ℍ[ℝ]` is **positive definite** if it is Hermitian and
`(star v ⬝ᵥ (M *ᵥ v)).re > 0` for every nonzero vector `v : n → ℍ[ℝ]`. -/
def QuatPosDef (M : Matrix n n ℍ[ℝ]) : Prop :=
  M.IsHermitian ∧ ∀ v : n → ℍ[ℝ], v ≠ 0 → 0 < (star v ⬝ᵥ (M *ᵥ v)).re

/-- Characterization of `Matrix.QuatPosDef` via Hermitian symmetry and quadratic-form positivity. -/
theorem quatPosDef_iff (M : Matrix n n ℍ[ℝ]) :
    M.QuatPosDef ↔ M.IsHermitian ∧ ∀ v : n → ℍ[ℝ], v ≠ 0 → 0 < (star v ⬝ᵥ (M *ᵥ v)).re := Iff.rfl

theorem QuatPosDef.isHermitian {M : Matrix n n ℍ[ℝ]} (hM : M.QuatPosDef) : M.IsHermitian := hM.1

theorem QuatPosDef.pos {M : Matrix n n ℍ[ℝ]} (hM : M.QuatPosDef) {v : n → ℍ[ℝ]} (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ (M *ᵥ v)).re := hM.2 v hv

/-- The sum of two positive definite quaternionic matrices is positive definite. -/
theorem QuatPosDef.add {M N : Matrix n n ℍ[ℝ]} (hM : M.QuatPosDef) (hN : N.QuatPosDef) :
    (M + N).QuatPosDef :=
  ⟨hM.1.add hN.1, fun v hv ↦ by
    simpa [Matrix.add_mulVec, dotProduct_add] using add_pos (hM.2 v hv) (hN.2 v hv)⟩

/-- A strictly positive real scalar multiple of a positive definite quaternionic matrix is
positive definite. -/
theorem QuatPosDef.smul {c : ℝ} (hc : 0 < c) {M : Matrix n n ℍ[ℝ]} (hM : M.QuatPosDef) :
    (c • M).QuatPosDef :=
  ⟨ext fun i j ↦ by simp [hM.1.apply i j], fun v hv ↦ by
    simpa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using mul_pos hc (hM.2 v hv)⟩

/-- Sum expansion of `Matrix.QuatPosDef` in terms of `∑ j, ∑ k, star (v j) * M j k * v k`. -/
theorem quatPosDef_iff_sum (M : Matrix n n ℍ[ℝ]) :
    M.QuatPosDef ↔ M.IsHermitian ∧ ∀ v : n → ℍ[ℝ], v ≠ 0 →
      0 < (∑ j : n, ∑ k : n, star (v j) * M j k * v k).re := by
  simp only [QuatPosDef, dotProduct, mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]

/-- A quaternionic matrix on an empty index type is vacuously positive definite. -/
theorem QuatPosDef.of_isEmpty [IsEmpty n] (M : Matrix n n ℍ[ℝ]) : M.QuatPosDef :=
  ⟨ext fun i _ ↦ isEmptyElim i, fun _ hv ↦ absurd (funext fun i ↦ isEmptyElim i) hv⟩

end

end Matrix
