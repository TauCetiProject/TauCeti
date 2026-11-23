/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Linarith

/-!
# Positive definite and skew-Hermitian quaternionic matrices

Hermitian and skew-Hermitian quadratic-form identities for quaternionic matrices, together with
`Matrix.QuatPosDef`.
-/

public section

open scoped Matrix Quaternion

namespace Matrix

/-- Over a star semiring, conjugating `star v ⬝ᵥ (M *ᵥ v)` replaces `M` by `Mᴴ`. -/
theorem star_dotProduct_mulVec_self {n R : Type*} [Fintype n] [NonUnitalSemiring R] [StarRing R]
    (M : Matrix n n R) (v : n → R) : star (star v ⬝ᵥ (M *ᵥ v)) = star v ⬝ᵥ (Mᴴ *ᵥ v) := by
  rw [← star_dotProduct, star_mulVec, dotProduct_mulVec]

/-- For a skew-Hermitian matrix `Mᴴ = -M`, `star v ⬝ᵥ (M *ᵥ v)` is skew-adjoint. -/
theorem star_dotProduct_mulVec_self_of_skewHermitian {n R : Type*} [Fintype n] [Ring R]
    [StarRing R] {M : Matrix n n R} (hM : Mᴴ = -M) (v : n → R) :
    star (star v ⬝ᵥ (M *ᵥ v)) = -(star v ⬝ᵥ (M *ᵥ v)) := by
  rw [star_dotProduct_mulVec_self, hM, neg_mulVec, dotProduct_neg]

/-- The real part of the quadratic form of a skew-Hermitian quaternionic matrix vanishes. -/
theorem re_dotProduct_mulVec_eq_zero_of_skewHermitian {n : Type*} [Fintype n]
    {M : Matrix n n ℍ[ℝ]} (hM : Mᴴ = -M) (v : n → ℍ[ℝ]) :
    (star v ⬝ᵥ (M *ᵥ v)).re = 0 := by
  have hre := congrArg QuaternionAlgebra.re (star_dotProduct_mulVec_self_of_skewHermitian hM v)
  simp only [Quaternion.re_star, QuaternionAlgebra.re_neg] at hre; linarith

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
