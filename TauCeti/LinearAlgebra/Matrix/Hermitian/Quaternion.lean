/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.Linarith
import TauCeti.LinearAlgebra.Matrix.ConjTranspose

/-!
# Skew-Hermitian quaternionic matrices

Establishes vanishing of the real part of the quadratic form `star v ⬝ᵥ (M *ᵥ v)` for
skew-Hermitian quaternionic matrices (`Matrix.re_dotProduct_mulVec_eq_zero_of_skewHermitian`).
-/

public section

open scoped Matrix Quaternion

namespace Matrix

/-- The real part of the quadratic form of a skew-Hermitian quaternionic matrix vanishes. -/
theorem re_dotProduct_mulVec_eq_zero_of_skewHermitian {n : Type*} [Fintype n]
    {M : Matrix n n ℍ[ℝ]} (hM : Mᴴ = -M) (v : n → ℍ[ℝ]) :
    (star v ⬝ᵥ (M *ᵥ v)).re = 0 := by
  have hre := congrArg QuaternionAlgebra.re (star_dotProduct_mulVec_self_of_skewHermitian hM v)
  simp only [Quaternion.re_star, QuaternionAlgebra.re_neg] at hre
  linarith

end Matrix
