/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Determinants of real powers of positive semidefinite matrices

Over `𝕜 = ℝ` or `ℂ`, the real power `X ^ s` of a positive semidefinite matrix `X` is defined by
the continuous functional calculus. Diagonalizing `X`, its determinant is the real power of the
determinant of `X`.

## Main results

* `Matrix.PosSemidef.det_rpow`: the determinant of a real power `X ^ s` of a positive
  semidefinite matrix is `(det X) ^ s`.
-/

public section

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The determinant of a real power `X ^ s` of a positive semidefinite matrix is the real power
`(det X) ^ s` of its determinant, which is a nonnegative real number. -/
theorem PosSemidef.det_rpow {X : Matrix n n 𝕜} (hX : X.PosSemidef) (s : ℝ) :
    (X ^ s).det = ((RCLike.re X.det ^ s : ℝ) : 𝕜) := by
  rw [CFC.rpow_eq_cfc_real hX.nonneg, hX.isHermitian.cfc_eq, hX.isHermitian.det_eq_prod_eigenvalues]
  simp only [IsHermitian.cfc, det_map, det_diagonal, Function.comp_apply, ← RCLike.ofReal_prod,
    RCLike.ofReal_re, Real.finsetProd_rpow _ _ (fun i _ ↦ hX.eigenvalues_nonneg i) s]

end Matrix
