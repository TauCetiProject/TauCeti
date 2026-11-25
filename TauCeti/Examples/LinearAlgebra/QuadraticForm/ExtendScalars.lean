/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.ComputeDegree
import TauCeti.LinearAlgebra.QuadraticForm.Arf.Basic
import TauCeti.LinearAlgebra.QuadraticForm.ExtendScalars

/-!
# Coordinate scalar extension of `[1, 1]` from `𝔽₂` to `𝔽₄`

The binary block `[1, 1] = x² + x y + y²` over `𝔽₂` is the norm form of `𝔽₄ / 𝔽₂`. It is
anisotropic and nonsingular. Its coordinate scalar extension keeps the mixed term `x y`, so over
`𝔽₄ = 𝔽₂[ω] / (ω² + ω + 1)` it is again `x² + x y + y²`. That form vanishes at `(ω, 1)`, so scalar
extension preserves nonsingularity but not anisotropy. Dropping the mixed term would instead give
`x² + y² = (x + y)²`, which vanishes at `(1, 1)` already over `𝔽₂` and has zero polar form.

## References

* R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  §7, Example 7.5 and the scalar extension before Lemma 7.15.
-/

open Polynomial QuadraticMap QuadraticForm

namespace TauCeti

/-- Over `𝔽₂`, the block `[1, 1]` is anisotropic. -/
example : (binaryQuadraticForm (ZMod 2) 1 1).Anisotropic :=
  anisotropic_binaryQuadraticForm_one

/-- Over `𝔽₂`, the block `[1, 1]` is nonsingular. -/
example : (binaryQuadraticForm (ZMod 2) 1 1).polarBilin.Nondegenerate :=
  nondegenerate_polarBilin_binaryQuadraticForm_of_two_mul_eq_zero (by decide) (by decide)

/-- The coordinate extension of `[1, 1]` keeps the mixed term: at `(1, 1)` it takes the value
`1 + 1 + 1 = 1` over any `𝔽₂`-algebra, whereas `(x + y)²` vanishes there. -/
example (L : Type*) [CommRing L] [Algebra (ZMod 2) L] :
    extendScalars L (binaryQuadraticForm (ZMod 2) 1 1) ![1, 1] = 1 := by
  have h2 : (2 : L) = 0 := by
    have h := congrArg (algebraMap (ZMod 2) L) (show (2 : ZMod 2) = 0 by decide)
    rwa [map_ofNat, map_zero] at h
  simp only [extendScalars_binaryQuadraticForm, map_one, binaryQuadraticForm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow, mul_one]
  linear_combination h2

/-- Over `𝔽₄ = 𝔽₂[ω] / (ω² + ω + 1)`, the extension of `[1, 1]` is isotropic, at `(ω, 1)`:
scalar extension does not preserve anisotropy. -/
example :
    ¬(extendScalars (AdjoinRoot (X ^ 2 + X + 1 : (ZMod 2)[X]))
      (binaryQuadraticForm (ZMod 2) 1 1)).Anisotropic := by
  have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).degree ≠ 0 := by
    rw [show (X ^ 2 + X + 1 : (ZMod 2)[X]).degree = 2 by compute_degree!]
    decide
  have := AdjoinRoot.nontrivial (X ^ 2 + X + 1 : (ZMod 2)[X]) hdeg
  have hω := AdjoinRoot.eval₂_root (X ^ 2 + X + 1 : (ZMod 2)[X])
  simp only [eval₂_add, eval₂_X_pow, eval₂_X, eval₂_one] at hω
  intro h
  have h0 := congrFun (h ![AdjoinRoot.root _, 1] (by
    simp only [extendScalars_binaryQuadraticForm, map_one, binaryQuadraticForm_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, mul_one,
      one_pow]
    linear_combination hω)) 1
  simp at h0

end TauCeti
