/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.GeometricMean

/-!
# The positive semidefinite solution of `A * S * A = T`

The Loewner order on square matrices makes `Matrix n n 𝕜` an algebra with a continuous functional
calculus, so `TauCeti.geometricMean` applies to it: for `S` positive definite and `T` positive
semidefinite there is exactly one positive semidefinite `A` with `A * S * A = T`, namely
`TauCeti.geometricMean S⁻¹ʳ T`, which is the classical matrix
`√(S⁻¹) * √(√S * T * √S) * √(S⁻¹)`.

Read through covariance matrices, that matrix is the linear map pushing a centred Gaussian law of
covariance `S` forward to one of covariance `T`, that is, the Brenier map between two Gaussians.

## Main results

* `Matrix.PosDef.existsUnique_posSemidef_mul_mul`: existence and uniqueness of that matrix.
-/

public section

noncomputable section

open Ring TauCeti
open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] {S T : Matrix n n 𝕜}

/-- For a positive definite `S` and a positive semidefinite `T` there is exactly one positive
semidefinite matrix `A` with `A * S * A = T`; it is `TauCeti.geometricMean S⁻¹ʳ T`. -/
theorem PosDef.existsUnique_posSemidef_mul_mul (hS : S.PosDef) (hT : T.PosSemidef) :
    ∃! A : Matrix n n 𝕜, A.PosSemidef ∧ A * S * A = T := by
  classical
  refine ⟨geometricMean S⁻¹ʳ T,
    ⟨nonneg_iff_posSemidef.mp (geometricMean_nonneg _ _), ?_⟩, ?_⟩
  · exact geometricMean_ringInverse_mul_mul_geometricMean_ringInverse hS.isStrictlyPositive
      hT.nonneg
  · rintro A ⟨hA, hAST⟩
    exact eq_geometricMean_ringInverse_of_mul_mul hAST hS.isStrictlyPositive hA.nonneg

end Matrix
