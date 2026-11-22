/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.InnerProductSpace.BilinearForm.End

/-!
# Orthogonal orthonormal bases for real quadratic forms

Every quadratic form `Q` on a finite-dimensional real inner product space `W` of dimension `m`
admits an orthonormal basis `(b₀, …, bₘ₋₁)` of `W` that is orthogonal for the polar bilinear form
`QuadraticMap.associated Q` (`QuadraticMap.exists_orthonormalBasis_isOrthoᵢ_associated`), obtained
from the spectral theorem for the self-adjoint operator representing `QuadraticMap.associated Q` in
the inner product.
-/

public section

noncomputable section

open Module
open scoped RealInnerProductSpace

namespace QuadraticMap

/-- Every quadratic form on a finite-dimensional real inner product space admits an orthonormal
basis orthogonal for its associated symmetric bilinear form. -/
theorem exists_orthonormalBasis_isOrthoᵢ_associated {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (Q : QuadraticForm ℝ W) {m : ℕ} (hm : finrank ℝ W = m) :
    ∃ b : OrthonormalBasis (Fin m) ℝ W, (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis := by
  let T : W →ₗ[ℝ] W := TauCeti.bilinFormToEnd (QuadraticMap.associated (R := ℝ) Q)
  have hinner : ∀ u v, ⟪T u, v⟫ = QuadraticMap.associated (R := ℝ) Q u v :=
    LinearMap.BilinForm.inner_bilinFormToEnd_left _
  have hT : T.IsSymmetric :=
    TauCeti.isSymmetric_bilinFormToEnd_iff.mpr ⟨(QuadraticForm.associated_isSymm ℝ Q).eq⟩
  refine ⟨hT.eigenvectorBasis hm, fun i j hij ↦ ?_⟩
  dsimp only [Function.onFun]
  rw [OrthonormalBasis.coe_toBasis, ← hinner, hT.apply_eigenvectorBasis, real_inner_smul_left,
    (hT.eigenvectorBasis hm).orthonormal.2 hij, mul_zero]

end QuadraticMap
