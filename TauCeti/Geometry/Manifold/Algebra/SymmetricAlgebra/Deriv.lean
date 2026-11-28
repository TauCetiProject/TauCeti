/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.SymmetricAlgebra
public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic
public import TauCeti.Geometry.Manifold.Algebra.SymmetricAlgebra.Basic

/-!
# Fréchet and directional derivatives of smooth symmetric-algebra evaluations

Combining `SymmetricAlgebra.contMDiffEval_apply` with the manifold-free derivative formulas in
`TauCeti.Analysis.Calculus.SymmetricAlgebra` identifies the Fréchet derivative of
`SymmetricAlgebra.contMDiffEval 𝕜 E n p` at `ξ : StrongDual 𝕜 E` with evaluation at the gradient
vector `p.gradient ξ.toLinearMap`, and its directional derivative along `t ↦ ξ + t • η` at `t = 0`
with `η (p.gradient ξ.toLinearMap)`.

When `𝕜` is complete and `E` is finite-dimensional, transporting
`fderiv 𝕜 (⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n p)) ξ` back to `E` via finite-dimensional
continuous biduality (`TauCeti.inclusionInDoubleDualEquiv 𝕜 E`) recovers `p.gradient ξ.toLinearMap`.

## Main results

* `SymmetricAlgebra.hasFDerivAt_contMDiffEval`, `SymmetricAlgebra.fderiv_contMDiffEval`,
  `SymmetricAlgebra.fderiv_contMDiffEval_apply`,
  `SymmetricAlgebra.hasDerivAt_contMDiffEval_add_smul_zero`: Fréchet and directional derivatives of
  smooth polynomial evaluation on `StrongDual 𝕜 E`, identified via `ContinuousLinearMap.apply`
  with `p.gradient`.
* `SymmetricAlgebra.inclusionInDoubleDualEquiv_symm_fderiv_contMDiffEval`: transporting the
  Fréchet derivative back to `E` through continuous biduality yields `p.gradient`.

## References

* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer
  (1999), §10.1 (smooth polynomial functions and functional derivatives on the dual of a Lie
  algebra).
-/

public section

open scoped ContDiff Manifold

namespace SymmetricAlgebra

section FDeriv

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Fréchet derivative of `SymmetricAlgebra.contMDiffEval`.** -/
theorem hasFDerivAt_contMDiffEval (n : ℕ∞ω) (p : SymmetricAlgebra 𝕜 E)
    (ξ : StrongDual 𝕜 E) :
    HasFDerivAt (⇑(contMDiffEval 𝕜 E n p))
      (ContinuousLinearMap.apply 𝕜 𝕜 (p.gradient ξ.toLinearMap)) ξ := by
  rw [coe_contMDiffEval]
  exact hasFDerivAt_lift p ξ

/-- The Fréchet derivative of `SymmetricAlgebra.contMDiffEval 𝕜 E n p` at `ξ` is
`ContinuousLinearMap.apply 𝕜 𝕜 (p.gradient ξ.toLinearMap)`. -/
theorem fderiv_contMDiffEval (n : ℕ∞ω) (p : SymmetricAlgebra 𝕜 E)
    (ξ : StrongDual 𝕜 E) :
    fderiv 𝕜 (⇑(contMDiffEval 𝕜 E n p)) ξ =
      ContinuousLinearMap.apply 𝕜 𝕜 (p.gradient ξ.toLinearMap) :=
  (hasFDerivAt_contMDiffEval n p ξ).fderiv

/-- Applying the Fréchet derivative of `SymmetricAlgebra.contMDiffEval 𝕜 E n p` at `ξ` to `η`
gives `η (p.gradient ξ.toLinearMap)`. -/
theorem fderiv_contMDiffEval_apply (n : ℕ∞ω) (p : SymmetricAlgebra 𝕜 E)
    (ξ η : StrongDual 𝕜 E) :
    fderiv 𝕜 (⇑(contMDiffEval 𝕜 E n p)) ξ η =
      η (p.gradient ξ.toLinearMap) := by
  rw [fderiv_contMDiffEval, ContinuousLinearMap.apply_apply]

/-- At `t = 0`, the directional derivative of
`t ↦ SymmetricAlgebra.contMDiffEval 𝕜 E n p (ξ + t • η)` is
`η (p.gradient ξ.toLinearMap)`. -/
theorem hasDerivAt_contMDiffEval_add_smul_zero (n : ℕ∞ω)
    (p : SymmetricAlgebra 𝕜 E) (ξ η : StrongDual 𝕜 E) :
    HasDerivAt (fun t : 𝕜 ↦ contMDiffEval 𝕜 E n p (ξ + t • η))
      (η (p.gradient ξ.toLinearMap)) 0 := by
  simpa [contMDiffEval_apply, ContinuousLinearMap.toLinearMap_add,
    FunLike.coe_smul] using hasDerivAt_lift_add_smul_zero p ξ.toLinearMap η.toLinearMap

/-- Transporting the Fréchet derivative of `SymmetricAlgebra.contMDiffEval 𝕜 E n p` at `ξ` back
to `E` through finite-dimensional continuous biduality recovers `p.gradient ξ.toLinearMap`. -/
theorem inclusionInDoubleDualEquiv_symm_fderiv_contMDiffEval
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    (n : ℕ∞ω) (p : SymmetricAlgebra 𝕜 E) (ξ : StrongDual 𝕜 E) :
    (TauCeti.inclusionInDoubleDualEquiv 𝕜 E).symm
      (fderiv 𝕜 (⇑(contMDiffEval 𝕜 E n p)) ξ) =
      p.gradient ξ.toLinearMap := by
  rw [fderiv_contMDiffEval]
  have h : ContinuousLinearMap.apply 𝕜 𝕜 (p.gradient ξ.toLinearMap) =
      TauCeti.inclusionInDoubleDualEquiv 𝕜 E (p.gradient ξ.toLinearMap) := by
    ext η
    simp [TauCeti.inclusionInDoubleDualEquiv_apply]
  rw [h, ContinuousLinearEquiv.symm_apply_apply]

end FDeriv

end SymmetricAlgebra
