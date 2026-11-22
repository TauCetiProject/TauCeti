/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.SymmetricAlgebra
public import TauCeti.Geometry.Manifold.Algebra.SymmetricAlgebra.Basic

/-!
# Fréchet and directional derivatives of smooth symmetric-algebra evaluations

Whenever a normed vector space `E` over a nontrivially normed field `𝕜` has a finite basis `b`,
combining `SymmetricAlgebra.contMDiffEval_apply` with the manifold-free derivative formulas in
`TauCeti.Analysis.Calculus.SymmetricAlgebra` identifies the Fréchet derivative of
`SymmetricAlgebra.contMDiffEval 𝕜 E n p` at `ξ : StrongDual 𝕜 E` with evaluation at the gradient
vector `b.symmetricGradient p ξ.toLinearMap`, and its directional derivative along `t ↦ ξ + t • η`
at `t = 0` with `η (b.symmetricGradient p ξ.toLinearMap)`.

When `𝕜` is complete, transporting `fderiv 𝕜 (⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n p)) ξ` back
to `E` via finite-dimensional biduality (`Module.evalEquiv 𝕜 E`) recovers
`b.symmetricGradient p ξ.toLinearMap`.

## Main results

* `Module.Basis.hasFDerivAt_contMDiffEval`, `Module.Basis.fderiv_contMDiffEval`,
  `Module.Basis.fderiv_contMDiffEval_apply`, `Module.Basis.hasDerivAt_contMDiffEval_add_smul_zero`:
  Fréchet and directional derivatives of smooth polynomial evaluation on `StrongDual 𝕜 E`,
  identified via `ContinuousLinearMap.apply` with `b.symmetricGradient`.
* `Module.Basis.evalEquiv_symm_fderiv_contMDiffEval`: transporting the Fréchet derivative back to
  `E` through finite-dimensional biduality yields `b.symmetricGradient`.

## References

* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer
  (1999), §10.1 (smooth polynomial functions and functional derivatives on the dual of a Lie
  algebra).
-/

public section

open scoped ContDiff Manifold

namespace Module.Basis

section FDeriv

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Fintype ι]

/-- **Fréchet derivative of `SymmetricAlgebra.contMDiffEval`.** -/
theorem hasFDerivAt_contMDiffEval (b : Module.Basis ι 𝕜 E) (n : ℕ∞ω) (p : SymmetricAlgebra 𝕜 E)
    (ξ : StrongDual 𝕜 E) :
    HasFDerivAt (⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n p))
      (ContinuousLinearMap.apply 𝕜 𝕜 (b.symmetricGradient p ξ.toLinearMap)) ξ := by
  have hfun : ⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n p) =
      fun η : StrongDual 𝕜 E ↦ SymmetricAlgebra.lift η.toLinearMap p :=
    funext (SymmetricAlgebra.contMDiffEval_apply p)
  rw [hfun]
  exact b.hasFDerivAt_lift p ξ

theorem fderiv_contMDiffEval (b : Module.Basis ι 𝕜 E) (n : ℕ∞ω) (p : SymmetricAlgebra 𝕜 E)
    (ξ : StrongDual 𝕜 E) :
    fderiv 𝕜 (⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n p)) ξ =
      ContinuousLinearMap.apply 𝕜 𝕜 (b.symmetricGradient p ξ.toLinearMap) :=
  (b.hasFDerivAt_contMDiffEval n p ξ).fderiv

theorem fderiv_contMDiffEval_apply (b : Module.Basis ι 𝕜 E) (n : ℕ∞ω) (p : SymmetricAlgebra 𝕜 E)
    (ξ η : StrongDual 𝕜 E) :
    fderiv 𝕜 (⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n p)) ξ η =
      η (b.symmetricGradient p ξ.toLinearMap) := by
  rw [b.fderiv_contMDiffEval]
  rfl

theorem hasDerivAt_contMDiffEval_add_smul_zero (b : Module.Basis ι 𝕜 E) (n : ℕ∞ω)
    (p : SymmetricAlgebra 𝕜 E) (ξ η : StrongDual 𝕜 E) :
    HasDerivAt (fun t : 𝕜 ↦ SymmetricAlgebra.contMDiffEval 𝕜 E n p (ξ + t • η))
      (η (b.symmetricGradient p ξ.toLinearMap)) 0 := by
  simpa [SymmetricAlgebra.contMDiffEval_apply, ContinuousLinearMap.toLinearMap_add,
    FunLike.coe_smul] using b.hasDerivAt_lift_add_smul_zero p ξ.toLinearMap η.toLinearMap

/-- Transporting the Fréchet derivative of `SymmetricAlgebra.contMDiffEval 𝕜 E n p` at `ξ` back
to `E` through finite-dimensional biduality recovers `b.symmetricGradient p ξ.toLinearMap`. -/
theorem evalEquiv_symm_fderiv_contMDiffEval [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    (b : Module.Basis ι 𝕜 E) (n : ℕ∞ω) (p : SymmetricAlgebra 𝕜 E) (ξ : StrongDual 𝕜 E) :
    (Module.evalEquiv 𝕜 E).symm
      ((fderiv 𝕜 (⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n p)) ξ).toLinearMap.comp
        LinearMap.toContinuousLinearMap.toLinearMap) =
      b.symmetricGradient p ξ.toLinearMap := by
  apply (Module.evalEquiv 𝕜 E).injective
  rw [LinearEquiv.apply_symm_apply]
  ext η
  simp [b.fderiv_contMDiffEval_apply]

end FDeriv

end Module.Basis
