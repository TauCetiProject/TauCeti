/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.PoissonBracket.Evaluation
public import TauCeti.Geometry.Manifold.Algebra.SymmetricAlgebra.Deriv

/-!
# Smooth Kirillov–Kostant–Souriau evaluation of the PBW Rees zero-fibre bracket

For a finite-dimensional Lie algebra `L` identified with a normed vector space `E` via a
`𝕜`-linear equivalence `e : L ≃ₗ[𝕜] E` over a complete nontrivially normed field `𝕜`, every
element `r : SymmetricAlgebra 𝕜 E` evaluates to a `C^n` polynomial function
`SymmetricAlgebra.contMDiffEval 𝕜 E n r` on `StrongDual 𝕜 E`.

Combining the algebraic linear Poisson evaluation formula `lift_reesZeroFiberBracket_apply` with
gradient naturality and the Fréchet derivative identification
`Module.Basis.evalEquiv_symm_fderiv_contMDiffEval` expresses the smooth evaluation of
`reesZeroFiberBracket 𝕜 L p q` at `ξ : StrongDual 𝕜 E` directly in terms of the two Fréchet
derivatives at `ξ` transported back to `L` through finite-dimensional biduality
`Module.evalEquiv 𝕜 E`, without defining a bracket on all smooth functions.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.contMDiffEval_reesZeroFiberBracket_apply`: smooth KKS
  differential formula for `reesZeroFiberBracket` on `StrongDual 𝕜 E`.

## References

* J. E. Marsden and T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Springer
  (1999), §10.1 (functional derivatives and the Lie–Poisson bracket on `𝔤*`).
* S. Gutt, *Deformation Quantization and Symmetries*, Lecture 1, slide 14 (2019), for the sign
  convention `{p, q}(ξ) = ξ([dp_ξ, dq_ξ])`.
-/

public section

open scoped ContDiff

namespace TauCeti.UniversalEnvelopingAlgebra

section SmoothPoissonEvaluation

/-- **Smooth KKS differential comparison for `reesZeroFiberBracket`.** Identifying a
finite-dimensional Lie algebra `L` over a complete nontrivially normed field `𝕜` with a normed
space `E` via `e : L ≃ₗ[𝕜] E`, evaluating `reesZeroFiberBracket 𝕜 L p q` as a smooth function at
`ξ : StrongDual 𝕜 E` equals `ξ (e ⁅dp_ξ, dq_ξ⁆)`, where `dp_ξ` and `dq_ξ` are the Fréchet
derivatives of the smooth evaluations of `p` and `q` at `ξ` transported back to `L` through
finite-dimensional biduality. -/
theorem contMDiffEval_reesZeroFiberBracket_apply
    {𝕜 L E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [LieRing L] [LieAlgebra 𝕜 L]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (e : L ≃ₗ[𝕜] E) (n : ℕ∞ω) (p q : SymmetricAlgebra 𝕜 L) (ξ : StrongDual 𝕜 E) :
    SymmetricAlgebra.contMDiffEval 𝕜 E n
        (SymmetricAlgebra.map 𝕜 e.toLinearMap (reesZeroFiberBracket 𝕜 L p q)) ξ =
      ξ (e ⁅e.symm ((Module.evalEquiv 𝕜 E).symm
          ((fderiv 𝕜 (⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n
            (SymmetricAlgebra.map 𝕜 e.toLinearMap p))) ξ).toLinearMap.comp
            LinearMap.toContinuousLinearMap.toLinearMap)),
        e.symm ((Module.evalEquiv 𝕜 E).symm
          ((fderiv 𝕜 (⇑(SymmetricAlgebra.contMDiffEval 𝕜 E n
            (SymmetricAlgebra.map 𝕜 e.toLinearMap q))) ξ).toLinearMap.comp
            LinearMap.toContinuousLinearMap.toLinearMap))⁆) := by
  let := Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex 𝕜 E)
  let b := Module.Basis.ofVectorSpace 𝕜 E
  let bL := b.map e.symm
  rw [SymmetricAlgebra.contMDiffEval_apply, SymmetricAlgebra.lift_map,
    lift_reesZeroFiberBracket_apply L bL p q (ξ.toLinearMap ∘ₗ e.toLinearMap),
    b.evalEquiv_symm_fderiv_contMDiffEval n (SymmetricAlgebra.map 𝕜 e.toLinearMap p) ξ,
    b.evalEquiv_symm_fderiv_contMDiffEval n (SymmetricAlgebra.map 𝕜 e.toLinearMap q) ξ,
    bL.symmetricGradient_map b e.toLinearMap p ξ.toLinearMap,
    bL.symmetricGradient_map b e.toLinearMap q ξ.toLinearMap]
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

end SmoothPoissonEvaluation

end TauCeti.UniversalEnvelopingAlgebra
