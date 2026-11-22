/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv
public import TauCeti.Topology.VectorBundle.Riemannian.Hermitian

/-!
# The Euler class of the dual of a Hermitian bundle

Let `E → B` be a complex vector bundle of complex rank `r + 1`. A fibrewise conjugate-linear
isomorphism, continuous on total spaces, multiplies the Euler class `e(E_ℝ)` by `(-1) ^ (r + 1)`
(`TauCeti.complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise`).

When the fibres of `E` carry a Hermitian inner product whose norm is continuous on the total space
(`TauCeti.ContinuousFiberNorm`), the fibrewise Riesz map `v ↦ ⟪v, ·⟫` (`TauCeti.bundleToDual`) is
such an isomorphism onto the dual bundle `fun b ↦ StrongDual ℂ (E b)`. So
`e(E*) = (-1) ^ (r + 1) e(E)` (`TauCeti.complexEulerClass_dual_of_continuousFiberNorm`), and for a
line bundle `e(L*) = -e(L)`
(`TauCeti.complexEulerClass_dual_eq_neg_of_finrank_eq_one_of_continuousFiberNorm`).

The Hermitian metric is a hypothesis: it supplies the conjugate-linear isomorphism `E ≅ E*`, and no
metric is chosen.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14, Lemma 14.9 (the dual of a Hermitian bundle).
-/

public section

noncomputable section

open Bundle Module
open scoped InnerProductSpace

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {r : ℕ}

/-! ### The dual of a Hermitian bundle -/

section Dual

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℂ (E b)] [FiberBundle F E] [VectorBundle ℂ F E]

variable [ContinuousFiberNorm F E] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [∀ b, Module ℝ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]

/-- **The Euler class of the dual of a Hermitian bundle.** For a complex vector bundle `E` of
complex rank `r + 1` whose fibres carry a Hermitian inner product with continuous norm, the dual
bundle `E*` has `e(E*) = (-1) ^ (r + 1) e(E)`. -/
theorem complexEulerClass_dual_of_continuousFiberNorm (hF : finrank ℂ (StrongDual ℂ F) = r + 1) :
    complexEulerClass (StrongDual ℂ F) (fun b ↦ StrongDual ℂ (E b)) hF =
      (-1 : ℤ) ^ (r + 1) •
        complexEulerClass F E (ContinuousLinearMap.dual_finrank_eq.symm.trans hF) := by
  have := FiniteDimensional.completeSpace ℂ F
  have h := complexEulerClass_eq_neg_one_pow_smul_of_conjugateFiberwise hF
    (ContinuousLinearMap.dual_finrank_eq.symm.trans hF)
    (φ := fun b ↦ (bundleToDual F E ℂ b).toContinuousLinearEquiv) (continuous_bundleToDual ℂ)
  rw [h, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- **The Euler class of the dual of a Hermitian line bundle is the negative**:
`e(L*) = -e(L)`. -/
theorem complexEulerClass_dual_eq_neg_of_finrank_eq_one_of_continuousFiberNorm
    (hF : finrank ℂ (StrongDual ℂ F) = 0 + 1) :
    complexEulerClass (StrongDual ℂ F) (fun b ↦ StrongDual ℂ (E b)) hF =
      -complexEulerClass F E (ContinuousLinearMap.dual_finrank_eq.symm.trans hF) := by
  rw [complexEulerClass_dual_of_continuousFiberNorm hF, pow_one, neg_one_zsmul]

end Dual

end TauCeti
