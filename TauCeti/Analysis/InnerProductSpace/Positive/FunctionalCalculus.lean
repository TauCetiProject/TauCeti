/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.Matrix.Exponential.Log

/-!
# Smooth functional calculus for positive operators in finite dimension

Real powers and the positive square root depend smoothly on a strictly positive operator
on a finite-dimensional inner product space over `ℝ` or `ℂ`. These statements use the native
continuous functional calculus on operators, rather than a choice of eigenvectors, and allow
dimension zero. They permit smooth changes of fibre metrics without choosing smoothly varying
eigenbases. Over `ℂ` the smoothness is complex, and `ContDiffOn.restrict_scalars` gives the real
statement.

The proof transports `Matrix.contDiffOn_rpow` through an orthonormal basis. See B. C. Hall,
*Lie Groups, Lie Algebras, and Representations*, second edition, §§2.3 and 2.5, for the
exponential and logarithm description of positive matrix powers.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E] [NormedAlgebra ℝ (E →L[𝕜] E)]
  [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]

open scoped ContDiff NNReal MatrixOrder ComplexOrder Matrix.Norms.L2Operator

/-- Every real power is smooth on the strictly positive operators in finite dimension,
including analyticity over `𝕜` (real over `ℝ`, complex over `ℂ`). Smoothness is within the
positive cone, not on an open subset of all operators. -/
theorem contDiffOn_rpow (s : ℝ) {n : ℕ∞ω} :
    ContDiffOn 𝕜 n (fun A : E →L[𝕜] E ↦ A ^ s) {A | IsStrictlyPositive A} := by
  let b := stdOrthonormalBasis 𝕜 E
  let e : Matrix (Fin (Module.finrank 𝕜 E)) (Fin (Module.finrank 𝕜 E)) 𝕜 ≃⋆ₐ[𝕜]
      (E →L[𝕜] E) :=
    (LinearMap.toMatrixOrthonormal b).symm.trans
      { LinearMap.toContinuousLinearMap with
        map_mul' := fun _ _ ↦ rfl
        map_star' := LinearMap.adjoint_toContinuousLinearMap }
  have he : ContDiff 𝕜 n e := e.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.contDiff
  have hei : ContDiff 𝕜 n e.symm :=
    e.symm.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.contDiff
  have hpos {A : E →L[𝕜] E} (hA : IsStrictlyPositive A) : (e.symm A).PosDef := by
    apply Matrix.isStrictlyPositive_iff_posDef.mp
    exact IsStrictlyPositive.iff_of_unital.mpr
      ⟨map_nonneg e.symm hA.nonneg, hA.isUnit.map e.symm⟩
  have h := he.comp_contDiffOn ((Matrix.contDiffOn_rpow s).comp
    (hei.contDiffOn (s := {A | IsStrictlyPositive A})) (fun A hA ↦ hpos hA))
  apply h.congr
  intro A hA
  have hp : 0 ≤ e.symm A := map_nonneg e.symm hA.nonneg
  simp only [Function.comp_apply, CFC.rpow_def]
  symm
  simpa only [StarAlgEquiv.toStarAlgHom_apply, e.apply_symm_apply] using
    e.toStarAlgHom.map_cfc (R := ℝ≥0)
    (fun x : ℝ≥0 ↦ x ^ s) (e.symm A) (hφ := he.continuous)
    (hf := fun x hx ↦ (NNReal.continuousAt_rpow_const (Or.inl (by
      intro hx0
      exact spectrum.zero_notMem ℝ≥0 (hA.isUnit.map e.symm) (hx0 ▸ hx)))).continuousWithinAt)

/-- The native positive square root is smooth on the strictly positive operators in
finite dimension, including analyticity over `𝕜` (real over `ℝ`, complex over `ℂ`). -/
theorem contDiffOn_sqrt {n : ℕ∞ω} :
    ContDiffOn 𝕜 n (CFC.sqrt : (E →L[𝕜] E) → (E →L[𝕜] E))
      {A | IsStrictlyPositive A} := by
  exact (contDiffOn_rpow (𝕜 := 𝕜) (E := E) (n := n) (1 / 2)).congr fun A _ ↦ CFC.sqrt_eq_rpow

end ContinuousLinearMap
