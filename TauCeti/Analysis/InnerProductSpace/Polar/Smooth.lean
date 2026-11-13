/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import TauCeti.Analysis.InnerProductSpace.Positive.FunctionalCalculus
import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# Smooth dependence of the modulus and the polar factor

Let `T : V →L[𝕜] W` be an operator from a finite-dimensional inner product space to a Hilbert
space over `RCLike 𝕜`. Its modulus `|T| = √(T† T)` is invertible exactly when `T` is injective
(`ContinuousLinearMap.isUnit_modulus_iff_injective`), and then its polar factor is
`U = T |T|⁻¹`. On the injective operators both depend smoothly on `T`, as functions of the
underlying real vector space of operators: `T ↦ T† T` is real-quadratic, the square root is
smooth on the strictly positive operators (`ContinuousLinearMap.contDiffOn_sqrt`), and inversion
is smooth on the invertible operators. Smoothness is only real, because over `ℂ` the adjoint is
conjugate-linear; the spaces carry a real structure compatible with the `𝕜`-action, as they do
automatically for `𝕜 = ℝ` and `𝕜 = ℂ`.

This is what makes the polar factor usable fibrewise: an operator-valued map that is smooth and
injective at every point has a smooth polar factor, for instance the unitary part of an elliptic
principal symbol.

## Main results

* `ContinuousLinearMap.contDiffOn_modulus`: the modulus is smooth on the injective operators.
* `ContinuousLinearMap.contDiffOn_polarFactor`: the polar factor is smooth on the injective
  operators.
-/

public section

noncomputable section

open scoped ContDiff InnerProduct

namespace ContinuousLinearMap

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] [FiniteDimensional 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W] [IsScalarTower ℝ 𝕜 W]
  [CompleteSpace W]

/-- The modulus `T ↦ |T| = √(T† T)` is smooth on the injective operators out of a
finite-dimensional inner product space. -/
theorem contDiffOn_modulus {n : ℕ∞ω} :
    ContDiffOn ℝ n (modulus : (V →L[𝕜] W) → V →L[𝕜] V) {T | Function.Injective T} := by
  -- The Gram operator `T† T`, a composition of `𝕜`-linear maps, is real-quadratic in `T`.
  have hgram : ContDiff ℝ n fun T : V →L[𝕜] W ↦ T† ∘L T := by
    simpa using (((compL 𝕜 V W V).bilinearRestrictScalars ℝ).contDiff.comp
      adjointRealCLM.contDiff).clm_apply contDiff_id
  -- The real algebra structure underlying `restrict_scalars`, with its operator norm.
  let : NormedAlgebra ℝ (V →L[𝕜] V) := { algebra with norm_smul_le := norm_smul_le }
  refine (((contDiffOn_sqrt (𝕜 := 𝕜) (E := V)).restrict_scalars ℝ).comp hgram.contDiffOn
    fun T hT ↦ ?_).congr fun T _ ↦ modulus_eq_sqrt T
  exact IsStrictlyPositive.iff_of_unital.2 ⟨nonneg_iff_isPositive.2 T.isPositive_adjoint_comp_self,
    (isUnit_adjoint_comp_self_iff T).2 hT⟩

/-- The polar factor `T ↦ T |T|⁻¹` is smooth on the injective operators out of a
finite-dimensional inner product space. -/
theorem contDiffOn_polarFactor {n : ℕ∞ω} :
    ContDiffOn ℝ n (polarFactor : (V →L[𝕜] W) → V →L[𝕜] W) {T | Function.Injective T} := by
  have hinv : ContDiffOn ℝ n (fun T : V →L[𝕜] W ↦ Ring.inverse T.modulus)
      {T | Function.Injective T} := fun T hT ↦ by
    obtain ⟨u, hu⟩ := isUnit_modulus_iff_injective.2 hT
    exact ((hu ▸ (contDiffAt_ringInverse 𝕜 u).restrict_scalars ℝ).comp_contDiffWithinAt T
      (contDiffOn_modulus T hT))
  refine ((((compL 𝕜 V V W).bilinearRestrictScalars ℝ).contDiff.comp_contDiffOn
    contDiffOn_id).clm_apply hinv).congr fun T hT ↦ ?_
  simp [polarFactor_eq_comp_inverse T (isUnit_modulus_iff_injective.2 hT)]

end ContinuousLinearMap
