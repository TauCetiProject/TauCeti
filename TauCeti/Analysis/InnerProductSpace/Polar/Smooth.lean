/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import TauCeti.Analysis.InnerProductSpace.Positive.FunctionalCalculus
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.RangeProjection

/-!
# Smooth dependence of the modulus and the polar factor

Let `T : V →L[ℂ] W` be an operator from a finite-dimensional complex inner product space to a
complex Hilbert space. Its modulus `|T| = √(T† T)` is invertible exactly when `T` is injective
(`ContinuousLinearMap.isUnit_modulus_iff_injective`), and then its polar factor is
`U = T |T|⁻¹`. On the injective operators both depend smoothly on `T`, as functions of the
underlying real vector space of operators: `T ↦ T† T` is real-quadratic, the square root is
smooth on the strictly positive operators (`ContinuousLinearMap.contDiffOn_sqrt`), and inversion
is smooth on the invertible operators. Smoothness is only real, because the adjoint is
conjugate-linear.

This is what makes the polar factor usable fibrewise: an operator-valued map that is smooth and
injective at every point has a smooth polar factor, for instance the unitary part of an elliptic
principal symbol.

## Main results

* `ContinuousLinearMap.isUnit_modulus_iff_injective`: `|T|` is invertible exactly when `T` is
  injective.
* `ContinuousLinearMap.contDiffOn_modulus`: the modulus is smooth on the injective operators.
* `ContinuousLinearMap.contDiffOn_polarFactor`: the polar factor is smooth on the injective
  operators.
-/

public section

noncomputable section

open scoped ContDiff InnerProduct

namespace ContinuousLinearMap

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- In finite dimension the modulus `|T|` of an operator is invertible exactly when `T` is
injective. -/
theorem isUnit_modulus_iff_injective {T : V →L[ℂ] W} :
    IsUnit T.modulus ↔ Function.Injective T := by
  rw [isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot, ker_modulus,
    LinearMap.ker_eq_bot, coe_coe]

/-- The modulus `T ↦ |T| = √(T† T)` is smooth on the injective operators out of a
finite-dimensional complex inner product space. -/
theorem contDiffOn_modulus {n : ℕ∞ω} :
    ContDiffOn ℝ n (modulus : (V →L[ℂ] W) → V →L[ℂ] V) {T | Function.Injective T} := by
  -- The Gram operator `T† T`, a composition of `ℂ`-linear maps, is real-quadratic in `T`.
  have hgram : ContDiff ℝ n fun T : V →L[ℂ] W ↦ T† ∘L T := by
    simpa using (((compL ℂ V W V).bilinearRestrictScalars ℝ).contDiff.comp
      adjointRealCLM.contDiff).clm_apply contDiff_id
  refine (((contDiffOn_sqrt (𝕜 := ℂ) (E := V)).restrict_scalars ℝ).comp hgram.contDiffOn
    fun T hT ↦ ?_).congr fun T _ ↦ modulus_eq_sqrt T
  exact IsStrictlyPositive.iff_of_unital.2 ⟨nonneg_iff_isPositive.2 T.isPositive_adjoint_comp_self,
    (isUnit_adjoint_comp_self_iff T).2 hT⟩

/-- The polar factor `T ↦ T |T|⁻¹` is smooth on the injective operators out of a
finite-dimensional complex inner product space. -/
theorem contDiffOn_polarFactor {n : ℕ∞ω} :
    ContDiffOn ℝ n (polarFactor : (V →L[ℂ] W) → V →L[ℂ] W) {T | Function.Injective T} := by
  have hinv : ContDiffOn ℝ n (fun T : V →L[ℂ] W ↦ Ring.inverse T.modulus)
      {T | Function.Injective T} := fun T hT ↦ by
    obtain ⟨u, hu⟩ := isUnit_modulus_iff_injective.2 hT
    exact ((hu ▸ contDiffAt_ringInverse ℝ u).comp_contDiffWithinAt T
      (contDiffOn_modulus T hT))
  refine ((((compL ℂ V V W).bilinearRestrictScalars ℝ).contDiff.comp_contDiffOn
    contDiffOn_id).clm_apply hinv).congr fun T hT ↦ ?_
  simp [polarFactor_eq_comp_inverse T (isUnit_modulus_iff_injective.2 hT)]

end ContinuousLinearMap
