/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.FiniteSpectrum
public import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot
public import TauCeti.Analysis.Normed.Operator.FiniteDimensional

/-!
# The finite symmetric calculus and modulus agree with the continuous functional calculus

On a finite-dimensional inner product space `E` over `𝕜 = ℝ` or `ℂ`, there are two functional
calculi for a symmetric operator `T`: the spectral sum `LinearMap.IsSymmetric.cfc`, defined for
every real function through an orthonormal eigenbasis, and Mathlib's continuous functional
calculus `cfc f T` of the self-adjoint bounded operator `T`. Likewise there are two square roots
of a positive operator and two moduli `√(A† A)` of a linear map. This file proves that the two
constructions coincide after the identification `LinearMap.toContinuousLinearMap` of linear maps
with bounded operators, so that results proved for either can be used for both.

The comparison rests on the eigenvector description of the continuous functional calculus.
The spectrum of a finite-dimensional operator is finite, so `cfc f T` acts on every eigenvector
of `T` for the eigenvalue `μ` as multiplication by `f μ`
(`TauCeti.cfc_smul_of_smul_eq_algebraMap_smul`), which characterizes the spectral sum
(`LinearMap.IsSymmetric.eq_cfc_iff`). In particular no continuity of `f` is needed.

The statements are uniform in the scalar field. They assume a real algebra structure on
`E →L[𝕜] E` compatible with the `𝕜`-scalars and a continuous functional calculus over `ℝ` for
self-adjoint operators, the setting of Mathlib's star order on bounded operators
(`Mathlib.Analysis.InnerProductSpace.StarOrder`); the square-root statements also assume that
this order makes `E →L[𝕜] E` a star-ordered ring. At `𝕜 = ℂ` all of this is Mathlib's structure
on the complex `C⋆`-algebra `E →L[ℂ] E`, and at `𝕜 = ℝ` it is supplied by
`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`. Completeness of `E`,
automatic in finite dimension, is assumed because Mathlib's adjoint on `E →L[𝕜] E` requires it.

## Main results

* `ContinuousLinearMap.cfc_apply_of_apply_eq_smul`: if `T x = μ x`, then `f(T) x = f(μ) x`.
* `LinearMap.IsSymmetric.toContinuousLinearMap_cfc`: the finite spectral calculus `f(T)` is the
  continuous functional calculus `cfc f T`.
* `LinearMap.IsPositive.toContinuousLinearMap_sqrt`: the finite positive square root is
  `CFC.sqrt`.
* `LinearMap.toContinuousLinearMap_operatorAbs`: the finite modulus of a rectangular map `A` is
  the square root `CFC.sqrt (A† A)` of its source Gram operator.
* `LinearMap.toContinuousLinearMap_operatorAbs_eq_cfcAbs`: the finite modulus of an endomorphism
  is its absolute value `CFC.abs` in the `C⋆`-algebra sense.
-/

public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

namespace ContinuousLinearMap

variable [CompleteSpace E] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

/-- **Eigenvector action of the continuous functional calculus.** On a finite-dimensional space,
if a self-adjoint operator `T` satisfies `T x = μ x`, then `f(T) x = f(μ) x` for every real
function `f`. -/
theorem cfc_apply_of_apply_eq_smul (f : ℝ → ℝ) {T : E →L[𝕜] E} {x : E} {μ : ℝ}
    (hx : T x = (μ : 𝕜) • x) (hT : IsSelfAdjoint T := by cfc_tac) :
    cfc f T x = (f μ : 𝕜) • x := by
  have halg (r : ℝ) : algebraMap ℝ (E →L[𝕜] E) r • x = (r : 𝕜) • x := by
    rw [ContinuousLinearMap.smul_def, IsScalarTower.algebraMap_apply ℝ 𝕜 (E →L[𝕜] E),
      algebraMap_apply, RCLike.algebraMap_eq_ofReal]
  rw [← ContinuousLinearMap.smul_def, ← halg] at hx ⊢
  exact TauCeti.cfc_smul_of_smul_eq_algebraMap_smul f (T.finite_spectrum ℝ) hx hT

end ContinuousLinearMap

namespace LinearMap

variable [CompleteSpace E] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

/-- **Agreement of the finite and continuous functional calculi.** For a symmetric operator `T`
on a finite-dimensional space and any real function `f`, the spectral sum `f(T)` is the
continuous functional calculus `cfc f T` of `T` viewed as a bounded operator. -/
theorem IsSymmetric.toContinuousLinearMap_cfc {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (f : ℝ → ℝ) : toContinuousLinearMap (hT.cfc f) = _root_.cfc f (toContinuousLinearMap T) := by
  have hT' : IsSelfAdjoint (toContinuousLinearMap T) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have h : hT.cfc f = (_root_.cfc f (toContinuousLinearMap T) : E →L[𝕜] E).toLinearMap :=
    ((hT.eq_cfc_iff f).mpr fun _ _ hx ↦
      ContinuousLinearMap.cfc_apply_of_apply_eq_smul f (by rwa [coe_toContinuousLinearMap'])).symm
  ext x
  simp [h]

variable [StarOrderedRing (E →L[𝕜] E)]

/-- The finite positive square root of a positive operator is the continuous-functional-calculus
square root `CFC.sqrt`. -/
theorem IsPositive.toContinuousLinearMap_sqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    toContinuousLinearMap hT.sqrt = CFC.sqrt (toContinuousLinearMap T) := by
  refine (CFC.sqrt_unique ?_ ?_).symm
  · rw [← ContinuousLinearMap.coe_inj, ContinuousLinearMap.toLinearMap_mul, Module.End.mul_eq_comp]
    simp
  · exact ContinuousLinearMap.nonneg_iff_isPositive.mpr hT.sqrt_isPositive

/-- The finite modulus `|A|` of a rectangular linear map `A` is the continuous-functional-calculus
square root of the source Gram operator `A† A`. -/
theorem toContinuousLinearMap_operatorAbs (A : E →ₗ[𝕜] F) :
    toContinuousLinearMap A.operatorAbs =
      CFC.sqrt (toContinuousLinearMap A.adjoint ∘L toContinuousLinearMap A) := by
  rw [(isPositive_adjoint_comp_self A).sqrt_unique A.isPositive_operatorAbs A.operatorAbs_sq]
  exact (isPositive_adjoint_comp_self A).toContinuousLinearMap_sqrt.trans
    (congrArg CFC.sqrt (by ext; simp))

/-- **The finite modulus is the absolute value.** For an endomorphism `A` of a finite-dimensional
space, the finite modulus `|A| = √(A† A)` is the absolute value `CFC.abs A` of `A` in the
bounded operators. -/
theorem toContinuousLinearMap_operatorAbs_eq_cfcAbs (A : E →ₗ[𝕜] E) :
    toContinuousLinearMap A.operatorAbs = CFC.abs (toContinuousLinearMap A) := by
  rw [toContinuousLinearMap_operatorAbs, CFC.abs, ContinuousLinearMap.star_eq_adjoint,
    ← adjoint_toContinuousLinearMap, ContinuousLinearMap.mul_def]

end LinearMap
