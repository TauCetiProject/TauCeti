/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.InnerProductSpace.Gram.Factor
public import TauCeti.Analysis.Normed.Operator.RealAlgebra

/-!
# The modulus of a bounded operator

For a bounded operator `T : E →L[𝕜] F` between Hilbert spaces over `RCLike 𝕜`, the source Gram
operator `T† T` is positive, and its positive square root is the *modulus*
`|T| = √(T† T) : E →L[𝕜] E` of `T`. The modulus measures the size of `T` on the source space:
`‖|T| x‖ = ‖T x‖` for every `x`, so `|T|` and `T` have the same kernel and the same operator norm.
It is the input to the polar decomposition `T = U |T|` of a bounded operator, whose factor `U`
is the canonical factor `T.factorThru |T|` of `T` through its modulus.

The square root is the one of the continuous functional calculus,
`ContinuousLinearMap.instContinuousFunctionalCalculusRCLikeIsSelfAdjoint`. That calculus is
stated for a real algebra structure on `E →L[𝕜] E` compatible with the `𝕜`-action; the
definition uses `ContinuousLinearMap.realAlgebra`, obtained by restricting scalars along `ℝ → 𝕜`,
so that `T.modulus` makes sense over every `RCLike` field and its API needs no structure beyond
the Hilbert spaces. Any other compatible real algebra structure, such as Mathlib's own at `𝕜 = ℝ`
and `𝕜 = ℂ`, gives the same square root (`ContinuousLinearMap.modulus_eq_sqrt`).

No finite dimension is assumed. For linear maps between finite-dimensional spaces the modulus
`LinearMap.operatorAbs` is built from an eigenbasis instead.

## Main declarations

* `ContinuousLinearMap.modulus`: the modulus `|T| = √(T† T)` of a bounded operator.
* `ContinuousLinearMap.modulus_eq_sqrt`: `|T| = CFC.sqrt (T† T)` for every real algebra structure
  compatible with the `𝕜`-action; `ContinuousLinearMap.modulus_eq_abs`: for an endomorphism,
  `|T|` is the absolute value `CFC.abs T`.
* `ContinuousLinearMap.isPositive_modulus`, `ContinuousLinearMap.isSelfAdjoint_modulus`: the
  modulus is positive and self-adjoint.
* `ContinuousLinearMap.modulus_comp_modulus`: `|T| |T| = T† T`.
* `ContinuousLinearMap.eq_modulus_iff`: the modulus is the unique positive square root of
  `T† T`; in particular `ContinuousLinearMap.IsPositive.modulus_eq`: a positive operator is its
  own modulus.
* `ContinuousLinearMap.norm_modulus_apply`: `‖|T| x‖ = ‖T x‖`; consequently
  `ContinuousLinearMap.ker_modulus`: `ker |T| = ker T`, and
  `ContinuousLinearMap.norm_modulus`: `‖|T|‖ = ‖T‖`.
* `ContinuousLinearMap.norm_modulus_comp`, `ContinuousLinearMap.norm_comp_modulus`: the
  composition laws `‖|T| D‖ = ‖T D‖` and `‖D |T|‖ = ‖D T†‖`.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  ed., Academic Press (1980), §VI.4.
-/

public section

open scoped InnerProduct

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

section RealAlgebra

-- The square root is taken for the real algebra structure on `E →L[𝕜] E` obtained by restricting
-- scalars along `ℝ → 𝕜`; `modulus_eq_sqrt` below removes this choice from the public API.
attribute [local instance] realAlgebra realIsScalarTower

/-- The **modulus** `|T| = √(T† T)` of a bounded operator `T` between Hilbert spaces: the positive
square root of the source Gram operator `T† T`.

The square root is taken in the continuous functional calculus for the real algebra structure
`ContinuousLinearMap.realAlgebra`; `ContinuousLinearMap.modulus_eq_sqrt` identifies it with the
square root for any other compatible real algebra structure. -/
noncomputable def modulus (T : E →L[𝕜] F) : E →L[𝕜] E :=
  CFC.sqrt (T† ∘L T)

/-- The modulus is nonnegative in the Loewner order. -/
theorem modulus_nonneg (T : E →L[𝕜] F) : 0 ≤ T.modulus :=
  CFC.sqrt_nonneg _

/-- The square of the modulus is the source Gram operator: `|T| |T| = T† T`. -/
@[simp]
theorem modulus_comp_modulus (T : E →L[𝕜] F) : T.modulus ∘L T.modulus = T† ∘L T :=
  CFC.sqrt_mul_sqrt_self _ (nonneg_iff_isPositive.2 (isPositive_adjoint_comp_self T))

/-- Applying the modulus twice is applying the source Gram operator: `|T| (|T| x) = T† (T x)`. -/
@[simp]
theorem modulus_modulus_apply (T : E →L[𝕜] F) (x : E) : T.modulus (T.modulus x) = (T†) (T x) :=
  congr($(T.modulus_comp_modulus) x)

/-- **Uniqueness of the modulus.** The modulus is the unique positive operator whose square is
the source Gram operator `T† T`. -/
theorem eq_modulus_iff {T : E →L[𝕜] F} {S : E →L[𝕜] E} :
    S = T.modulus ↔ S.IsPositive ∧ S ∘L S = T† ∘L T := by
  refine ⟨?_, fun ⟨hS, h⟩ ↦ (CFC.sqrt_unique h (nonneg_iff_isPositive.2 hS)).symm⟩
  rintro rfl
  exact ⟨nonneg_iff_isPositive.1 T.modulus_nonneg, T.modulus_comp_modulus⟩

end RealAlgebra

/-- The modulus is positive. -/
theorem isPositive_modulus (T : E →L[𝕜] F) : T.modulus.IsPositive :=
  nonneg_iff_isPositive.1 T.modulus_nonneg

/-- The modulus is self-adjoint. -/
theorem isSelfAdjoint_modulus (T : E →L[𝕜] F) : IsSelfAdjoint T.modulus :=
  T.isPositive_modulus.isSelfAdjoint

/-- The modulus is its own adjoint. -/
@[simp]
theorem adjoint_modulus (T : E →L[𝕜] F) : T.modulus† = T.modulus :=
  T.isSelfAdjoint_modulus.adjoint_eq

/-- A positive operator is its own modulus. -/
theorem IsPositive.modulus_eq {T : E →L[𝕜] E} (hT : T.IsPositive) : T.modulus = T :=
  (eq_modulus_iff.2 ⟨hT, by rw [hT.isSelfAdjoint.adjoint_eq]⟩).symm

/-- The modulus of the modulus is the modulus. -/
@[simp]
theorem modulus_modulus (T : E →L[𝕜] F) : T.modulus.modulus = T.modulus :=
  T.isPositive_modulus.modulus_eq

/-- The modulus of the zero operator is zero. -/
@[simp]
theorem modulus_zero : (0 : E →L[𝕜] F).modulus = 0 :=
  (eq_modulus_iff.2 ⟨isPositive_zero, by simp⟩).symm

/-- The modulus is the square root `CFC.sqrt (T† T)` of the continuous functional calculus, for
every real algebra structure on `E →L[𝕜] E` compatible with the `𝕜`-action. -/
theorem modulus_eq_sqrt [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
    (T : E →L[𝕜] F) : T.modulus = CFC.sqrt (T† ∘L T) :=
  (CFC.sqrt_unique T.modulus_comp_modulus T.modulus_nonneg).symm

/-- The modulus of an endomorphism `T` is its absolute value `CFC.abs T = √(star T * T)`, for
every real algebra structure on `E →L[𝕜] E` compatible with the `𝕜`-action. -/
theorem modulus_eq_abs [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
    (T : E →L[𝕜] E) : T.modulus = CFC.abs T := by
  rw [modulus_eq_sqrt, CFC.abs, star_eq_adjoint, mul_def]

/-- The modulus has the same pointwise norms as the operator: `‖|T| x‖ = ‖T x‖`. -/
@[simp]
theorem norm_modulus_apply (T : E →L[𝕜] F) (x : E) : ‖T.modulus x‖ = ‖T x‖ := by
  refine adjoint_comp_self_eq_adjoint_comp_self_iff.1 ?_ x
  rw [adjoint_modulus, modulus_comp_modulus]

/-- The modulus and the operator have the same kernel. -/
@[simp]
theorem ker_modulus (T : E →L[𝕜] F) : T.modulus.ker = T.ker := by
  ext x
  simp only [LinearMap.mem_ker, coe_coe, ← norm_eq_zero (a := T.modulus x),
    ← norm_eq_zero (a := T x), norm_modulus_apply]

/-- The modulus and the operator have the same operator norm. -/
@[simp]
theorem norm_modulus (T : E →L[𝕜] F) : ‖T.modulus‖ = ‖T‖ :=
  opNorm_ext _ _ T.norm_modulus_apply

/-- Precomposition law for the modulus: `‖|T| D‖ = ‖T D‖` for every bounded operator `D` into
the source of `T`. -/
@[simp]
theorem norm_modulus_comp {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : E →L[𝕜] F) (D : G →L[𝕜] E) : ‖T.modulus ∘L D‖ = ‖T ∘L D‖ :=
  opNorm_ext _ _ fun x ↦ T.norm_modulus_apply (D x)

/-- Postcomposition law for the modulus: `‖D |T|‖ = ‖D T†‖` for every bounded operator `D` out of
the source of `T`. -/
theorem norm_comp_modulus {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [CompleteSpace G] (T : E →L[𝕜] F) (D : E →L[𝕜] G) : ‖D ∘L T.modulus‖ = ‖D ∘L T†‖ :=
  -- Pass to adjoints, which preserve norms, and apply the precomposition law.
  calc ‖D ∘L T.modulus‖ = ‖(D ∘L T.modulus)†‖ := (adjoint.norm_map _).symm
    _ = ‖T ∘L D†‖ := by rw [adjoint_comp, adjoint_modulus, norm_modulus_comp]
    _ = ‖D ∘L T†‖ := by rw [← adjoint.norm_map, adjoint_comp, adjoint_adjoint]

end ContinuousLinearMap
