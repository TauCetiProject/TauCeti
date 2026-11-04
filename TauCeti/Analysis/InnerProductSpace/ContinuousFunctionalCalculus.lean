/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5,
  OpenAI GPT-6
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Subalgebra
public import TauCeti.Analysis.InnerProductSpace.Complexification
import Mathlib.Analysis.RCLike.ContinuousMap

/-!
# The continuous functional calculus on real and `RCLike` Hilbert spaces

Mathlib's continuous functional calculus for bounded self-adjoint operators comes from the
complex `C⋆`-algebra structure of `E →L[ℂ] E`, so it is available only on complex Hilbert spaces.
This file supplies the instance

`ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint`

for every Hilbert space `E` over `RCLike 𝕜`, in any dimension, for every real algebra structure on
`E →L[𝕜] E` compatible with the `𝕜`-action (`IsScalarTower ℝ 𝕜 (E →L[𝕜] E)`), and with it
Mathlib's star order (`ContinuousLinearMap.instStarOrderedRingRCLike`). Hence `cfc f T` and the
positive square root `CFC.sqrt T` of a positive operator are available on Hilbert spaces over
every `RCLike 𝕜`, as is the absolute value `CFC.abs T = √(T† T)` of every bounded operator. Over
an abstract `RCLike` field, the real algebra structure is `ContinuousLinearMap.realAlgebra`,
obtained by restricting scalars along `ℝ → 𝕜`; at `𝕜 = ℝ` and `𝕜 = ℂ` it is Mathlib's own, and any
two compatible real algebra structures coincide by `Algebra.restrictScalars_eq`.

The real calculus is pulled back from the complexification. Complexification
`T ↦ T_ℂ` (`ContinuousLinearMap.complexifyL2StarAlgHom`) is an isometric unital `⋆`-homomorphism
from `X →L[ℝ] X` into the complex `C⋆`-algebra `X_ℂ →L[ℂ] X_ℂ`, so it is a closed embedding,
and `StarAlgHom.continuousFunctionalCalculus_of_isClosedEmbedding` applies. Consequently
complexification preserves the spectrum of a self-adjoint operator
(`ContinuousLinearMap.spectrum_complexifyL2`) and intertwines the two calculi
(`ContinuousLinearMap.complexifyL2_cfc`): `(f(T))_ℂ = f(T_ℂ)`.

The calculus over `RCLike 𝕜` is in turn pulled back from the real one along realification. A
Hilbert space `E` over `𝕜` is a real Hilbert space for the inner product `re ⟪x, y⟫`
(`InnerProductSpace.rclikeToReal`), and restricting scalars `T ↦ T.restrictScalars ℝ` is an
isometric unital `⋆`-homomorphism from `E →L[𝕜] E` into the real operators on `E`
(`ContinuousLinearMap.restrictScalarsStarAlgHom`): the adjoint for `re ⟪·, ·⟫` of the restriction
of `T` is the restriction of `T†` (`ContinuousLinearMap.adjoint_restrictScalars`). Consequently
realification preserves the spectrum of a self-adjoint operator
(`ContinuousLinearMap.spectrum_restrictScalars`) and intertwines the two calculi
(`ContinuousLinearMap.restrictScalars_cfc`).

## Main declarations

* `ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`: the continuous
  functional calculus for bounded self-adjoint operators on a real Hilbert space.
* `ContinuousLinearMap.instContinuousFunctionalCalculusRCLikeIsSelfAdjoint`: the continuous
  functional calculus for bounded self-adjoint operators on a Hilbert space over `RCLike 𝕜`.
* `ContinuousLinearMap.instStarOrderedRingRCLike`: Mathlib's star order on bounded operators,
  registered here as an instance.
* `ContinuousLinearMap.spectrum_complexifyL2`: complexification preserves the spectrum of a
  self-adjoint operator.
* `ContinuousLinearMap.complexifyL2_cfc`: complexification commutes with the continuous
  functional calculus.
* `ContinuousLinearMap.restrictScalarsStarAlgHom`: realification of the bounded operators on a
  Hilbert space over `RCLike 𝕜`, as a `⋆`-algebra homomorphism over `ℝ`.
* `ContinuousLinearMap.spectrum_restrictScalars`: realification preserves the spectrum of a
  self-adjoint operator.
* `ContinuousLinearMap.restrictScalars_cfc`: realification commutes with the continuous functional
  calculus.

## Acknowledgements

A real continuous functional calculus for bounded operators, also obtained from the
complexification, appears in
`ForTauCeti/Analysis/InnerProductSpace/RealContinuousFunctionalCalculus.lean` of the
[AIQ DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0). There the calculus is descended through the conjugation of the
complexification; here it is restricted to the closed range of the complexification map.
The normal-operator half-plane bound
`ContinuousLinearMap.nonneg_add_star_sub_smul_of_spectrum_re` is adapted from
`DavisKahan/InfiniteDimensional/TanTwoTheta/QuarterAcuteFormGap.lean`, Kitware DKPS
(Jon Crall, OpenAI GPT-5.6 Thinking and Claude Opus 5; Apache-2.0). It turns a lower
bound `a` on real parts of the spectrum into `W + W† ≥ 2 a I`.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- **The continuous functional calculus for bounded self-adjoint operators on a real Hilbert
space**, pulled back from the complexification. -/
instance instContinuousFunctionalCalculusRealIsSelfAdjoint :
    ContinuousFunctionalCalculus ℝ (X →L[ℝ] X) IsSelfAdjoint :=
  (complexifyL2StarAlgHom X).continuousFunctionalCalculus_of_isClosedEmbedding
    (isClosedEmbedding_complexifyL2StarAlgHom X) fun _ ↦ by simp

/-- Complexification preserves the spectrum of a self-adjoint operator on a real Hilbert space. -/
theorem spectrum_complexifyL2 {T : X →L[ℝ] X} (hT : IsSelfAdjoint T) :
    spectrum ℝ T.complexifyL2 = spectrum ℝ T := by
  -- Instance search finds `StarModule ℝ` on the complex operators only for the real scalar
  -- action restricted from `ℂ`, not for the action of `ContinuousLinearMap.algebra`.
  have : StarModule ℝ (WithLp 2 (TauCeti.Complexification X) →L[ℂ]
      WithLp 2 (TauCeti.Complexification X)) :=
    StarModule.complexToReal (E := WithLp 2 (TauCeti.Complexification X) →L[ℂ]
      WithLp 2 (TauCeti.Complexification X))
  simpa using (complexifyL2StarAlgHom X).spectrum_apply_eq_of_isClosedEmbedding
    (isClosedEmbedding_complexifyL2StarAlgHom X) (q := IsSelfAdjoint) (by simpa using hT)

/-- Complexification commutes with the continuous functional calculus: for a self-adjoint
operator `T` on a real Hilbert space and `f` continuous on its spectrum, `(f(T))_ℂ = f(T_ℂ)`. -/
theorem complexifyL2_cfc (f : ℝ → ℝ) (T : X →L[ℝ] X)
    (hf : ContinuousOn f (spectrum ℝ T) := by cfc_cont_tac) (hT : IsSelfAdjoint T := by cfc_tac) :
    (cfc f T).complexifyL2 = cfc f T.complexifyL2 := by
  simpa using (complexifyL2StarAlgHom X).map_cfc f T hf
    (isClosedEmbedding_complexifyL2StarAlgHom X).continuous hT (by simpa using hT)

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

-- The declarations below are stated for the real Hilbert space underlying `E`, with inner product
-- `re ⟪x, y⟫` (`InnerProductSpace.rclikeToReal`). It cannot be a local instance, since `𝕜` does
-- not appear in `InnerProductSpace ℝ E`.

/-- For the real inner product `re ⟪x, y⟫`, the adjoint of the realification of a bounded
operator is the realification of its adjoint. -/
@[simp]
theorem adjoint_restrictScalars {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F] (T : E →L[𝕜] F) :
    letI := InnerProductSpace.rclikeToReal 𝕜 E
    letI := InnerProductSpace.rclikeToReal 𝕜 F
    adjoint (T.restrictScalars ℝ) = (adjoint T).restrictScalars ℝ := by
  let := InnerProductSpace.rclikeToReal 𝕜 E
  let := InnerProductSpace.rclikeToReal 𝕜 F
  refine ((eq_adjoint_iff _ _).2 fun x y ↦ ?_).symm
  simp only [real_inner_eq_re_inner 𝕜, coe_restrictScalars', adjoint_inner_left]

/-- A bounded operator on a Hilbert space over `RCLike 𝕜` is self-adjoint exactly when its
realification is, for the real inner product `re ⟪x, y⟫`. -/
@[simp]
theorem isSelfAdjoint_restrictScalars_iff {T : E →L[𝕜] E} :
    letI := InnerProductSpace.rclikeToReal 𝕜 E
    IsSelfAdjoint (T.restrictScalars ℝ) ↔ IsSelfAdjoint T := by
  let := InnerProductSpace.rclikeToReal 𝕜 E
  simp only [isSelfAdjoint_iff', adjoint_restrictScalars, ContinuousLinearMap.ext_iff,
    coe_restrictScalars']

variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]

variable (𝕜 E) in
/-- Realification `T ↦ T.restrictScalars ℝ` of the bounded operators on a Hilbert space over
`RCLike 𝕜`, as a `⋆`-algebra homomorphism over `ℝ` into the bounded operators on the underlying
real Hilbert space, for any real algebra structure compatible with the `𝕜`-action. -/
noncomputable def restrictScalarsStarAlgHom :
    letI := InnerProductSpace.rclikeToReal 𝕜 E
    (E →L[𝕜] E) →⋆ₐ[ℝ] (E →L[ℝ] E) :=
  letI := InnerProductSpace.rclikeToReal 𝕜 E
  { toFun := restrictScalars ℝ
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl
    commutes' r := by
      ext x
      simp [IsScalarTower.algebraMap_apply ℝ 𝕜 (E →L[𝕜] E), Algebra.algebraMap_eq_smul_one]
    map_star' T := (adjoint_restrictScalars T).symm }

@[simp]
theorem restrictScalarsStarAlgHom_apply (T : E →L[𝕜] E) :
    letI := InnerProductSpace.rclikeToReal 𝕜 E
    restrictScalarsStarAlgHom 𝕜 E T = T.restrictScalars ℝ := (rfl)

variable (𝕜 E) in
/-- Realification of the bounded operators on a Hilbert space over `RCLike 𝕜` is an isometry. -/
theorem isometry_restrictScalarsStarAlgHom :
    letI := InnerProductSpace.rclikeToReal 𝕜 E
    Isometry (restrictScalarsStarAlgHom 𝕜 E) :=
  letI := InnerProductSpace.rclikeToReal 𝕜 E
  (restrictScalarsIsometry 𝕜 E E ℝ ℝ).isometry

variable (𝕜 E) in
/-- Realification of the bounded operators on a Hilbert space over `RCLike 𝕜` is a closed
embedding. -/
theorem isClosedEmbedding_restrictScalarsStarAlgHom :
    letI := InnerProductSpace.rclikeToReal 𝕜 E
    Topology.IsClosedEmbedding (restrictScalarsStarAlgHom 𝕜 E) :=
  letI := InnerProductSpace.rclikeToReal 𝕜 E
  (isometry_restrictScalarsStarAlgHom 𝕜 E).isClosedEmbedding

/-- **The continuous functional calculus for bounded self-adjoint operators on a Hilbert space
over `RCLike 𝕜`**, for any real algebra structure on the operators compatible with the `𝕜`-action,
pulled back from the real calculus along realification. -/
instance instContinuousFunctionalCalculusRCLikeIsSelfAdjoint :
    ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint :=
  letI := InnerProductSpace.rclikeToReal 𝕜 E
  (restrictScalarsStarAlgHom 𝕜 E).continuousFunctionalCalculus_of_isClosedEmbedding
    (isClosedEmbedding_restrictScalarsStarAlgHom 𝕜 E) fun _ ↦
      isSelfAdjoint_restrictScalars_iff.symm

/-- Realification preserves the spectrum of a self-adjoint operator on a Hilbert space over
`RCLike 𝕜`. -/
theorem spectrum_restrictScalars {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    letI := InnerProductSpace.rclikeToReal 𝕜 E
    spectrum ℝ (T.restrictScalars ℝ) = spectrum ℝ T := by
  let := InnerProductSpace.rclikeToReal 𝕜 E
  simpa using (restrictScalarsStarAlgHom 𝕜 E).spectrum_apply_eq_of_isClosedEmbedding
    (isClosedEmbedding_restrictScalarsStarAlgHom 𝕜 E) (q := IsSelfAdjoint)
    (isSelfAdjoint_restrictScalars_iff.2 hT)

/-- Realification commutes with the continuous functional calculus: for a self-adjoint operator
`T` on a Hilbert space over `RCLike 𝕜` and `f` continuous on its spectrum,
`(f(T)).restrictScalars ℝ = f(T.restrictScalars ℝ)`. -/
theorem restrictScalars_cfc (f : ℝ → ℝ) (T : E →L[𝕜] E)
    (hf : ContinuousOn f (spectrum ℝ T) := by cfc_cont_tac) (hT : IsSelfAdjoint T := by cfc_tac) :
    letI := InnerProductSpace.rclikeToReal 𝕜 E
    (cfc f T).restrictScalars ℝ = cfc f (T.restrictScalars ℝ) := by
  -- Synthesized before the real inner product is introduced, since `NormedSpace ℝ E` then gives
  -- a second action of `ℝ` on `E →L[𝕜] E`, and instance search would pick that one instead.
  have : IsScalarTower ℝ ℝ (E →L[𝕜] E) := inferInstance
  let := InnerProductSpace.rclikeToReal 𝕜 E
  simpa using (restrictScalarsStarAlgHom 𝕜 E).map_cfc f T hf
    (isClosedEmbedding_restrictScalarsStarAlgHom 𝕜 E).continuous hT
    (isSelfAdjoint_restrictScalars_iff.2 hT)

-- The bounded operators on a Hilbert space over `RCLike 𝕜` form a star-ordered ring for the
-- Loewner order: the positive operators are exactly the sums of operators `S† S`. Mathlib proves
-- this from the real continuous functional calculus, which is now available for every `𝕜`.
attribute [instance] instStarOrderedRingRCLike

end RCLike

/-- The inner product of two images under a positive operator's square root. -/
theorem inner_sqrt_apply_sqrt_apply_eq_inner {T : X →L[ℝ] X} (hT : 0 ≤ T) (u v : X) :
    ⟪CFC.sqrt T u, CFC.sqrt T v⟫_ℝ = ⟪T u, v⟫_ℝ := by
  rw [← (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).inner_left_eq_inner_right,
    ← mul_apply_eq_comp, CFC.sqrt_mul_sqrt_self T hT]

open scoped ComplexOrder

/-- A spectral half-plane bound for a normal operator is an order bound
for its Hermitian part. -/
theorem nonneg_add_star_sub_smul_of_spectrum_re
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (W : E →L[ℂ] E) [IsStarNormal W] {a : ℝ}
    (hspec : ∀ z ∈ spectrum ℂ W, a ≤ z.re) :
    0 ≤ W + star W - ((2 * a : ℝ) : ℂ) • 1 := by
  let hWnormal : IsStarNormal W := inferInstance
  let X : C(spectrum ℂ W, ℂ) :=
    (ContinuousMap.id ℂ).restrict (spectrum ℂ W)
  let g : C(spectrum ℂ W, ℝ) :=
    ⟨fun z => 2 * (z : ℂ).re - 2 * a,
      (continuous_const.mul
        (Complex.continuous_re.comp continuous_subtype_val)).sub continuous_const⟩
  have hg : ∀ z, 0 ≤ g z := by
    intro z
    dsimp [g]
    have hz := hspec (z : ℂ) z.property
    linarith
  have hT : 0 ≤ cfcHom hWnormal
      ((ContinuousMap.realToRCLikeStarAlgHom _ ℂ) g) := by
    apply map_nonneg (cfcHom hWnormal)
    intro z
    simpa using hg z
  have hsymbol :
      (ContinuousMap.realToRCLikeStarAlgHom _ ℂ) g =
        X + star X - ((2 * a : ℝ) : ℂ) • 1 := by
    ext z
    dsimp [g, X]
    apply Complex.ext
    · simp
      ring
    · simp
  rw [hsymbol, map_sub, map_add, map_star, map_smul, map_one,
    cfcHom_id] at hT
  exact hT

end ContinuousLinearMap
