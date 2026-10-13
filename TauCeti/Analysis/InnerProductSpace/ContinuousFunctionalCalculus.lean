/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Subalgebra
public import TauCeti.Analysis.InnerProductSpace.Complexification

/-!
# The continuous functional calculus on a real Hilbert space

Mathlib's continuous functional calculus for bounded self-adjoint operators comes from the
complex `C⋆`-algebra structure of `E →L[ℂ] E`, so it is available only on complex Hilbert spaces.
This file supplies the instance

`ContinuousFunctionalCalculus ℝ (X →L[ℝ] X) IsSelfAdjoint`

for every real Hilbert space `X`, in any dimension, and with it Mathlib's star order
(`ContinuousLinearMap.instStarOrderedRingRCLike`). Hence `cfc f T` and the positive square root
`CFC.sqrt T` of a positive operator are available on real Hilbert spaces, as is the absolute value
`CFC.abs T = √(T† T)` of every bounded operator.

The calculus is pulled back from the complexification. Complexification
`T ↦ T_ℂ` (`ContinuousLinearMap.complexifyL2StarAlgHom`) is an isometric unital `⋆`-homomorphism
from `X →L[ℝ] X` into the complex `C⋆`-algebra `X_ℂ →L[ℂ] X_ℂ`, so it is a closed embedding,
and `StarAlgHom.continuousFunctionalCalculus_of_isClosedEmbedding` applies. Consequently
complexification preserves the spectrum of a self-adjoint operator
(`ContinuousLinearMap.spectrum_complexifyL2`) and intertwines the two calculi
(`ContinuousLinearMap.complexifyL2_cfc`): `(f(T))_ℂ = f(T_ℂ)`.

## Main declarations

* `ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`: the continuous
  functional calculus for bounded self-adjoint operators on a real Hilbert space.
* `ContinuousLinearMap.instStarOrderedRingReal`: the bounded operators on a real Hilbert space
  form a star-ordered ring.
* `ContinuousLinearMap.spectrum_complexifyL2`: complexification preserves the spectrum of a
  self-adjoint operator.
* `ContinuousLinearMap.complexifyL2_cfc`: complexification commutes with the continuous
  functional calculus.

## Acknowledgements

A real continuous functional calculus for bounded operators, also obtained from the
complexification, appears in
`ForTauCeti/Analysis/InnerProductSpace/RealContinuousFunctionalCalculus.lean` of the
[AIQ DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0). There the calculus is descended through the conjugation of the
complexification; here it is restricted to the closed range of the complexification map.
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

/-- The bounded operators on a real Hilbert space form a star-ordered ring for the Loewner order:
the positive operators are exactly the sums of operators `S† S`. -/
instance instStarOrderedRingReal : StarOrderedRing (X →L[ℝ] X) :=
  instStarOrderedRingRCLike (𝕜 := ℝ) (H := X)

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

end ContinuousLinearMap
