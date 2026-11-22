/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Completion.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Semilocal
import TauCeti.RingTheory.Ideal.Maps

/-!
# Semilocal decomposition of the different under completion

For a place `P` of `F / k` and a finite separable extension `F' / F` (with arbitrary constant
extension `k' / k` where `k'` is integral over `k`), extending the different ideal of `𝒪'_P` over
`𝒪_P` to `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` and transporting along
`TauCeti.Place.integralCompletionSemilocalEquiv` yields the product of the completed different
ideals at the places of `F' / k'` lying over `P`.

## Main results

* `TauCeti.Place.differentIdeal_integralCompletionSemilocal`: fibrewise product decomposition of
  `differentIdeal 𝒪_P 𝒪'_P` under `integralCompletionSemilocalEquiv`.

## References

* `IsDedekindDomain.HeightOneSpectrum.differentIdeal_adicCompletionIntegersSemilocal` in
  `TauCeti/RingTheory/DedekindDomain/Different/Completion.lean`.
-/

public section
noncomputable section

open IsDedekindDomain
open scoped PlaceCompletionExtension TensorProduct

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- **The different ideal in the integral semilocal decomposition.** Extending the different ideal
of `𝒪'_P` over `𝒪_P` to `𝒪̂_P ⊗[𝒪_P] 𝒪'_P` and transporting along
`TauCeti.Place.integralCompletionSemilocalEquiv` yields the product of the completed different
ideals at the places of `F' / k'` lying over `P`. -/
theorem differentIdeal_integralCompletionSemilocal (P : Place k F) :
    ((differentIdeal P.integers (integralClosure P.integers F')).map
        (Algebra.TensorProduct.includeRight :
          integralClosure P.integers F' →ₐ[P.integers]
            P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F')).map
        (integralCompletionSemilocalEquiv k' F' P) =
      Ideal.pi fun Q : {P' : Place k' F' // P'.restrict k F = P} ↦
        differentIdeal P.completionPlace.integers Q.val.completionPlace.integers := by
  refine (Ideal.map_map
    (Algebra.TensorProduct.includeRight :
      integralClosure P.integers F' →ₐ[P.integers]
        P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F').toRingHom
    (integralCompletionSemilocalEquiv k' F' P).toRingEquiv.toRingHom).trans
    (Ideal.map_eq_pi_iff.mpr fun Q ↦ ?_)
  rw [← map_differentIdeal_eq_differentIdeal_completionIntegers P Q.val Q.property]
  congr 1; ext x; simp

end TauCeti.Place

end
