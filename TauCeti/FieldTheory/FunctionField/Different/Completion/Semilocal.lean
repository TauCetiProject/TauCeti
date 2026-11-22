/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Completion.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Semilocal

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
  let incR : integralClosure P.integers F' →ₐ[P.integers]
      P.completionPlace.integers ⊗[P.integers] integralClosure P.integers F' :=
    Algebra.TensorProduct.includeRight
  let f : integralClosure P.integers F' →+*
      ∀ Q : {P' : Place k' F' // P'.restrict k F = P}, Q.val.completionPlace.integers :=
    (integralCompletionSemilocalEquiv k' F' P).toRingEquiv.toRingHom.comp incR.toRingHom
  have hcomp (Q : {P' : Place k' F' // P'.restrict k F = P}) :
      ((differentIdeal P.integers (integralClosure P.integers F')).map f).map (Pi.evalRingHom _ Q) =
        differentIdeal P.completionPlace.integers Q.val.completionPlace.integers := by
    rw [Ideal.map_map, ← map_differentIdeal_eq_differentIdeal_completionIntegers P Q.val Q.property]
    congr 1; ext x; simp [f, incR]
  have hf : ((differentIdeal P.integers (integralClosure P.integers F')).map incR).map
        (integralCompletionSemilocalEquiv k' F' P) =
      (differentIdeal P.integers (integralClosure P.integers F')).map f :=
    Ideal.map_map incR.toRingHom (integralCompletionSemilocalEquiv k' F' P).toRingEquiv.toRingHom
  rw [hf]
  exact Ideal.piOrderIso.injective <| funext fun Q ↦ by
    dsimp [Ideal.piOrderIso]
    rw [Ideal.map_evalRingHom_pi, hcomp Q]

end TauCeti.Place

end
