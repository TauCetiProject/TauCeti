/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit

/-!
# Positive functionals pulled back along surjective homomorphisms

The norm of a positive functional on a possibly nonunital C⋆-algebra is its limit along any
increasing approximate unit, Mathlib's `PositiveContinuousLinearMap.tendsto_nhds_opNorm`. A
surjective star-algebra homomorphism carries increasing approximate units to increasing
approximate units, so pulling a positive functional back along it does not change the norm,
`PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective`. In particular states pull back
to states along quotient maps; without surjectivity the norm can drop, for instance to `0`.
-/

public section

open scoped ComplexOrder

namespace PositiveContinuousLinearMap

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- Pulling a positive functional back along a surjective star-algebra homomorphism of
C⋆-algebras preserves its norm. -/
theorem opNorm_comp_ofClass_of_surjective (ω : B →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f) :
    ‖((ω.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ = ‖(ω : B →L[ℂ] ℂ)‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  exact Complex.ofReal_injective <| tendsto_nhds_unique
    ((ω.comp (.ofClass f)).tendsto_nhds_opNorm hl)
    (Filter.tendsto_map'_iff.mp (ω.tendsto_nhds_opNorm (hl.map f hf)))

end PositiveContinuousLinearMap
