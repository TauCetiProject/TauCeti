/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.CyclicFamily.RayClass
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz.RayClass
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder.Family

/-!
# Riesz remainders for cyclic families

The weighted remainder on rational ray class characters becomes a finite sum of Dirichlet
remainders indexed by the primitive characters of the cyclic family.
-/

public section

namespace TauCeti.PrimitiveDirichletCharacter

/-- The Riesz remainder of the transferred weights is the weighted sum of the real parts of
the Dirichlet remainders over the original cyclic family. -/
theorem finsuppRieszRemainder_cyclicFamilyWeights (ψ : PrimitiveDirichletCharacter)
    (w : PrimitiveDirichletCharacter → ℝ) (y : ℝ) :
    LFunctions.finsuppRieszRemainder (ψ.cyclicFamilyWeights w) y =
      ∑ κ ∈ ψ.cyclicFamily, w κ * (κ.rieszRemainder y).re := by
  rw [LFunctions.finsuppRieszRemainder_apply]
  simpa only [smul_eq_mul, rieszRemainder_toPrimitiveRayClassCharacter] using
    ψ.sum_cyclicFamilyWeights w (fun η ↦ (η.rieszRemainder y).re)

end TauCeti.PrimitiveDirichletCharacter
