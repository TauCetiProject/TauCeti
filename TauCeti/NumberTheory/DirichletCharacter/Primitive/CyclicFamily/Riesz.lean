/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.CyclicFamily.RayClass
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder.Family

/-!
# Riesz remainders for cyclic families

The weighted remainder on rational ray class characters becomes a finite sum indexed by the
primitive Dirichlet characters of the cyclic family. The individual prime-sum formulas are
available in `TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz`.
-/

public section

namespace TauCeti.PrimitiveDirichletCharacter

/-- The Riesz remainder of the transferred weights is the weighted sum over the original cyclic
family, with each character evaluated through the rational ray class dictionary. -/
theorem familyRieszRemainder_cyclicFamilyWeights (ψ : PrimitiveDirichletCharacter)
    (w : PrimitiveDirichletCharacter → ℝ) (y : ℝ) :
    (ψ.cyclicFamilyWeights w).familyRieszRemainder y =
      ∑ κ ∈ ψ.cyclicFamily, w κ * ((toPrimitiveRayClassCharacter κ).rieszRemainder y).re := by
  rw [Finsupp.familyRieszRemainder_apply]
  simpa only [smul_eq_mul] using
    ψ.sum_cyclicFamilyWeights w (fun η ↦ (η.rieszRemainder y).re)

end TauCeti.PrimitiveDirichletCharacter
