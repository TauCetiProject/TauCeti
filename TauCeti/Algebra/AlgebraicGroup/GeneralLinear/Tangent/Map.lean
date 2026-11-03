/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map

/-!
# Matrix realizations of differentials of representations

A coordinate bialgebra map out of `O(GLₙ)` gives a matrix-valued tangent Lie homomorphism.
It is injective when the coordinate map is surjective, over any coefficient algebra.
-/

public section

namespace TauCeti.GeneralLinear

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {R B H : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing H] [Bialgebra R H] {n : ℕ}

/-- The differential of a representation, expressed as matrices over the coefficient algebra. -/
def tangentMatrixLieHom (q : coordinateHopfAlgebra R n →ₐc[R] H) :
    Derivation R H (Bialgebra.CounitAlgebra R H B) →ₗ⁅B⁆ Matrix (Fin n) (Fin n) B :=
  (tangentLieEquivMatrix (R := R) (B := B) n).toLieHom.comp (derivationCompLieHom q)

/-- The matrix realization evaluates the precomposed tangent vector on the generic matrix. -/
theorem tangentMatrixLieHom_apply (q : coordinateHopfAlgebra R n →ₐc[R] H)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    tangentMatrixLieHom q d = tangentMatrix n (derivationComp q d) := by
  simp only [tangentMatrixLieHom, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    tangentLieEquivMatrix_apply, derivationCompLieHom_apply]

/-- A closed immersion has an injective matrix-valued differential. -/
theorem tangentMatrixLieHom_injective_of_surjective
    (q : coordinateHopfAlgebra R n →ₐc[R] H) (hq : Function.Surjective q) :
    Function.Injective (tangentMatrixLieHom (B := B) q) :=
  (tangentLieEquivMatrix (R := R) (B := B) n).injective.comp
    (derivationCompLieHom_injective_of_surjective q hq)

end

end TauCeti.GeneralLinear
