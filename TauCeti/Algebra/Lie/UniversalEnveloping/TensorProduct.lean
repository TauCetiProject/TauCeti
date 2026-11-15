/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.TensorProduct
public import TauCeti.Algebra.Bialgebra.Module.TensorProduct
public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.Module

/-!
# Enveloping actions on tensor products

The enveloping action of the diagonal Lie action on a tensor product is the coproduct
representation `BialgebraModule.tensorAction`. This comparison allows integral coproduct
formulas to control tensor products of Lie representations.

The constructions being compared are Mathlib's Lie tensor product and the coproduct module
construction in `TauCeti.Algebra.Bialgebra.Module.TensorProduct`. See Humphreys,
*Introduction to Lie Algebras and Representation Theory*, §17.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R L M N : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

attribute [local instance] asModule isScalarTower_asModule LieRing.ofAssociativeRing

/-- The diagonal Lie action extends to the coproduct representation of the enveloping algebra. -/
theorem tensorAction_eq_representation :
    BialgebraModule.tensorAction R (_root_.UniversalEnvelopingAlgebra R L) M N =
      representation R L (M ⊗[R] N) := by
  apply _root_.UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  apply TensorProduct.ext
  apply LinearMap.ext₂
  intro m n
  simp [BialgebraModule.tensorAction_apply]

end TauCeti.UniversalEnvelopingAlgebra
